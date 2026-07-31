-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Netlist.Miter
import Loom.Emit.MicroVerilog.Parse

/-!
# `lake exe eqcheck` — post-synthesis equivalence checking (D22)

```console
lake exe eqcheck rtl/s0blinky.v out/s0blinky.json
```

Reads the emitted µVerilog text back with the verified round-trip parser
(`Loom.Emit.MicroVerilog.Parse`), reads the netlist yosys synthesized from
that same text, matches registers/ports bijectively, and checks — signal by
signal — that the netlist's one-cycle transition function equals the
module's. Every UNSAT verdict is certified by an LRAT proof re-checked with
the proved checker `Loom.Dp.Cert.checkLrat`.

Trust: the CNF encoder (`Loom/Netlist/*`) is **untrusted** in v1. What the
tool establishes is "*if* the encoding is faithful, netlist ≡ module"; the
solver's UNSAT claims themselves are never taken on faith. See
`Loom/Netlist/EQCHECK_SPEC.md`.
-/

open Loom.Netlist
open Loom.Emit.MicroVerilog
open Loom.Dp.Cnf

/-- Outcome of one signal's miter. -/
structure SigResult where
  kind    : String
  name    : String
  width   : Nat
  vars    : Nat
  clauses : Nat
  lrat    : Nat
  ms      : Nat
  verdict : String            -- "PASS" | "FAIL" | "SKIP"
  detail  : String := ""

/-- Run cadical on a DIMACS file and, on UNSAT, re-check the LRAT proof
with the proved checker. Mirrors `Loom.Dp.Solver.solve`'s invocation. -/
def solveAndCheck (d : Dimacs) (dir : System.FilePath) (tag : String) :
    IO (String × Nat × String) := do
  let cnfPath := dir / s!"{tag}.cnf"
  let lratPath := dir / s!"{tag}.lrat"
  IO.FS.writeFile cnfPath d.text
  let out ← IO.Process.output
    { cmd := "cadical",
      args := #["-q", "--no-binary", "--lrat", cnfPath.toString, lratPath.toString] }
  if out.exitCode == 20 then
    let bytes ← IO.FS.readBinFile lratPath
    let text ← IO.FS.readFile lratPath
    let lines := (text.splitOn "\n").filter (fun l => l.trimAscii.toString != "") |>.length
    match Loom.Dp.Cert.parseLrat bytes with
    | .error e => return ("FAIL", lines, s!"LRAT parse error: {e}")
    | .ok cert =>
        if Loom.Dp.Cert.checkLrat cert d.cnf then
          return ("PASS", lines, "")
        else
          return ("FAIL", lines, "the proved LRAT checker REJECTED cadical's certificate")
  else if out.exitCode == 10 then
    let model : List Int :=
      (out.stdout.splitOn "\n").foldl (fun acc l =>
        if l.startsWith "v " then
          acc ++ (((l.drop 2).toString).splitOn " ").filterMap (fun t => t.trimAscii.toString.toInt?)
        else acc) []
    let assign := decodeModel d model
    let shown := assign.map (fun a => s!"{a.1}[{a.2.1}]={if a.2.2 then 1 else 0}")
    let more := if shown.length > 64 then s!" … (+{shown.length - 64} more)" else ""
    return ("FAIL", 0,
      "COUNTEREXAMPLE (a state where the two transition functions differ): " ++
       (if shown.isEmpty then "(the miter has no named variables)"
        else String.intercalate " " (shown.take 64) ++ more))
  else
    return ("FAIL", 0, s!"cadical failed (exit {out.exitCode}): {out.stderr.trimAscii}")

def runSignal (dir : System.FilePath) (kind name : String) (width : Nat)
    (build : M Unit) : IO SigResult := do
  let t0 ← IO.monoMsNow
  let (r, st) := M.run build {}
  match r with
  | .error e =>
      let t1 ← IO.monoMsNow
      -- A cone that crosses the memory boundary is *excluded*, by name, with
      -- the reason printed — never silently dropped (EQCHECK_SPEC.md §Scope).
      let skip := e.startsWith "MEMCUT:"
      pure { kind := kind, name := name, width := width, vars := 0, clauses := 0,
             lrat := 0, ms := t1 - t0,
             verdict := if skip then "SKIP" else "FAIL",
             detail := if skip then (e.drop 8).toString else e }
  | .ok () =>
      let d := toDimacs st.clauses
      let (verdict, lrat, detail) ←
        if d.trivial then
          pure ("PASS", 0,
            "trivially equal: the encoder produced the same formula on both sides")
        else solveAndCheck d dir s!"{kind}_{name.replace "." "_"}"
      let t1 ← IO.monoMsNow
      pure { kind := kind, name := name, width := width, vars := d.vars.size,
             clauses := d.nClauses, lrat := lrat, ms := t1 - t0,
             verdict := verdict, detail := detail }

/-- A signal excluded before any miter ran. -/
def skipped (kind name : String) (width : Nat) (why : String) : SigResult :=
  { kind := kind, name := name, width := width, vars := 0, clauses := 0,
    lrat := 0, ms := 0, verdict := "SKIP", detail := why }

def failed (kind name : String) (width : Nat) (why : String) : SigResult :=
  { kind := kind, name := name, width := width, vars := 0, clauses := 0,
    lrat := 0, ms := 0, verdict := "FAIL", detail := why }

def check (vPath jsonPath : String) : IO UInt32 := do
  let vText ← IO.FS.readFile vPath
  let some cp := Parse.parseCut vText
    | IO.eprintln s!"eqcheck: {vPath}: the µVerilog round-trip parser \
        (Loom.Emit.MicroVerilog.Parse) does not accept this text"
      return 1
  let m := cp.module
  let jText ← IO.FS.readFile jsonPath
  let nl ←
    match parseNetlistTop jText m.name with
    | .error e => IO.eprintln s!"eqcheck: {jsonPath}: {e}"; return 1
    | .ok nl => pure nl
  IO.println s!"eqcheck: {m.name}  ({vPath} vs {jsonPath})"
  let clk ←
    match clockNets nl with
    | .error e => IO.eprintln s!"eqcheck: {e}"; return 1
    | .ok c => pure c
  let regs := m.regs.map (fun r => (r.name, r.width))
  let ins := m.ins.map (fun i => (i.name, i.width))
  let reads := cp.reads.map (fun r => (r.wire, r.width))
  let mt ←
    match matchModule nl regs ins reads (strictFFs := m.mems.isEmpty) with
    | .error e => IO.eprintln s!"eqcheck: MATCHING FAILURE: {e}"; return 1
    | .ok mt => pure mt
  let env ←
    match buildEnv nl mt.seed clk mt.memFF with
    | .error e => IO.eprintln s!"eqcheck: {e}"; return 1
    | .ok e => pure e
  let fuel := env.cells.size + 2
  let syms := regs ++ ins ++ reads
  -- The µVerilog expression a printed identifier stands for: a generated
  -- wire (in the parser's SSA environment) or a declared symbol.
  let symExpr : String → Option (Σ w, Expr w) := fun nm =>
    match cp.env.find? (fun p => p.1 == nm) with
    | some p => some p.2
    | none => (syms.find? (fun kv => kv.1 == nm)).map
        (fun kv => ⟨kv.2, Expr.reg kv.2 nm⟩)
  -- Output ports: bijection with the module's outputs.
  let outPorts := nl.ports.filter (fun p => p.dir == "output")
  for p in outPorts do
    unless m.outs.any (fun o => o.name == p.name) do
      IO.eprintln s!"eqcheck: MATCHING FAILURE: netlist output port '{p.name}' \
        has no µVerilog counterpart"
      return 1
  let regBits := m.regs.foldl (fun a r => a + r.width) 0
  let outBits := m.outs.foldl (fun a o => a + o.width) 0
  IO.println s!"  netlist: {nl.cells.length} cells, {mt.ffOf.size} flip-flops, \
    {nl.ports.length} ports"
  IO.println s!"  matched: {m.regs.length} registers ({regBits} bits, \
    {mt.folded} constant-folded), {m.outs.length} output ports ({outBits} bits), \
    {m.ins.length} inputs"
  unless m.mems.isEmpty do
    IO.println s!"  memories: {m.mems.length} array(s), {cp.reads.length} read \
      site(s) ({mt.cutReads.length} cut at the printed wire, \
      {mt.absorbedReads.length} absorbed into a read port), \
      {cp.writes.length} write port(s); {mt.memRegs.length} read register(s) \
      inside a hard block, {mt.cutFFs} flip-flop(s) retimed inside a cut \
      read, {mt.foldedReads} read bit(s) folded to a constant from the array \
      contents (assumed)"
    unless mt.memFF.isEmpty do
      IO.println s!"  {mt.memFF.size} flip-flop(s) match no µVerilog register \
        bit — memory array storage realized in fabric, or registers retimed \
        into a memory read path (e.g. \
        {String.intercalate ", " mt.memFFNames}). Excluded, not ignored: a \
        checked cone that reaches one is reported as an exclusion."
    IO.println "  (array storage is carried by cell identity: what is checked \
      is every cone that feeds or leaves a memory port, not the array — see \
      EQCHECK_SPEC.md §Scope)"
  let dir ← IO.FS.createTempDir
  let mut results : Array SigResult := #[]
  -- Registers.
  for r in m.regs do
    let some (_, _, srcs) := mt.regs.find? (fun t => t.1 == r.name)
      | IO.eprintln s!"eqcheck: internal: register '{r.name}' unmatched"; return 1
    match mt.memRegs.find? (fun t => t.1 == r.name) with
    | some (_, cn, ty) =>
        results := results.push (skipped "reg" r.name r.width
          s!"EXCLUDED: absorbed into {ty} '{cn}' (D19 sync-read register); its \
            next-state function is inside the hard block")
    | none =>
        results := results.push
          (← runSignal dir "reg" r.name r.width (regMiter env mt fuel syms r srcs))
  -- Output ports.
  for o in m.outs do
    match nl.port? o.name with
    | none =>
        results := results.push
          (failed "out" o.name o.width "no netlist port of that name")
    | some p =>
        if p.bits.size != o.width then
          results := results.push (failed "out" o.name o.width
            s!"netlist port width {p.bits.size} ≠ {o.width}")
        else
          results := results.push
            (← runSignal dir "out" o.name o.width (outMiter env mt fuel syms o p.bits))
  -- Memory read ports: the address cone of every read site.
  for rs in cp.reads do
    let nm := s!"{rs.mem}[{rs.addr}]"
    match symExpr rs.addr with
    | none =>
        results := results.push
          (failed "rdaddr" nm 0 s!"unknown address signal '{rs.addr}'")
    | some ⟨aw, ae⟩ =>
        match namedBits nl rs.addr aw with
        | none => results := results.push (skipped "rdaddr" nm aw
            s!"EXCLUDED: synthesis did not keep a net named '{rs.addr}' — the \
              read address cone has no netlist signal to compare against")
        | some bits =>
            results := results.push
              (← runSignal dir "rdaddr" nm aw (coneMiter env mt fuel syms ae bits))
  -- Memory write ports: the enable, address and data cones of every port.
  for mm in m.mems do
    let sites := cp.writes.filter (fun w => w.mem == mm.name)
    if sites.length != mm.wrPorts.length then
      IO.eprintln s!"eqcheck: internal: memory '{mm.name}' has \
        {mm.wrPorts.length} write ports but {sites.length} printed write lines"
      return 1
    for (site, port) in sites.zip mm.wrPorts do
      let cone (tag wire : String) (w : Nat) (e : Expr w) : IO SigResult := do
        let nm := s!"{mm.name}.{tag}"
        match namedBits nl wire w with
        | none => pure (skipped s!"wr{tag}" nm w
            s!"EXCLUDED: synthesis did not keep a net named '{wire}' (it was \
              absorbed into the memory's port logic)")
        | some bits => runSignal dir s!"wr{tag}" nm w (coneMiter env mt fuel syms e bits)
      results := results.push (← cone "en" site.en 1 port.en)
      results := results.push (← cone "addr" site.addr mm.addrWidth port.addr)
      results := results.push (← cone "data" site.data mm.dataWidth port.data)
  let mut clauses := 0
  let mut lrat := 0
  let mut ms := 0
  let mut bad := 0
  let mut skip := 0
  for r in results do
    let pad := String.ofList (List.replicate (max 1 (18 - r.name.length)) ' ')
    IO.println s!"  [{r.verdict}] {r.kind} {r.name}{pad}w={r.width} \
      vars={r.vars} clauses={r.clauses} lrat={r.lrat} {r.ms}ms"
    unless r.detail == "" do IO.println s!"         {r.detail}"
    clauses := clauses + r.clauses
    lrat := lrat + r.lrat
    ms := ms + r.ms
    if r.verdict == "FAIL" then bad := bad + 1
    if r.verdict == "SKIP" then skip := skip + 1
  let checked := results.size - skip
  IO.println s!"  totals: {checked} signals checked, {skip} excluded, \
    {clauses} clauses, {lrat} LRAT lines, {ms}ms solver+checker wall time"
  IO.println "  (the CNF encoder is untrusted in v1: the claim is \"if the \
    encoding is faithful, netlist ≡ module\"; every UNSAT is LRAT-certified \
    and re-checked by Loom.Dp.Cert.checkLrat, the proved checker)"
  if skip > 0 then
    IO.println s!"  NOT COVERED ({skip} signal(s), each named [SKIP] above): \
      memory array storage, plus every cone that crosses a memory boundary."
  if bad == 0 then
    IO.println s!"EQCHECK OK ({checked} signals, {skip} excluded, {clauses} \
      clauses, LRAT-verified)"
    return 0
  else
    IO.println s!"EQCHECK FAILED ({bad} of {checked} checked signals differ)"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [v, j] => check v j
  | _ =>
      IO.eprintln "usage: eqcheck <module.v> <netlist.json>"
      return 2
