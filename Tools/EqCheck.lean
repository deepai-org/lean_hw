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
  verdict : String            -- "PASS" | "FAIL"
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
      pure { kind := kind, name := name, width := width, vars := 0, clauses := 0,
             lrat := 0, ms := t1 - t0, verdict := "FAIL", detail := e }
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

def check (vPath jsonPath : String) : IO UInt32 := do
  let vText ← IO.FS.readFile vPath
  let some m := Parse.parse vText
    | IO.eprintln s!"eqcheck: {vPath}: the µVerilog round-trip parser \
        (Loom.Emit.MicroVerilog.Parse) does not accept this text"
      let lines := vText.splitOn "\n"
      if lines.any (fun l => l.startsWith "  input wire [") then
        IO.eprintln "  reason: the module declares D15 input ports; the \
          round-trip parser predates D15 and reads only `clk`/`rst` plus \
          output ports (EQCHECK_SPEC.md §Deviations)"
      if lines.any (fun l => l.startsWith "  reg [" && l.endsWith "];") then
        IO.eprintln "  note: the module also declares memory arrays, which \
          are outside the v1 register-only scope"
      return 1
  let jText ← IO.FS.readFile jsonPath
  let nl ←
    match parseNetlistTop jText m.name with
    | .error e => IO.eprintln s!"eqcheck: {jsonPath}: {e}"; return 1
    | .ok nl => pure nl
  IO.println s!"eqcheck: {m.name}  ({vPath} vs {jsonPath})"
  unless m.mems.isEmpty do
    IO.eprintln s!"eqcheck: {m.name} declares {m.mems.length} memory array(s) — \
      outside the v1 register-only scope (EQCHECK_SPEC.md §Scope)"
    return 1
  let clk ←
    match clockNets nl with
    | .error e => IO.eprintln s!"eqcheck: {e}"; return 1
    | .ok c => pure c
  let regs := m.regs.map (fun r => (r.name, r.width))
  let ins := m.ins.map (fun i => (i.name, i.width))
  let mt ←
    match matchModule nl regs ins with
    | .error e => IO.eprintln s!"eqcheck: MATCHING FAILURE: {e}"; return 1
    | .ok mt => pure mt
  let env ←
    match buildEnv nl mt.seed clk with
    | .error e => IO.eprintln s!"eqcheck: {e}"; return 1
    | .ok e => pure e
  let fuel := env.cells.size + 2
  let syms := regs ++ ins
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
  let dir ← IO.FS.createTempDir
  let mut results : Array SigResult := #[]
  for r in m.regs do
    let some (_, _, srcs) := mt.regs.find? (fun t => t.1 == r.name)
      | IO.eprintln s!"eqcheck: internal: register '{r.name}' unmatched"; return 1
    results := results.push
      (← runSignal dir "reg" r.name r.width (regMiter env mt fuel syms r srcs))
  for o in m.outs do
    match nl.port? o.name with
    | none =>
        results := results.push
          { kind := "out", name := o.name, width := o.width, vars := 0,
            clauses := 0, lrat := 0, ms := 0, verdict := "FAIL",
            detail := "no netlist port of that name" }
    | some p =>
        if p.bits.size != o.width then
          results := results.push
            { kind := "out", name := o.name, width := o.width, vars := 0,
              clauses := 0, lrat := 0, ms := 0, verdict := "FAIL",
              detail := s!"netlist port width {p.bits.size} ≠ {o.width}" }
        else
          results := results.push
            (← runSignal dir "out" o.name o.width (outMiter env mt fuel syms o p.bits))
  let mut clauses := 0
  let mut lrat := 0
  let mut ms := 0
  let mut bad := 0
  for r in results do
    let pad := String.ofList (List.replicate (max 1 (18 - r.name.length)) ' ')
    IO.println s!"  [{r.verdict}] {r.kind} {r.name}{pad}w={r.width} \
      vars={r.vars} clauses={r.clauses} lrat={r.lrat} {r.ms}ms"
    unless r.detail == "" do IO.println s!"         {r.detail}"
    clauses := clauses + r.clauses
    lrat := lrat + r.lrat
    ms := ms + r.ms
    if r.verdict != "PASS" then bad := bad + 1
  IO.println s!"  totals: {results.size} signals, {clauses} clauses, \
    {lrat} LRAT lines, {ms}ms solver+checker wall time"
  IO.println "  (the CNF encoder is untrusted in v1: the claim is \"if the \
    encoding is faithful, netlist ≡ module\"; every UNSAT is LRAT-certified \
    and re-checked by Loom.Dp.Cert.checkLrat, the proved checker)"
  if bad == 0 then
    IO.println s!"EQCHECK OK ({results.size} signals, {clauses} clauses, LRAT-verified)"
    return 0
  else
    IO.println s!"EQCHECK FAILED ({bad} of {results.size} signals differ)"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [v, j] => check v j
  | _ =>
      IO.eprintln "usage: eqcheck <module.v> <netlist.json>"
      return 2
