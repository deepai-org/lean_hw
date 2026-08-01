-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Netlist.Mem
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

/-! The three miters, each preceded by the matching's *equality*
assumptions (register bits yosys merged into one flip-flop). The unit
assumptions are asserted inside the miters themselves; keeping the pair
half here means `Loom/Netlist/Miter.lean` needs no change. -/

def regMiterE (env : NetlistEnv) (mt : Matching) (fuel : Nat)
    (syms : List (String × Nat)) (rd : RegDef) (srcs : Array RegSrc) : M Unit := do
  assertEqs mt.eqs; regMiter env mt fuel syms rd srcs

def outMiterE (env : NetlistEnv) (mt : Matching) (fuel : Nat)
    (syms : List (String × Nat)) (od : OutDef) (bits : Array SigBit) : M Unit := do
  assertEqs mt.eqs; outMiter env mt fuel syms od bits

/-- A cone miter under a guard: the two sides need only agree where the
guard holds. Write addresses and write data are compared this way, because
`WritePort.commit` consults them only when the port's enable is set — and
yosys is entitled to (and does) simplify a memory's `ADDR`/`DI` logic using
the write enable as a don't-care condition. -/
def coneMiterUnder (env : NetlistEnv) (mt : Matching) (fuel : Nat)
    (syms : List (String × Nat)) (guard : Expr 1) {w : Nat} (e : Expr w)
    (bits : Array SigBit) : M Unit := do
  assertEqs mt.eqs
  let g ← blastE syms guard
  assert g[0]!
  coneMiter env mt fuel syms e bits

def coneMiterE (env : NetlistEnv) (mt : Matching) (fuel : Nat)
    (syms : List (String × Nat)) {w : Nat} (e : Expr w) (bits : Array SigBit) :
    M Unit := do
  assertEqs mt.eqs; coneMiter env mt fuel syms e bits

/-- Signals whose failure is *known and recorded* elsewhere. An
acknowledged failure is still printed, in full, as an `ACK` line and
counted in the verdict — the point is that a recorded defect stays visible
instead of becoming invisible. Mirrors `scripts/check_mem_init.py --allow`. -/
def check (vPath jsonPath : String) (ack : List String := []) : IO UInt32 := do
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
  -- `rst` is a free symbol on both sides (it is the reset input port), and
  -- the memory write ports need to name it: the printed write lines sit in
  -- the `else` arm of `if (rst)`, so a bank's realized write enable is the
  -- port's enable AND NOT rst.
  let syms := regs ++ ins ++ reads ++ [("rst", 1)]
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
          (← runSignal dir "reg" r.name r.width (regMiterE env mt fuel syms r srcs))
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
            (← runSignal dir "out" o.name o.width (outMiterE env mt fuel syms o p.bits))
  -- ── Memories (D31) ──────────────────────────────────────────────────
  -- Every memory primitive in the netlist must belong to a declared
  -- µVerilog memory: an array the checker cannot account for is a matching
  -- failure, not something to walk past.
  let memCells := nl.cells.filter (fun c => isMemCell c.type)
  for c in memCells do
    unless m.mems.any (fun mm => mm.name == memBankOf c.name) do
      IO.eprintln s!"eqcheck: MATCHING FAILURE: netlist memory primitive \
        '{c.name}' ({c.type}) belongs to no declared µVerilog memory"
      return 1
  for mm in m.mems do
    let wsites := cp.writes.filter (fun w => w.mem == mm.name)
    let rsites := cp.reads.filter (fun r => r.mem == mm.name)
    if wsites.length != mm.wrPorts.length then
      IO.eprintln s!"eqcheck: internal: memory '{mm.name}' has \
        {mm.wrPorts.length} write ports but {wsites.length} printed write lines"
      return 1
    let cs := (memCells.filter (fun c => memBankOf c.name == mm.name)).toArray
    let depth := 2 ^ mm.addrWidth
    let imgNonZero := (List.range depth).any (fun a => mm.init a != 0)
    -- The write cones as the *printed* wires carry them. On a bank realized
    -- in primitives these are subsumed by the pin miters below, so they are
    -- only run where there is no bank.
    let printedCones : IO (Array SigResult) := do
      let mut out : Array SigResult := #[]
      for (site, port) in wsites.zip mm.wrPorts do
        let cone (tag wire : String) (w : Nat) (e : Expr w) : IO SigResult := do
          let nm := s!"{mm.name}.{tag}"
          match namedBits nl wire w with
          | none => pure (skipped s!"wr{tag}" nm w
              s!"EXCLUDED: synthesis did not keep a net named '{wire}' (it was \
                absorbed into the memory's port logic)")
          | some bits => runSignal dir s!"wr{tag}" nm w (coneMiterE env mt fuel syms e bits)
        out := out.push (← cone "en" site.en 1 port.en)
        out := out.push (← cone "addr" site.addr mm.addrWidth port.addr)
        out := out.push (← cone "data" site.data mm.dataWidth port.data)
      pure out
    if cs.isEmpty then
      -- No memory primitive: either the storage is unobservable and yosys
      -- deleted it, or `memory_libmap` left the array in fabric flip-flops.
      if rsites.isEmpty then
        results := results.push (skipped "mem" mm.name mm.dataWidth
          "EXCLUDED (storage): no read port, so the array is unobservable and \
           synthesis deleted it; the write cones are checked all the same")
      else
        results := results.push (skipped "mem" mm.name mm.dataWidth
          s!"EXCLUDED (storage): no memory primitive — the array is realized \
            outside them, as fabric flip-flops (a written array libmap left in \
            flops) or as LUT ROM (an array no rule writes). Its transition and \
            its {if imgNonZero then "NON-ZERO" else "all-zero"} image are \
            inside the cut read wire. Not a D30 hazard: flip-flop INIT and LUT \
            truth tables are both carried by the bitstream; distributed RAM is \
            the realization whose image is not.")
      results := results ++ (← printedCones)
      continue
    match buildBank mm.name depth mm.dataWidth cs with
    | .error e =>
        results := results.push (failed "mem" mm.name mm.dataWidth e)
        results := results ++ (← printedCones)
    | .ok bank =>
      let cw := bank.cellWidth
      let k := Nat.log2 bank.cellDepth
      let hi := mm.addrWidth - k
      -- (1) The reset image.
      let shape := s!"{bank.cells.size} × {bank.cells[0]!.ty} \
        ({bank.nRepl} replica(s) × {bank.nDepth} depth group(s) × \
        {bank.nLane} lane(s)), {bank.initOnes} INIT bit(s) set"
      match checkImage bank mm with
      | .mismatch a j d r =>
          results := results.push (failed "meminit" mm.name mm.dataWidth
            s!"RESET IMAGE MISMATCH in bank '{mm.name}': the module declares \
              bit {j} of word {a} = {if d then 1 else 0}, the netlist's INIT \
              parameters give {if r then 1 else 0} ({shape})")
      | .undelivered fam ty cell =>
          results := results.push (failed "meminit" mm.name mm.dataWidth
            s!"RESET IMAGE NOT DELIVERED for bank '{mm.name}': the image is \
              NON-ZERO but synthesis mapped the bank to {fam.name} ({ty}, e.g. \
              '{cell}'). The configuration path carries a block-RAM image and \
              does NOT carry a distributed-RAM one, so this bank comes up \
              all-zero on silicon while simulation says otherwise (D30). \
              {shape}")
      | .ok nz =>
          results := results.push
            { kind := "meminit", name := mm.name, width := mm.dataWidth,
              vars := 0, clauses := 0, lrat := 0, ms := 0, verdict := "PASS",
              detail := s!"reset image {if nz then "NON-ZERO" else "all-zero"}, \
                delivered by {bank.family.name}: {shape}" }
      -- (2) Write-port semantics, against the primitives' own pins.
      if mm.wrPorts.length > 1 then
        results := results.push (skipped "wrport" mm.name mm.dataWidth
          s!"EXCLUDED (write ports): {mm.wrPorts.length} write ports share one \
            bank; the checker models one committing port per primitive, not \
            the last-write-wins fold across several")
      else
        for port in mm.wrPorts do
          for r in [0:bank.nRepl] do
            for g in [0:bank.nDepth] do
              let tag := if bank.nRepl == 1 && bank.nDepth == 1 then mm.name
                         else s!"{mm.name}[r{r}g{g}]"
              let some c0 := bank.at r g 0
                | results := results.push (failed "wren" tag 1 "short bank"); continue
              -- write clock
              match (c0.wrClk[0]? : Option SigBit) with
              | some (.net cn) =>
                  unless env.clk.contains cn do
                    results := results.push (failed "wrclk" tag 1
                      s!"'{c0.name}': the write clock pin is not the clock net")
              | _ =>
                  results := results.push (failed "wrclk" tag 1
                    s!"'{c0.name}': the write clock pin is not connected to a net")
              -- write enable: all enable bits must be one net, and the cone
              -- must be the port's enable, restricted to this depth group.
              let enA : Expr 1 :=
                Expr.and (Expr.and port.en (Expr.not (Expr.reg 1 "rst")))
                  (if bank.nDepth == 1 then Expr.lit 1#1
                   else Expr.eq (Expr.slice port.addr k hi)
                                (Expr.lit (BitVec.ofNat hi g)))
              if c0.wrEn.isEmpty || c0.wrEn.any (fun b => b != c0.wrEn[0]!) then
                results := results.push (failed "wren" tag 1
                  s!"'{c0.name}': the write-enable pins are not all driven by \
                    one net (byte enables are not modelled)")
              else
                results := results.push (← runSignal dir "wren" tag 1
                  (coneMiterE env mt fuel syms enA #[c0.wrEn[0]!]))
              -- write address: the cell's own address bits are the low bits.
              results := results.push (← runSignal dir "wraddr" tag k
                (coneMiterUnder env mt fuel syms enA (Expr.slice port.addr 0 k)
                  c0.wrAddr))
              -- write data: lane `l` carries word bits `l*cw …`.
              for l in [0:bank.nLane] do
                let some c := bank.at r g l
                  | results := results.push (failed "wrdata" tag 0 "short bank"); continue
                let n := min cw (mm.dataWidth - l * cw)
                let ltag := if bank.nLane == 1 then tag else s!"{tag}.{l}"
                results := results.push (← runSignal dir "wrdata" ltag n
                  (coneMiterUnder env mt fuel syms enA
                    (Expr.slice port.data (l * cw) n) (c.wrData.extract 0 n)))
      -- (3) Read ports: match each netlist read port to a printed read site
      -- by *proving* the address cones equal, then check the data path.
      let mut taken : List String := []
      for r in [0:bank.nRepl] do
        let nports := ((bank.at r 0 0).map (·.rdPorts.size)).getD 0
        for q in [0:nports] do
          let tag := s!"{mm.name}[r{r}p{q}]"
          let some c0 := bank.at r 0 0 | continue
          let some (apins, _) := c0.rdPorts[q]? | continue
          -- which read site is this port?
          let mut hit : Option Parse.ReadSiteInfo := none
          for rs in rsites do
            if hit.isNone && !taken.contains rs.wire then
              match symExpr rs.addr with
              | some ⟨aw, ae⟩ =>
                  if aw == mm.addrWidth then
                    let probe ← runSignal dir "rdaddr" tag k
                      (coneMiterE env mt fuel syms (Expr.slice ae 0 k) apins)
                    if probe.verdict == "PASS" then hit := some rs
              | none => pure ()
          match hit with
          | none =>
              results := results.push (failed "rdaddr" tag k
                s!"no printed read site of '{mm.name}' has this port's address \
                  cone — the checker cannot say what this read port reads")
          | some rs =>
            taken := rs.wire :: taken
            results := results.push
              { kind := "rdaddr", name := tag, width := k, vars := 0,
                clauses := 0, lrat := 0, ms := 0, verdict := "PASS",
                detail := s!"address cone equals '{rs.addr}' (site \
                  '{rs.wire} = {rs.mem}[{rs.addr}]')" }
            -- The read port's data pins, and what µVerilog value they are.
            let mut acc : Array SigBit := #[]
            if bank.nDepth == 1 then
              for l in [0:bank.nLane] do
                match (bank.at r 0 l).bind (fun c => c.rdPorts[q]?) with
                | some (_, d) => acc := acc ++ d
                | none => pure ()
            let dbits := acc.extract 0 mm.dataWidth
            let asWire :=
              if bank.nDepth != 1 then none
              else match namedBits nl rs.wire mm.dataWidth with
                   | some b => if b == dbits then some rs.wire else none
                   | none => none
            let asReg :=
              if bank.nDepth != 1 then none
              else mt.memRegs.findSome? fun (rn, _, _) =>
                     match namedBits nl rn mm.dataWidth with
                     | some b => if b == dbits then some rn else none
                     | none => none
            -- read shape: async LUT RAM vs D19 synchronous block RAM.
            if bank.nDepth != 1 then
              results := results.push (skipped "rdshape" tag mm.dataWidth
                s!"EXCLUDED (read data): the bank is split {bank.nDepth} ways in \
                  depth, so the read value is muxed across groups by logic \
                  outside the array; the checker ties data pins to a µVerilog \
                  value only for an unsplit bank")
            else if c0.regOut then
              results := results.push (failed "rdshape" tag mm.dataWidth
                s!"'{c0.name}' has DOx_REG set: two cycles of read latency, \
                  not the one cycle a D19 sync read means")
            else if c0.syncRead && c0.wrMode != "READ_FIRST" then
              results := results.push (failed "rdshape" tag mm.dataWidth
                s!"'{c0.name}' is configured {c0.wrMode}; the µVerilog read \
                  evaluates against the PRE-cycle contents (READ_FIRST)")
            else if c0.syncRead then
              -- One cycle of latency: sound only if the module's read feeds a
              -- register that synthesis absorbed into this read port (D19).
              match asReg with
              | some rn =>
                  results := results.push
                    { kind := "rdshape", name := tag, width := mm.dataWidth,
                      vars := 0, clauses := 0, lrat := 0, ms := 0,
                      verdict := "PASS",
                      detail := s!"D19 synchronous read: {c0.ty} drives the read \
                        register '{rn}' directly (one cycle, WRITE_MODE \
                        {c0.wrMode}) — the register the module writes with \
                        '{rs.wire}' IS this read port's output" }
              | none =>
                  if asWire.isSome then
                    results := results.push (failed "rdshape" tag mm.dataWidth
                      s!"the netlist reads '{mm.name}' SYNCHRONOUSLY ({c0.ty}, \
                        one cycle of latency) but its output is the printed \
                        COMBINATIONAL wire '{rs.wire}': the netlist is a cycle \
                        behind the module")
                  else
                    results := results.push (skipped "rdshape" tag mm.dataWidth
                      s!"EXCLUDED (read data): {c0.ty} reads synchronously and \
                        its data pins drive neither the printed wire \
                        '{rs.wire}' (synthesis dropped the name) nor a read \
                        register directly, so the checker cannot tie this read \
                        port's output to a µVerilog value")
            else
              match asWire with
              | some w =>
                  results := results.push
                    { kind := "rdshape", name := tag, width := mm.dataWidth,
                      vars := 0, clauses := 0, lrat := 0, ms := 0,
                      verdict := "PASS",
                      detail := s!"asynchronous read: the {c0.ty} outputs ARE \
                        the printed read wire '{w}', so this read port reads \
                        the primitives the write port writes" }
              | none =>
                  match asReg with
                  | some rn =>
                      results := results.push
                        { kind := "rdshape", name := tag, width := mm.dataWidth,
                          vars := 0, clauses := 0, lrat := 0, ms := 0,
                          verdict := "PASS",
                          detail := s!"asynchronous read: the {c0.ty} outputs \
                            drive the read register '{rn}' directly" }
                  | none =>
                      results := results.push (skipped "rdshape" tag mm.dataWidth
                        s!"EXCLUDED (read data): the {c0.ty} outputs drive \
                          neither the printed wire '{rs.wire}' (synthesis \
                          dropped the name) nor a read register directly, so \
                          the checker cannot tie this read port's output to a \
                          µVerilog value")
      for rs in rsites do
        unless taken.contains rs.wire do
          results := results.push (skipped "rdaddr" s!"{mm.name}[{rs.addr}]"
            mm.dataWidth
            s!"EXCLUDED (read port): the printed read site '{rs.wire}' matched \
              no read port of the bank")
  let mut clauses := 0
  let mut lrat := 0
  let mut ms := 0
  let mut bad := 0
  let mut acked := 0
  let mut skip := 0
  -- Acknowledged failures: recorded elsewhere, still printed.
  results := results.map fun r =>
    if r.verdict == "FAIL" && ack.contains r.name then
      { r with verdict := "ACK" } else r
  for r in results do
    let pad := String.ofList (List.replicate (max 1 (18 - r.name.length)) ' ')
    IO.println s!"  [{r.verdict}] {r.kind} {r.name}{pad}w={r.width} \
      vars={r.vars} clauses={r.clauses} lrat={r.lrat} {r.ms}ms"
    unless r.detail == "" do IO.println s!"         {r.detail}"
    clauses := clauses + r.clauses
    lrat := lrat + r.lrat
    ms := ms + r.ms
    if r.verdict == "FAIL" then bad := bad + 1
    if r.verdict == "ACK" then acked := acked + 1
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
  if acked > 0 then
    IO.println s!"  ACKNOWLEDGED ({acked} signal(s) marked [ACK] above): a \
      failure recorded elsewhere and deliberately not fixed here. Named on \
      the command line with --ack, never suppressed."
  if bad == 0 then
    IO.println s!"EQCHECK OK ({checked} signals, {skip} excluded, \
      {acked} acknowledged, {clauses} clauses, LRAT-verified)"
    return 0
  else
    IO.println s!"EQCHECK FAILED ({bad} of {checked} checked signals differ)"
    return 1

def main (args : List String) : IO UInt32 := do
  let rec go (as : List String) (ack : List String) : IO UInt32 := do
    match as with
    | "--ack" :: names :: rest =>
        go rest (ack ++ (names.splitOn ",").filter (· != ""))
    | [v, j] => check v j ack
    | _ =>
        IO.eprintln "usage: eqcheck [--ack name,name] <module.v> <netlist.json>"
        return 2
  go args []
