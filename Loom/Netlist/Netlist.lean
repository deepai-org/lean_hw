-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Netlist.Cells

/-!
# Netlist cones and signal matching (D22)

Turns a `write_json` module into (a) a driver map, (b) a combinational cone
evaluator producing a `Bit` per net over the shared free variables
(register state bits, module inputs, `rst`), and (c) the *matching* between
the µVerilog module's registers/ports and the netlist's flip-flops/ports.

Matching is a bijection by construction: every IR register bit is claimed
by exactly one flip-flop (or by a constant — see below), and any
flip-flop left unclaimed is a hard failure, never a skip.

**Constant-folded register bits.** yosys's `wreduce`/`opt_dff` replace a
register bit that provably holds a constant from reset by that constant, so
the netlist's transition function differs from the module's *on unreachable
states*. Such a bit is recorded as an assumption `bit = c` added to every
miter; the assumption is discharged by the very miters that use it: the
register's own miter is checked with `rst` free, and its `rst = 1` branch
forces the module's *reset* value of that bit to equal `c` (a comparison of
two constants, independent of the assumption), which is the base case, while
the `rst = 0` branch is the induction step. The verdict is therefore
equivalence of the two transition functions on every state reachable from
reset — which is exactly what the emission claim needs.
-/

namespace Loom.Netlist

open Loom.Dp.Cnf

/-- The free variable standing for bit `i` of `name` (a register or an
input port) — shared by both sides of the miter. -/
def stateBit (name : String) (w i : Nat) : Bit := .lit (.reg 0 name w i) true

/-- The free variable standing for the synchronous reset pin. -/
def rstBit : Bit := stateBit "rst" 1 0

/-- Where a matched register bit lives in the netlist. -/
inductive RegSrc where
  | folded (b : Bool)   -- constant-folded by the synthesizer
  | ff (net : Nat)      -- driven by the flip-flop whose `Q` is this net
  /-- Driven by a memory hard block's data output: the µVerilog read
  register was absorbed into the memory's read port (D19 sync read), so
  its next-state function lives inside a cell this checker does not model.
  Such a register is *excluded* from the comparison, by name, with the
  cell reported. -/
  | mem (cell : String) (ty : String)
deriving Repr, Inhabited

/-- A netlist prepared for cone evaluation. -/
structure NetlistEnv where
  cells : Array Cell
  /-- net → (cell index, output port, bit index within that port). -/
  drv   : Std.HashMap Nat (Nat × String × Nat)
  /-- net → free variable (flip-flop `Q` nets and input-port bits). -/
  seed  : Std.HashMap Nat Bit
  /-- nets carrying the clock (illegal inside a data cone). -/
  clk   : Std.HashSet Nat
  /-- `Q` nets of flip-flops that match no µVerilog register bit and are
  tolerated because the design has memories: array storage realized in
  fabric, and registers synthesis retimed into a memory read path. A
  *checked* cone that reaches one is still an error — a `MEMCUT` one, so
  the affected signal is reported as excluded rather than silently
  dropped. -/
  memFF : Std.HashSet Nat := {}
deriving Inhabited

/-- Cell-type validation plus the driver map. -/
def buildEnv (m : NlModule) (seed : Std.HashMap Nat Bit)
    (clk : Std.HashSet Nat) (memFF : Std.HashSet Nat := {}) :
    Except String NetlistEnv := do
  let cells := m.cells.toArray
  let mut drv : Std.HashMap Nat (Nat × String × Nat) := {}
  for h : ci in [0:cells.size] do
    let c := cells[ci]
    if let some (_, outs) := memCellPorts c.type then
      -- A memory hard block is a cut point: only its data outputs enter the
      -- driver map (so a cone reaching one can be reported), and its input
      -- pins are neither required nor evaluated.
      for p in outs do
        match c.conn? p with
        | none => pure ()
        | some bits =>
            for h : j in [0:bits.size] do
              match bits[j] with
              | .net n =>
                  if drv.contains n then
                    throw s!"net {n} has multiple drivers (second: '{c.name}')"
                  drv := drv.insert n (ci, p, j)
              | _ => pure ()
      continue
    match cellPorts c.type with
    | none => throw s!"unsupported cell type '{c.type}' (instance '{c.name}')"
    | some (ins, outs) =>
        for p in ins do
          match c.conn? p with
          | none => throw s!"{c.type} '{c.name}': input pin '{p}' is unconnected"
          | some bits =>
              if bits.isEmpty then
                throw s!"{c.type} '{c.name}': input pin '{p}' has no bits"
              if c.type == "CARRY4" && (p == "DI" || p == "S") && bits.size != 4 then
                throw s!"CARRY4 '{c.name}': pin '{p}' has {bits.size} bits, expected 4"
        for p in outs do
          match c.conn? p with
          | none => pure ()
          | some bits =>
              for h : j in [0:bits.size] do
                match bits[j] with
                | .net n =>
                    if drv.contains n then
                      throw s!"net {n} has multiple drivers (second: '{c.name}')"
                    drv := drv.insert n (ci, p, j)
                | _ => pure ()
  pure { cells := cells, drv := drv, seed := seed, clk := clk, memFF := memFF }

/-- Nets that carry the clock: the `clk` port and everything a chain of
pass-through buffers propagates it to. -/
def clockNets (m : NlModule) : Except String (Std.HashSet Nat) := do
  let some p := m.port? "clk"
    | throw "netlist module has no 'clk' port"
  let mut s : Std.HashSet Nat := {}
  for b in p.bits do
    match b with
    | .net n => s := s.insert n
    | _ => pure ()
  let cells := m.cells.toArray
  -- Saturate: one pass per cell suffices for any buffer chain.
  for _ in [0:cells.size] do
    let mut changed := false
    for c in cells do
      if isBuf c.type then
        match c.conn? "I", c.conn? "O" with
        | some i, some o =>
            match (i[0]? : Option SigBit), (o[0]? : Option SigBit) with
            | some (.net a), some (.net b) =>
                if s.contains a && !s.contains b then
                  s := s.insert b; changed := true
            | _, _ => pure ()
        | _, _ => pure ()
    unless changed do break
  pure s

/-- Evaluate one signal bit into the CNF encoding, memoizing per net.
`fuel` bounds the combinational depth; exhausting it means a combinational
loop (or a netlist deeper than its own cell count, which is impossible for
an acyclic one). -/
def evalSig (env : NetlistEnv) : Nat → SigBit → M Bit
  | _, .zero => pure (.const false)
  | _, .one => pure (.const true)
  | _, .undef => throw "an 'x' constant appears in a data cone"
  | _, .highz => throw "a 'z' constant appears in a data cone"
  | 0, .net n => throw s!"combinational loop (or excessive depth) at net {n}"
  | fuel + 1, .net n => do
      match env.seed[n]? with
      | some b => pure b
      | none =>
        if env.clk.contains n then
          throw s!"net {n} carries the clock but is used as data"
        match (← get).memo[n]? with
        | some b => pure b
        | none =>
          match env.drv[n]? with
          | none => throw s!"net {n} is undriven"
          | some (ci, _, _) => do
              let c := env.cells[ci]!
              if isMemCell c.type then
                throw s!"MEMCUT: net {n} is a data output of {c.type} '{c.name}' \
                  that no µVerilog read wire names — the read register was \
                  absorbed into the memory's read port, so this cone crosses \
                  the memory boundary (EQCHECK_SPEC.md §Scope)"
              if isFF c.type then
                if env.memFF.contains n then
                  throw s!"MEMCUT: net {n} comes from {c.type} '{c.name}', a \
                    flip-flop with no µVerilog register bit — memory storage \
                    in fabric, or a register synthesis retimed into a memory \
                    read path, so this cone crosses the memory boundary \
                    (EQCHECK_SPEC.md §Scope)"
                throw s!"{c.type} '{c.name}' drives net {n} but was not matched \
                  to a µVerilog register"
              let some (ins, _) := cellPorts c.type
                | throw s!"unsupported cell type '{c.type}'"
              let mut pins : List (String × Array Bit) := []
              for p in ins do
                let sig := (c.conn? p).getD #[]
                let mut bs : Array Bit := #[]
                for b in sig do
                  bs := bs.push (← evalSig env fuel b)
                pins := (p, bs) :: pins
              let pin := fun p => ((pins.find? (fun kv => kv.1 == p)).map (·.2)).getD #[]
              let outs ← evalCell c pin
              for (p, bs) in outs do
                let sig := (c.conn? p).getD #[]
                for h : j in [0:bs.size] do
                  match sig[j]? with
                  | some (.net k) =>
                      modify fun s => { s with memo := s.memo.insert k bs[j] }
                  | _ => pure ()
              match (← get).memo[n]? with
              | some b => pure b
              | none => throw s!"cell '{c.name}' did not drive net {n}"

/-- Evaluate a whole signal (a list of bits). -/
def evalBits (env : NetlistEnv) (fuel : Nat) (bits : Array SigBit) :
    M (Array Bit) := do
  let mut out : Array Bit := #[]
  for b in bits do
    out := out.push (← evalSig env fuel b)
  pure out

/-! ## Matching -/

/-- The result of matching the µVerilog module against the netlist. -/
structure Matching where
  /-- Per IR register: name, width, and the netlist source of each bit. -/
  regs : List (String × Nat × Array RegSrc)
  /-- net → the flip-flop cell driving it (matched flip-flops only). -/
  ffOf : Std.HashMap Nat Cell
  /-- net → free variable, for `evalSig`. -/
  seed : Std.HashMap Nat Bit
  /-- Unit assumptions: constant-folded register bits (see the header). -/
  assumptions : Array Bit
  /-- Number of constant-folded register bits. -/
  folded : Nat
  /-- Registers whose bits come out of a memory hard block (D19 sync-read
  registers absorbed into a read port): `(register, cell, cell type)`.
  Their transition function is inside the cell — excluded, and reported. -/
  memRegs : List (String × String × String)
  /-- Memory read wires whose netlist nets survived synthesis, and are
  therefore cut (side A's free symbol seeded onto side B's nets). -/
  cutReads : List String
  /-- Memory read wires with no netlist net of that name: the read fed a
  register that synthesis absorbed into the memory's read port. Any signal
  whose cone crosses one is excluded (side B reports `MEMCUT`). -/
  absorbedReads : List String
  /-- Flip-flops that drive a cut read wire: synthesis retimed a register
  through the array (a registered ROM read). Inside the cut, hence not
  part of the register bijection — counted and reported. -/
  cutFFs : Nat
  /-- Cut read-wire bits yosys folded to a constant *from the array
  contents*: assumed, not checked (see `matchModule`). -/
  foldedReads : Nat
  /-- `Q` nets of tolerated unmatched flip-flops (see `NetlistEnv.memFF`). -/
  memFF : Std.HashSet Nat
  /-- A few of them, by cell name, for the report. -/
  memFFNames : List String
deriving Inhabited

/-- The netlist bit named `name[i]` (or `name`, for a one-bit signal that
`splitnets` left alone). -/
def bitNet (m : NlModule) (name : String) (w i : Nat) :
    Except String SigBit := do
  let entry :=
    match m.net? s!"{name}[{i}]" with
    | some e => some e
    | none => if w == 1 then m.net? name else none
  match entry with
  | none =>
      throw s!"no netlist net for '{name}[{i}]' — the register/port bit was \
        renamed away by synthesis (was the netlist produced with `splitnets`?)"
  | some e =>
      if e.bits.size != 1 then
        throw s!"netlist net '{e.name}' has {e.bits.size} bits, expected 1"
      else pure e.bits[0]!

/-- All bits of a named netlist signal, if synthesis kept the name. -/
def namedBits (m : NlModule) (name : String) (w : Nat) :
    Option (Array SigBit) := Id.run do
  let mut out : Array SigBit := #[]
  for i in [0:w] do
    match bitNet m name w i with
    | .error _ => return none
    | .ok b => out := out.push b
  return some out

/-- Match IR registers to flip-flops (bijectively) and IR inputs to
netlist input ports. `regs` and `ins` are `(name, width)` pairs; `reads`
are the memory read wires (`parseCut`'s cut points), also `(name, width)`. -/
def matchModule (m : NlModule) (regs ins reads : List (String × Nat))
    (strictFFs : Bool := true) : Except String Matching := do
  -- All flip-flops, by their Q net; all memory hard blocks, by data output.
  let mut memByOut : Std.HashMap Nat Cell := {}
  for c in m.cells do
    if let some (_, outs) := memCellPorts c.type then
      for p in outs do
        match c.conn? p with
        | none => pure ()
        | some bits =>
            for b in bits do
              match b with
              | .net n => memByOut := memByOut.insert n c
              | _ => pure ()
  let mut ffByQ : Std.HashMap Nat Cell := {}
  for c in m.cells do
    if isFF c.type then
      match c.conn? "Q" with
      | some qs =>
          if qs.size != 1 then
            throw s!"{c.type} '{c.name}': Q has {qs.size} bits"
          match qs[0]! with
          | .net n =>
              if ffByQ.contains n then
                throw s!"two flip-flops drive net {n}"
              ffByQ := ffByQ.insert n c
          | b => throw s!"{c.type} '{c.name}': Q is the constant {b}"
      | none => throw s!"{c.type} '{c.name}': no Q pin"
  -- Memory read wires first: cut where synthesis kept the wire's name,
  -- absorbed (and reported) where it did not. The cut nets are seeded with
  -- free variables shared by both sides, so whatever drives them in the
  -- netlist — a distributed-RAM output, a block-RAM output, or a flip-flop
  -- yosys retimed *through* the array (a registered ROM read: the address
  -- register pushed into the read port) — is outside the comparison.
  let mut used : Std.HashSet Nat := {}
  let mut seed : Std.HashMap Nat Bit := {}
  let mut readNets : Std.HashSet Nat := {}
  let mut cutReads : List String := []
  let mut absorbedReads : List String := []
  let mut assumptions : Array Bit := #[]
  let mut foldedReads := 0
  for (nm, w) in reads do
    match namedBits m nm w with
    | none => absorbedReads := nm :: absorbedReads
    | some bits =>
        cutReads := nm :: cutReads
        for h : i in [0:bits.size] do
          match bits[i] with
          | .net n =>
              readNets := readNets.insert n
              seed := seed.insert n (stateBit nm w i)
          | .zero =>
              -- yosys folded this read-wire bit to a constant *from the array
              -- contents*. Unlike a folded register bit there is no reset
              -- branch to discharge it: it is an assumption about the array,
              -- which is exactly what cell identity carries. Counted.
              assumptions := assumptions.push (stateBit nm w i).not
              foldedReads := foldedReads + 1
          | .one =>
              assumptions := assumptions.push (stateBit nm w i)
              foldedReads := foldedReads + 1
          | b => throw s!"memory read wire '{nm}[{i}]' is the constant {b}"
  let mut out : List (String × Nat × Array RegSrc) := []
  let mut folded := 0
  let mut memRegs : List (String × String × String) := []
  for (name, w) in regs do
    let mut srcs : Array RegSrc := #[]
    for i in [0:w] do
      match ← bitNet m name w i with
      | .zero =>
          srcs := srcs.push (.folded false)
          assumptions := assumptions.push (stateBit name w i).not
          folded := folded + 1
      | .one =>
          srcs := srcs.push (.folded true)
          assumptions := assumptions.push (stateBit name w i)
          folded := folded + 1
      | .net n =>
          if readNets.contains n then
            throw s!"'{name}[{i}]' (net {n}) is also a memory read wire — the \
              cut would rename it"
          else if let some c := memByOut[n]? then
            -- A read register absorbed into a memory read port: its value is
            -- still a shared free variable (consumers are checked normally),
            -- but its own transition function is inside the cell.
            seed := seed.insert n (stateBit name w i)
            srcs := srcs.push (.mem c.name c.type)
          else
            unless ffByQ.contains n do
              throw s!"'{name}[{i}]' (net {n}) is not driven by a flip-flop"
            if used.contains n then
              throw s!"net {n} is claimed by two µVerilog register bits"
            used := used.insert n
            seed := seed.insert n (stateBit name w i)
            srcs := srcs.push (.ff n)
      | b => throw s!"'{name}[{i}]' is the constant {b}"
    if srcs.any (fun s => match s with | .mem _ _ => true | _ => false) then
      unless srcs.all (fun s => match s with | .mem _ _ => true | _ => false) do
        throw s!"register '{name}' is only partly driven by a memory hard \
          block — the checker cannot split it"
      match srcs[0]! with
      | .mem cn ty => memRegs := (name, cn, ty) :: memRegs
      | _ => pure ()
    out := (name, w, srcs) :: out
  -- Bijection: no unmatched flip-flop — except flip-flops that drive a cut
  -- memory read wire, which are inside the cut (see above) and counted.
  let cutFFs := (ffByQ.toList.filter (fun kv => readNets.contains kv.1)).length
  let unmatched := ffByQ.toList.filter
    (fun kv => !used.contains kv.1 && !readNets.contains kv.1)
  let mut memFF : Std.HashSet Nat := {}
  let mut memFFNames : List String := []
  unless unmatched.isEmpty do
    let names := (unmatched.take 6).map (fun kv => s!"{kv.2.type} '{kv.2.name}'")
    if strictFFs then
      throw s!"{unmatched.length} flip-flop(s) in the netlist match no µVerilog \
        register bit: {String.intercalate ", " names}"
    -- The design has memories: an unmatched flip-flop is array storage
    -- realized in fabric, or a register retimed into a memory read path.
    -- Tolerated *and tracked* — `evalSig` turns any checked cone that
    -- reaches one into a reported exclusion.
    for kv in unmatched do memFF := memFF.insert kv.1
    memFFNames := names
  -- Input ports: `rst` plus the declared µVerilog inputs.
  for p in m.ports do
    if p.dir == "input" && p.name != "clk" then
      let w :=
        if p.name == "rst" then 1
        else match ins.find? (fun kv => kv.1 == p.name) with
             | some (_, w) => w
             | none => 0
      if p.name != "rst" && w == 0 then
        throw s!"netlist input port '{p.name}' has no µVerilog counterpart"
      if p.bits.size != w then
        throw s!"input port '{p.name}': netlist width {p.bits.size} ≠ µVerilog width {w}"
      for h : i in [0:p.bits.size] do
        match p.bits[i] with
        | .net n => seed := seed.insert n (stateBit p.name w i)
        | _ => pure ()
  for (nm, _) in ins do
    unless (m.ports.any (fun p => p.name == nm && p.dir == "input")) do
      throw s!"µVerilog input '{nm}' has no netlist input port"
  unless (m.ports.any (fun p => p.name == "rst" && p.dir == "input")) do
    throw "netlist module has no 'rst' input port"
  pure { regs := out.reverse, ffOf := ffByQ, seed := seed,
         assumptions := assumptions, folded := folded,
         memRegs := memRegs.reverse, cutReads := cutReads.reverse,
         absorbedReads := absorbedReads.reverse, cutFFs := cutFFs,
         foldedReads := foldedReads, memFF := memFF, memFFNames := memFFNames }

end Loom.Netlist
