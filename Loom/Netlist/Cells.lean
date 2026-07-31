-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Dp.Cnf
import Loom.Netlist.Json

/-!
# The synthesized cell library (D22)

Bit-level semantics of the cells `synth_xilinx -flatten -nowidelut` emits,
expressed as a Tseitin encoder over `Loom.Dp.Cnf`'s `Bit`/`Var`/`BClause`
vocabulary (the CNF layer this checker reuses).

* combinational: `LUT1`..`LUT6` (truth table from `INIT`), `CARRY4`,
  `MUXF7`/`MUXF8`, `INV`, `VCC`/`GND`, and the pass-throughs
  `BUF`/`BUFG`/`BUFH`/`IBUF`/`OBUF` (treated as wires — the I/O buffers and
  the clock buffer are outside the µVerilog claim, exactly as the board
  wrapper's primitives are, D15/D21);
* sequential: `FDRE`/`FDSE` (sync R/S) and `FDCE`/`FDPE` (async CLR/PRE —
  accepted only when the async pin is tied to a constant `0`, i.e. the
  design never exercises it; otherwise a hard error).

Any other cell type is a hard error naming it: the checker never silently
skips logic. **Untrusted**: this encoder is the "if the encoding is
faithful" side of the v1 claim (see `EQCHECK_SPEC.md`).
-/

namespace Loom.Netlist

open Loom.Dp.Cnf

instance : BEq Var := ⟨fun a b => decide (a = b)⟩
instance : Hashable Var where
  hash
    | .reg t n w b => mixHash (hash t) (mixHash (hash n) (mixHash (hash w) (hash b)))
    | .aux i => mixHash 7 (hash i)
instance : BEq Bit := ⟨fun a b => decide (a = b)⟩
instance : Inhabited Bit := ⟨.const false⟩

/-- Encoder state: the aux-variable counter, the accumulated clauses, and
the net→bit memo table of the cone walk. -/
structure St where
  next    : Nat := 0
  clauses : Array BClause := #[]
  memo    : Std.HashMap Nat Bit := {}
  /-- Pointer-identity memo for the µVerilog side's bit blaster: node
  address ↦ its encoded bits. Used only by `blastE`'s compiled twin
  (`Loom/Netlist/Miter.lean`); the reference definition ignores it. -/
  amemo   : Std.HashMap USize (Array Bit) := {}
deriving Inhabited

/-- The encoder monad: clause accumulation with hard errors. -/
abbrev M := ExceptT String (StateM St)

def M.run {α : Type} (m : M α) (s : St) : Except String α × St :=
  StateT.run m s

/-! ## Gates -/

def addCl (c : BClause) : M Unit :=
  modify fun s => { s with clauses := s.clauses.push c }

/-- A fresh Tseitin variable, as a positive `Bit`. -/
def fresh : M Bit := do
  let s ← get
  set { s with next := s.next + 1 }
  pure (.lit (.aux s.next) true)

/-- Assert `b`. -/
def assert (b : Bit) : M Unit := addCl [b]

def mkAnd (x y : Bit) : M Bit :=
  match x, y with
  | .const false, _ => pure (.const false)
  | _, .const false => pure (.const false)
  | .const true, b => pure b
  | a, .const true => pure a
  | a, b =>
      if a == b then pure a
      else if a == b.not then pure (.const false)
      else do
        let o ← fresh
        addCl [o.not, a]; addCl [o.not, b]; addCl [o, a.not, b.not]
        pure o

def mkOr (x y : Bit) : M Bit := do
  let r ← mkAnd x.not y.not
  pure r.not

def mkXor (x y : Bit) : M Bit :=
  match x, y with
  | .const a, .const b => pure (.const (xor a b))
  | .const a, b => pure (if a then b.not else b)
  | a, .const b => pure (if b then a.not else a)
  | a, b =>
      if a == b then pure (.const false)
      else if a == b.not then pure (.const true)
      else do
        let o ← fresh
        addCl [o.not, a, b]; addCl [o.not, a.not, b.not]
        addCl [o, a.not, b]; addCl [o, a, b.not]
        pure o

/-- `if c then t else e`. -/
def mkIte (c t e : Bit) : M Bit :=
  match c with
  | .const true => pure t
  | .const false => pure e
  | c =>
      if t == e then pure t
      else if t == (Bit.const true) && e == (Bit.const false) then pure c
      else if t == (Bit.const false) && e == (Bit.const true) then pure c.not
      else do
        let o ← fresh
        addCl [o.not, c.not, t]; addCl [o, c.not, t.not]
        addCl [o.not, c, e];     addCl [o, c, e.not]
        pure o

/-- OR-reduce a list (balanced enough: left fold; the lists are short). -/
def mkOrList : List Bit → M Bit
  | [] => pure (.const false)
  | b :: bs => do
      let r ← mkOrList bs
      mkOr b r

/-- AND-reduce a list. -/
def mkAndList : List Bit → M Bit
  | [] => pure (.const true)
  | b :: bs => do
      let r ← mkAndList bs
      mkAnd b r

/-! ## Port directions

Directions are hard-coded per cell type: with the cell-library modules
stripped from the netlist (see `EQCHECK_SPEC.md` §Deviations) yosys does
not emit `port_directions`, and hard-coding them is in any case the same
"unknown cell = hard error" discipline the semantics below follow. -/

/-- `(inputs, outputs)` of a supported cell type. -/
def cellPorts (ty : String) : Option (List String × List String) :=
  if ty == "INV" || ty == "BUF" || ty == "BUFG" || ty == "BUFH" ||
     ty == "BUFGP" || ty == "IBUF" || ty == "OBUF" || ty == "IBUFG" then
    some (["I"], ["O"])
  else if ty == "LUT1" then some (["I0"], ["O"])
  else if ty == "LUT2" then some (["I0", "I1"], ["O"])
  else if ty == "LUT3" then some (["I0", "I1", "I2"], ["O"])
  else if ty == "LUT4" then some (["I0", "I1", "I2", "I3"], ["O"])
  else if ty == "LUT5" then some (["I0", "I1", "I2", "I3", "I4"], ["O"])
  else if ty == "LUT6" then some (["I0", "I1", "I2", "I3", "I4", "I5"], ["O"])
  else if ty == "MUXF7" || ty == "MUXF8" then some (["I0", "I1", "S"], ["O"])
  else if ty == "CARRY4" then some (["CI", "CYINIT", "DI", "S"], ["CO", "O"])
  else if ty == "VCC" then some ([], ["P"])
  else if ty == "GND" then some ([], ["G"])
  else if ty == "FDRE" then some (["C", "CE", "D", "R"], ["Q"])
  else if ty == "FDSE" then some (["C", "CE", "D", "S"], ["Q"])
  else if ty == "FDCE" then some (["C", "CE", "D", "CLR"], ["Q"])
  else if ty == "FDPE" then some (["C", "CE", "D", "PRE"], ["Q"])
  else none

/-! ## Memory hard blocks

Distributed and block RAM are **cut points**, never evaluated: the checker
seeds each memory's read-data nets with free variables shared by both
sides, and checks the cones that *feed* the memory's ports instead (the
v1 boundary of `EQCHECK_SPEC.md` §Scope — array storage is carried by cell
identity). So only two things matter here: the output pin list, which the
driver map needs in order to know that a net comes out of a memory, and
the type name itself. Input pins are listed for documentation and are not
required to be present (yosys omits unused ports). An unknown cell type is
still a hard error — a memory the table does not name will be reported as
an unsupported cell, never silently skipped. -/

/-- `(inputs, outputs)` of a supported memory hard block. -/
def memCellPorts (ty : String) : Option (List String × List String) :=
  if ty == "RAM32M" || ty == "RAM64M" || ty == "RAM32M16" || ty == "RAM64M8" then
    some (["ADDRA", "ADDRB", "ADDRC", "ADDRD", "DIA", "DIB", "DIC", "DID",
           "WCLK", "WE"], ["DOA", "DOB", "DOC", "DOD"])
  else if ty == "RAM32X1D" || ty == "RAM64X1D" || ty == "RAM128X1D" then
    some (["A0", "A1", "A2", "A3", "A4", "A5", "A6", "A", "D", "DPRA0",
           "DPRA1", "DPRA2", "DPRA3", "DPRA4", "DPRA5", "DPRA6", "DPRA",
           "WCLK", "WE"], ["SPO", "DPO"])
  else if ty == "RAM32X1S" || ty == "RAM64X1S" || ty == "RAM128X1S" ||
          ty == "RAM256X1S" then
    some (["A0", "A1", "A2", "A3", "A4", "A5", "A6", "A", "D", "WCLK", "WE"],
          ["O"])
  else if ty == "RAMD32" || ty == "RAMD64E" || ty == "RAMS32" ||
          ty == "RAMS64E" then
    some (["RADR0", "RADR1", "RADR2", "RADR3", "RADR4", "RADR5",
           "WADR0", "WADR1", "WADR2", "WADR3", "WADR4", "WADR5",
           "I", "CLK", "WE"], ["O"])
  else if ty == "RAMB18E1" || ty == "RAMB36E1" then
    some (["ADDRARDADDR", "ADDRBWRADDR", "CLKARDCLK", "CLKBWRCLK",
           "DIADI", "DIBDI", "DIPADIP", "DIPBDIP", "ENARDEN", "ENBWREN",
           "REGCEAREGCE", "REGCEB", "RSTRAMARSTRAM", "RSTRAMB",
           "RSTREGARSTREG", "RSTREGB", "WEA", "WEBWE"],
          ["DOADO", "DOBDO", "DOPADOP", "DOPBDOP"])
  else none

/-- Is this cell a memory hard block (a cut point)? -/
def isMemCell (ty : String) : Bool := (memCellPorts ty).isSome

/-- Is this cell a flip-flop (state, not combinational logic)? -/
def isFF (ty : String) : Bool :=
  ty == "FDRE" || ty == "FDSE" || ty == "FDCE" || ty == "FDPE"

/-- Is this a pass-through buffer (used to trace the clock net)? -/
def isBuf (ty : String) : Bool :=
  ty == "BUF" || ty == "BUFG" || ty == "BUFH" || ty == "BUFGP" ||
  ty == "IBUF" || ty == "IBUFG" || ty == "OBUF"

/-! ## Combinational semantics -/

/-- `INIT` as a truth table indexed by `Σ_j inᵢ·2ʲ`. The parameter is a
yosys bit string, most-significant (highest index) first. -/
def initTable (ty : String) (init : String) (k : Nat) :
    Except String (Array Bool) := do
  let cs := init.toList
  if cs.any (fun c => c != '0' && c != '1') then
    .error s!"{ty}: INIT '{init}' is not a 0/1 bit string"
  let n := 2 ^ k
  if cs.length > n then
    .error s!"{ty}: INIT '{init}' has {cs.length} bits, expected at most {n}"
  let pad := List.replicate (n - cs.length) '0'
  let bits := (pad ++ cs).toArray            -- index 0 = truth-table entry n-1
  .ok (Array.ofFn (n := n) fun i => bits[n - 1 - i.val]! == '1')

/-- Shannon expansion of a `k`-input truth table over `ins` (LSB = `I0`). -/
def lutBody (tbl : Array Bool) (ins : Array Bit) : Nat → Nat → M Bit
  | 0, base => pure (.const (tbl[base]!))
  | k + 1, base => do
      let half := 2 ^ k
      let lo ← lutBody tbl ins k base
      let hi ← lutBody tbl ins k (base + half)
      mkIte (ins[k]!) hi lo

/-- The CARRY4 chain: `O[i] = S[i] ⊕ c[i]`, `CO[i] = S[i] ? c[i] : DI[i]`,
`c[0] = CI or CYINIT` (exactly one of which must be tied to a constant 0,
as the primitive requires), `c[i+1] = CO[i]`. -/
def carry4 (ci cyinit : Bit) (di s : Array Bit) :
    M (Array Bit × Array Bit) := do
  let c0 ←
    match ci, cyinit with
    | .const false, y => pure y
    | x, .const false => pure x
    | _, _ => throw "CARRY4: both CI and CYINIT are driven (not a legal instance)"
  let mut c := c0
  let mut co : Array Bit := #[]
  let mut o : Array Bit := #[]
  for i in [0:4] do
    let si := s[i]!
    o := o.push (← mkXor si c)
    let cn ← mkIte si c (di[i]!)
    co := co.push cn
    c := cn
  pure (co, o)

/-- One combinational cell: given its already-encoded input pins, the bits
of each output pin. -/
def evalCell (c : Cell) (pin : String → Array Bit) :
    M (List (String × Array Bit)) := do
  let ty := c.type
  if ty == "INV" then
    pure [("O", #[(pin "I")[0]!.not])]
  else if isBuf ty then
    pure [("O", pin "I")]
  else if ty == "VCC" then pure [("P", #[.const true])]
  else if ty == "GND" then pure [("G", #[.const false])]
  else if ty == "MUXF7" || ty == "MUXF8" then
    pure [("O", #[← mkIte ((pin "S")[0]!) ((pin "I1")[0]!) ((pin "I0")[0]!)])]
  else if ty == "CARRY4" then do
    let (co, o) ← carry4 ((pin "CI")[0]!) ((pin "CYINIT")[0]!) (pin "DI") (pin "S")
    pure [("CO", co), ("O", o)]
  else
    match cellPorts ty with
    | some (ins, _) =>
      if ty.startsWith "LUT" then do
        let k := ins.length
        let init ←
          match c.param? "INIT" with
          | some s => pure s
          | none => throw s!"{ty} '{c.name}': missing INIT parameter"
        let tbl ← liftM (initTable ty init k : Except String _)
        let args := (ins.map (fun p => (pin p)[0]!)).toArray
        pure [("O", #[← lutBody tbl args k 0])]
      else throw s!"cell type '{ty}' is not combinational"
    | none => throw s!"unsupported cell type '{ty}' (instance '{c.name}')"

/-- The next value of a flip-flop's `Q`, given its encoded pins and the
current-state bit `q`. Async `CLR`/`PRE` are accepted only tied to `0`. -/
def ffNext (c : Cell) (pin : String → Array Bit) (q : Bit) : M Bit := do
  for (k, _) in c.params do
    unless k == "INIT" do
      throw s!"{c.type} '{c.name}': unsupported parameter '{k}' \
        (inversion attributes change the transition function)"
  let d := (pin "D")[0]!
  let ce := (pin "CE")[0]!
  let held ← mkIte ce d q
  match c.type with
  | "FDRE" => mkIte ((pin "R")[0]!) (.const false) held
  | "FDSE" => mkIte ((pin "S")[0]!) (.const true) held
  | "FDCE" =>
      if (pin "CLR")[0]! == Bit.const false then pure held
      else throw s!"FDCE '{c.name}': asynchronous CLR is driven by logic — \
        outside the synchronous transition-function comparison"
  | "FDPE" =>
      if (pin "PRE")[0]! == Bit.const false then pure held
      else throw s!"FDPE '{c.name}': asynchronous PRE is driven by logic — \
        outside the synchronous transition-function comparison"
  | ty => throw s!"'{ty}' is not a flip-flop"

end Loom.Netlist
