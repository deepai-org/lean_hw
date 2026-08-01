-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Netlist.Encode
import Loom.Netlist.Netlist
import Loom.Emit.MicroVerilog.Ast
import Loom.Dp.Cert.Lrat

/-!
# Miters: µVerilog expression ≟ netlist cone (D22)

Side A is the µVerilog `Module`'s one-cycle transition function, bit
blasted here (a full-precision blaster: unlike `Loom.Dp.Cnf.blast`, whose
arithmetic nodes are deliberately over-approximated for the BMC engine,
equivalence checking needs every bit of `add`/`sub`/`shl`/`shr`/`eq`/`ult`/
`slt` encoded exactly). Side B is the synthesized netlist's cone. Both are
encoded over the *same* free variables — one per register bit, per input
bit, and one for `rst` — so a miter is UNSAT exactly when the two
transition functions agree bit for bit.

Untrusted, per `EQCHECK_SPEC.md`: the claim discharged is "*if* this
encoding is faithful, the netlist and the module have the same transition
function"; the LRAT certificate makes only the UNSAT judgement itself
machine-checked (by `Loom.Dp.Cert.checkLrat`, the proved checker).
-/

namespace Loom.Netlist

open Loom.Dp.Cnf
open Loom.Emit.MicroVerilog

/-! ## Bit-blasting the µVerilog side -/

/-- Ripple-carry adder over the low `k` bit positions; returns the sum bits
and the carry out. (Structural recursion rather than a `for` loop: same
gates in the same order, but the shape `Loom/Netlist/Encode.lean` can
induct over.) -/
def addBitsGo (a b : Array Bit) (cin : Bit) : Nat → M (Array Bit × Bit)
  | 0 => Pure.pure (#[], cin)
  | k + 1 => do
      let (out, c) ← addBitsGo a b cin k
      let x := a[k]!
      let y := b[k]!
      let t ← mkXor x y
      let sum ← mkXor t c
      let ab ← mkAnd x y
      let tc ← mkAnd t c
      let c' ← mkOr ab tc
      Pure.pure (out.push sum, c')

/-- Ripple-carry adder; returns the sum bits and the carry out. -/
def addBits (a b : Array Bit) (cin : Bit) : M (Array Bit × Bit) :=
  addBitsGo a b cin a.size

/-- Unsigned `a < b` via the borrow out of `a + ~b + 1`. -/
def ultBits (a b : Array Bit) : M Bit := do
  let (_, cout) ← addBits a (b.map (·.not)) (.const true)
  pure cout.not

/-- Signed `a < b`. -/
def sltBits (a b : Array Bit) : M Bit := do
  if a.size = 0 then pure (.const false)
  else do
    let sa := a[a.size - 1]!
    let sb := b[a.size - 1]!
    let u ← ultBits a b
    let diff ← mkXor sa sb
    mkIte diff sa u

/-- The per-bit equalities of `a` and `b`, high bit first (the order the
accumulating loop this replaces produced). -/
def eqAcc (a b : Array Bit) : Nat → M (List Bit)
  | 0 => Pure.pure []
  | k + 1 => do
      let acc ← eqAcc a b k
      let t ← mkXor a[k]! b[k]!
      Pure.pure (t.not :: acc)

/-- Bitwise equality. -/
def eqBits (a b : Array Bit) : M Bit := do
  mkAndList (← eqAcc a b a.size)

/-- Rigid shift of `a` by the constant `k` (zero fill). -/
private def shiftConst (left : Bool) (a : Array Bit) (k : Nat) : Array Bit :=
  Array.ofFn (n := a.size) fun i =>
    if left then (if i.val < k then .const false else a[i.val - k]!)
    else (if i.val + k < a.size then a[i.val + k]! else .const false)

/-- Barrel shifter: `a` shifted by the value of `b` (zero fill; a shift
amount of at least the width yields zero, matching `BitVec`'s `<<<`/`>>>`). -/
def shiftBits (left : Bool) (a b : Array Bit) : M (Array Bit) := do
  let w := a.size
  -- Stages 0 … n-1 with 2^k < w; higher bits of `b` force the result to 0.
  let mut nstages := 0
  for k in [0:b.size] do
    if 2 ^ k < w then nstages := k + 1
  let mut res := a
  for k in [0:nstages] do
    let sh := shiftConst left res (2 ^ k)
    let sel := b[k]!
    let mut nxt : Array Bit := #[]
    for h : i in [0:res.size] do
      nxt := nxt.push (← mkIte sel sh[i]! res[i])
    res := nxt
  let mut ovf : List Bit := []
  for k in [nstages:b.size] do
    ovf := b[k]! :: ovf
  let o ← mkOrList ovf
  res.mapM (fun r => mkIte o (.const false) r)

/-- Bit-blast a µVerilog expression. `syms` gives the declared width of
every register and input name. -/
def blastE (syms : List (String × Nat)) : {w : Nat} → Expr w → M (Array Bit)
  | w, .lit v => pure (Array.ofFn (n := w) fun i => .const (v.getLsbD i.val))
  | w, .reg _ n => do
      match syms.find? (fun kv => kv.1 == n) with
      | none => throw s!"expression reads unknown signal '{n}'"
      | some (_, dw) =>
          if dw != w then
            throw s!"expression reads '{n}' at width {w}, declared {dw}"
          pure (Array.ofFn (n := w) fun i => stateBit n dw i.val)
  | _, .memRead _ m _ =>
      throw s!"memory read of '{m}': the checker compares the *cut* reading \
        of the text (Parse.parseCut), in which every memory read is a free \
        symbol; this node should not exist"
  | _, .and a b => do
      let x ← blastE syms a; let y ← blastE syms b
      buildM (fun i => mkAnd x[i]! y[i]!) x.size
  | _, .or a b => do
      let x ← blastE syms a; let y ← blastE syms b
      buildM (fun i => mkOr x[i]! y[i]!) x.size
  | _, .xor a b => do
      let x ← blastE syms a; let y ← blastE syms b
      buildM (fun i => mkXor x[i]! y[i]!) x.size
  | _, .not a => do
      let x ← blastE syms a
      pure (x.map (·.not))
  | _, .add a b => do
      let x ← blastE syms a; let y ← blastE syms b
      pure (← addBits x y (.const false)).1
  | _, .sub a b => do
      let x ← blastE syms a; let y ← blastE syms b
      pure (← addBits x (y.map (·.not)) (.const true)).1
  | _, .shl a b => do
      let x ← blastE syms a; let y ← blastE syms b
      shiftBits true x y
  | _, .shr a b => do
      let x ← blastE syms a; let y ← blastE syms b
      shiftBits false x y
  | _, .eq a b => do
      let x ← blastE syms a; let y ← blastE syms b
      pure #[← eqBits x y]
  | _, .ult a b => do
      let x ← blastE syms a; let y ← blastE syms b
      pure #[← ultBits x y]
  | _, .slt a b => do
      let x ← blastE syms a; let y ← blastE syms b
      pure #[← sltBits x y]
  | _, .mux c t f => do
      let cb ← blastE syms c
      let x ← blastE syms t; let y ← blastE syms f
      buildM (fun i => mkIte cb[0]! x[i]! y[i]!) x.size
  | _, .slice a lo width => do
      let x ← blastE syms a
      pure (Array.ofFn (n := width) fun i => x[lo + i.val]?.getD (.const false))
  | _, .zext a w' => do
      let x ← blastE syms a
      pure (Array.ofFn (n := w') fun i => x[i.val]?.getD (.const false))
  | _, @Expr.sext wa a w' => do
      let x ← blastE syms a
      pure (Array.ofFn (n := w') fun i =>
        if i.val < wa then x[i.val]?.getD (.const false)
        else x[wa - 1]?.getD (.const false))

/-! ### Sharing-preserving blasting (compiled twin)

`blastE` walks the expression as a *tree*. The parsed module's expressions
are DAGs — `Parse` rebuilds the printer's SSA wires by environment lookup,
so a wire referenced *k* times is the *same* node *k* times — and blasting
it as a tree re-encodes each occurrence, which is what made `s13soak`'s
`err` register cost 6 M clauses (EQCHECK_SPEC.md §Deviations) and what
makes `lnp64mini_soc` infeasible. The twin below gives each
pointer-distinct node one encoding and reuses its bits on every further
occurrence; it computes exactly what the reference definition computes
(a memo hit means the *same* term, and the encoding of a term is a pure
function of the term and the clause state before it), and only compiled
evaluation uses it. Same trust shape as `Print.printImpl`; nothing
kernel-facing depends on either. -/

mutual

private unsafe def blastEGo (syms : List (String × Nat)) :
    {w : Nat} → Expr w → M (Array Bit)
  | w, .lit v => pure (Array.ofFn (n := w) fun i => .const (v.getLsbD i.val))
  | w, .reg _ n => do
      match syms.find? (fun kv => kv.1 == n) with
      | none => throw s!"expression reads unknown signal '{n}'"
      | some (_, dw) =>
          if dw != w then
            throw s!"expression reads '{n}' at width {w}, declared {dw}"
          pure (Array.ofFn (n := w) fun i => stateBit n dw i.val)
  | _, .memRead _ m _ =>
      throw s!"memory read of '{m}': the checker compares the *cut* reading \
        of the text (Parse.parseCut), in which every memory read is a free \
        symbol; this node should not exist"
  | _, .and a b => do
      let x ← blastEM syms a; let y ← blastEM syms b
      buildM (fun i => mkAnd x[i]! y[i]!) x.size
  | _, .or a b => do
      let x ← blastEM syms a; let y ← blastEM syms b
      buildM (fun i => mkOr x[i]! y[i]!) x.size
  | _, .xor a b => do
      let x ← blastEM syms a; let y ← blastEM syms b
      buildM (fun i => mkXor x[i]! y[i]!) x.size
  | _, .not a => do
      let x ← blastEM syms a
      pure (x.map (·.not))
  | _, .add a b => do
      let x ← blastEM syms a; let y ← blastEM syms b
      pure (← addBits x y (.const false)).1
  | _, .sub a b => do
      let x ← blastEM syms a; let y ← blastEM syms b
      pure (← addBits x (y.map (·.not)) (.const true)).1
  | _, .shl a b => do
      let x ← blastEM syms a; let y ← blastEM syms b
      shiftBits true x y
  | _, .shr a b => do
      let x ← blastEM syms a; let y ← blastEM syms b
      shiftBits false x y
  | _, .eq a b => do
      let x ← blastEM syms a; let y ← blastEM syms b
      pure #[← eqBits x y]
  | _, .ult a b => do
      let x ← blastEM syms a; let y ← blastEM syms b
      pure #[← ultBits x y]
  | _, .slt a b => do
      let x ← blastEM syms a; let y ← blastEM syms b
      pure #[← sltBits x y]
  | _, .mux c t f => do
      let cb ← blastEM syms c
      let x ← blastEM syms t; let y ← blastEM syms f
      buildM (fun i => mkIte cb[0]! x[i]! y[i]!) x.size
  | _, .slice a lo width => do
      let x ← blastEM syms a
      pure (Array.ofFn (n := width) fun i => x[lo + i.val]?.getD (.const false))
  | _, .zext a w' => do
      let x ← blastEM syms a
      pure (Array.ofFn (n := w') fun i => x[i.val]?.getD (.const false))
  | _, @Expr.sext wa a w' => do
      let x ← blastEM syms a
      pure (Array.ofFn (n := w') fun i =>
        if i.val < wa then x[i.val]?.getD (.const false)
        else x[wa - 1]?.getD (.const false))

private unsafe def blastEM (syms : List (String × Nat)) {w : Nat}
    (e : Expr w) : M (Array Bit) := do
  let k := ptrAddrUnsafe e
  if let some bs := (← get).amemo[k]? then
    return bs
  let bs ← blastEGo syms e
  modify fun s => { s with amemo := s.amemo.insert k bs }
  return bs

end

attribute [implemented_by blastEM] blastE

/-! ## Miters -/

/-- The per-bit differences of `a` and `b`, high bit first. -/
def differAcc (a b : Array Bit) : Nat → M (List Bit)
  | 0 => Pure.pure []
  | k + 1 => do
      let xs ← differAcc a b k
      let t ← mkXor a[k]! b[k]!
      Pure.pure (t :: xs)

/-- Assert that the two bit vectors differ (the miter output). -/
def assertDiffer (a b : Array Bit) : M Unit := do
  if a.size != b.size then
    throw s!"width mismatch in miter: {a.size} vs {b.size}"
  assert (← mkOrList (← differAcc a b a.size))

/-- The netlist-side next value of one register bit. -/
def netlistNext (env : NetlistEnv) (mt : Matching) (fuel : Nat)
    (name : String) (w i : Nat) (src : RegSrc) : M Bit := do
  match src with
  | .folded b => pure (.const b)
  | .mem cn ty =>
      throw s!"MEMCUT: register '{name}[{i}]' is driven by {ty} '{cn}' — the \
        read register was absorbed into the memory's read port"
  | .ff n =>
      match mt.ffOf[n]? with
      | none => throw s!"internal: no flip-flop for net {n}"
      | some c => do
          -- The clock pin must actually carry the clock.
          match ((c.conn? "C").bind (fun a => a[0]?) : Option SigBit) with
          | some (.net cn) =>
              unless env.clk.contains cn do
                throw s!"{c.type} '{c.name}': pin C (net {cn}) is not the clock"
          | _ => throw s!"{c.type} '{c.name}': pin C is not connected to a net"
          let some (ins, _) := cellPorts c.type
            | throw s!"unsupported flip-flop type '{c.type}'"
          let mut pins : List (String × Array Bit) := []
          for p in ins do
            if p == "C" then pure ()
            else
              let bits ← evalBits env fuel ((c.conn? p).getD #[])
              pins := (p, bits) :: pins
          let pin := fun p => ((pins.find? (fun kv => kv.1 == p)).map (·.2)).getD #[]
          ffNext c pin (stateBit name w i)

/-- One register's miter: `rst ? init : next` (module) vs the flip-flops'
next state (netlist), under the constant-folding assumptions. -/
def regMiter (env : NetlistEnv) (mt : Matching) (fuel : Nat)
    (syms : List (String × Nat)) (rd : RegDef) (srcs : Array RegSrc) :
    M Unit := do
  for a in mt.assumptions do assert a
  let nextBits ← blastE syms rd.next
  let mut sideA : Array Bit := #[]
  for h : i in [0:rd.width] do
    sideA := sideA.push (← mkIte rstBit (.const (rd.init.getLsbD i)) nextBits[i]!)
  let mut sideB : Array Bit := #[]
  for h : i in [0:srcs.size] do
    sideB := sideB.push (← netlistNext env mt fuel rd.name rd.width i srcs[i])
  assertDiffer sideA sideB

/-- One combinational cone's miter: a µVerilog expression against the
netlist's cone at a named signal. Output ports use it with the port's
bits; a memory port's enable/address/data cone uses it with the bits of
the netlist net that still carries the printed wire's name. -/
def coneMiter (env : NetlistEnv) (mt : Matching) (fuel : Nat)
    (syms : List (String × Nat)) {w : Nat} (e : Expr w)
    (bits : Array SigBit) : M Unit := do
  for a in mt.assumptions do assert a
  let sideA ← blastE syms e
  let sideB ← evalBits env fuel bits
  assertDiffer sideA sideB

/-- One output port's miter: the module's combinational view vs the
netlist's cone for that port. -/
def outMiter (env : NetlistEnv) (mt : Matching) (fuel : Nat)
    (syms : List (String × Nat)) (od : OutDef) (bits : Array SigBit) :
    M Unit :=
  coneMiter env mt fuel syms od.val bits

/-! ## DIMACS export and countermodel decoding -/

/-- A CNF ready for the solver: DIMACS text (variables `1 … n`), the same
formula as `Std.Sat.CNF Nat` for the proved LRAT checker (DIMACS variable
`d` enters as `d-1`, as `Loom.Dp.Cert.checkLrat` expects), and the
variable table for decoding countermodels. -/
structure Dimacs where
  text     : String
  cnf      : Loom.Dp.Cert.Cnf
  vars     : Array Var
  nClauses : Nat
  /-- The clause list contains the empty clause: the miter output folded to
  constant false, i.e. the encoder made both sides *the same* formula and no
  search is needed. -/
  trivial  : Bool

/-- Normalize and number the clauses. Clauses containing a constant-true
literal are dropped; constant-false literals are removed. -/
def toDimacs (clauses : Array BClause) : Dimacs := Id.run do
  let mut idx : Std.HashMap Var Nat := {}
  let mut vars : Array Var := #[]
  let mut lines : Array String := #[]
  let mut cnf : Array (List (Nat × Bool)) := #[]
  for cl in clauses do
    let mut lits : Array (Nat × Bool) := #[]
    let mut sat := false
    for b in cl do
      match b with
      | .const true => sat := true
      | .const false => pure ()
      | .lit v pol =>
          let id ←
            match idx[v]? with
            | some i => pure i
            | none => do
                vars := vars.push v
                idx := idx.insert v vars.size
                pure vars.size
          -- Normalize: drop repeated literals, drop tautological clauses.
          -- (Both are legal DIMACS but confuse the LRAT clause-id alignment,
          -- since solvers may discard a tautology at parse time.)
          if lits.contains (id, !pol) then sat := true
          else unless lits.contains (id, pol) do lits := lits.push (id, pol)
    unless sat do
      let mut s := ""
      for (id, pol) in lits do
        s := s ++ (if pol then "" else "-") ++ toString id ++ " "
      lines := lines.push (s ++ "0")
      cnf := cnf.push (lits.toList.map (fun (id, pol) => (id - 1, pol)))
  let header := s!"p cnf {vars.size} {lines.size}"
  let text := String.intercalate "\n" (header :: lines.toList) ++ "\n"
  return { text := text, cnf := cnf.toList, vars := vars, nClauses := lines.size,
           trivial := cnf.any (fun c => c.isEmpty) }

/-- Decode a DIMACS model (list of signed literals) into the assignment of
the *named* variables — register/input bits and `rst`. -/
def decodeModel (d : Dimacs) (model : List Int) : List (String × Nat × Bool) :=
  model.filterMap fun (l : Int) =>
    let v := Int.natAbs l
    if v == 0 || v > d.vars.size then none
    else match d.vars[v - 1]? with
      | some (Var.reg _ n _ b) => some (n, b, l > 0)
      | _ => none

end Loom.Netlist
