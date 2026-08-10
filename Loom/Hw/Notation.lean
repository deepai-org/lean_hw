-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Trees

/-!
# EDSL ergonomics: typed signal handles and Verilog-shaped notation

The code review of `Machines/Lnp64mini/Core.lean` found the same three
papercuts everywhere:

1. a register is named by a *string* in six places (declaration, read
   shorthand, every write, the ISS mirror, the emitted name, the readback),
   so a typo is a silent behaviour change rather than a type error;
2. an indexed register family (`tpc0`…`tpc31`) repeats a name-derivation
   `s!"tpc{i}"` at every one of those sites;
3. rule bodies are deeply-nested constructor applications
   (`.seq (.ite … (.write 64 "pc" (.add …)) .skip) …`) that read nothing
   like the hardware they describe.

This module fixes all three without any elaborator magic — a structure, a
few `scoped instance`s, and ordinary `notation`/`macro`.

## Handles

`Reg w` is a width-typed name; `RegArray w n` is a width-typed family whose
member names are derived once; `Mem aw dw` carries both address and data
widths:

```lean
def cnt  : Reg 28 := ⟨"cnt"⟩
def bank : RegArray 16 8 := ⟨"bank"⟩
def ram  : Mem 10 32 := ⟨"ram"⟩

#check cnt.rd            -- Expr 28
#check cnt ⇐ cnt.rd + 1  -- Act
#check bank.decls        -- List RegDecl  (bank0 … bank7)
#check ram.rd addr       -- Expr 32, requiring addr : Expr 10
```

A register or memory width mismatch (writing a 16-bit value into a 28-bit
register, using the wrong address width for `ram`) is a *type* error, and each
name string exists in exactly one place. `RegArray` additionally makes a
statically indexed out-of-bounds access a type error.

## Notation

Everything is `scoped` in `Loom.Hw.Notation`, so importing this file changes
nothing until a design says `open Loom.Hw.Notation`.  Existing machines are
completely unaffected.

| notation | meaning |
| --- | --- |
| `1`, `0xA` | `Expr.lit` at the expected width (`OfNat`) |
| `a + b`, `a - b` | `Expr.add`, `Expr.sub` |
| `a &&& b`, `a ||| b`, `a ^^^ b`, `~~~a` | bitwise |
| `a <<< b`, `a >>> b` | shifts |
| `a === b` | `Expr.eq` (width-1 result) |
| `a <ᵤ b`, `a <ₛ b` | unsigned / signed compare |
| `c ?? t ::: f` | `Expr.mux` |
| `r ⇐ e` | `Reg.set` |
| `a ;; b` | `Act.seq` |
| `when c then a` | `Act.when` |
| `ifA c then a else b` | `Act.ite` |
| `act! { a, b, c }` | `actSeq [a, b, c]` |
-/

namespace Loom.Hw

/-! ## Typed register handles -/

/-- A width-typed register handle: the *only* place its name is written. -/
structure Reg (w : Nat) where
  name : String
  deriving Repr, DecidableEq, Inhabited

namespace Reg

/-- Read the register (coerces to `Expr w`). -/
def rd {w : Nat} (r : Reg w) : Expr w := .reg w r.name

/-- Write the register. -/
def set {w : Nat} (r : Reg w) (e : Expr w) : Act := .write w r.name e

/-- The declaration (reset value defaults to zero). -/
@[simp] def decl {w : Nat} (r : Reg w) (init : BitVec w := 0) : RegDecl :=
  ⟨r.name, w, init⟩

/-- As an input-port declaration (D15). -/
def input {w : Nat} (r : Reg w) : InputDecl := ⟨r.name, w⟩

instance {w : Nat} : CoeHead (Reg w) (Expr w) := ⟨rd⟩

end Reg

/-- A width-typed, `Fin`-indexed register family.  One declaration replaces
the six name-derivation sites the review flagged. -/
structure RegArray (w n : Nat) where
  base : String
  deriving Repr, DecidableEq, Inhabited

namespace RegArray

variable {w n : Nat}

/-- Member `i` as a handle. -/
def reg (ra : RegArray w n) (i : Fin n) : Reg w := ⟨ra.base ++ toString i.val⟩

/-- Member `i` by raw index (for builders that range over `List.range n`). -/
def regN (ra : RegArray w n) (i : Nat) : Reg w := ⟨ra.base ++ toString i⟩

def rd (ra : RegArray w n) (i : Fin n) : Expr w := (ra.reg i).rd

def set (ra : RegArray w n) (i : Fin n) (e : Expr w) : Act := (ra.reg i).set e

/-- Every member handle, in index order. -/
def handles (ra : RegArray w n) : List (Reg w) := (List.finRange n).map ra.reg

/-- All declarations, in index order. -/
def decls (ra : RegArray w n) (init : Fin n → BitVec w := fun _ => 0) :
    List RegDecl :=
  (List.finRange n).map (fun i => (ra.reg i).decl (init i))

/-- Balanced dynamic read `ra[idx]` (`dflt` when `idx` is out of range). -/
def dynRd {iw : Nat} (ra : RegArray w n) (idx : Expr iw) (dflt : Expr w) :
    Expr w :=
  dynRead n idx (fun i => (ra.regN i).rd) dflt

/-- Dynamic write `ra[idx] <= v` (guarded per member; guards are mutually
exclusive so at most one fires). -/
def dynSet {iw : Nat} (ra : RegArray w n) (idx : Expr iw) (v : Expr w) : Act :=
  dynWrite n idx (fun i => (ra.regN i).name) (fun _ => v)

/-- OR-reduce a per-member predicate over the family, balanced. -/
def any (ra : RegArray w n) (p : Reg w → Expr 1) : Expr 1 :=
  orTree (ra.handles.map p)

/-- ADD-reduce a per-member value over the family, balanced. -/
def sum {v : Nat} (ra : RegArray w n) (f : Reg w → Expr v) : Expr v :=
  addTree (ra.handles.map f)

end RegArray

/-! ## Typed memory handles -/

/-- A memory handle whose address and data widths are carried by its type.

The handle is an additive authoring layer: it elaborates directly to the
existing `MemDecl`, `Expr.memRead`, and `Act.memWrite` representation. -/
structure Mem (aw dw : Nat) where
  name : String
  deriving Repr, DecidableEq, Inhabited

namespace Mem

/-- Declare the memory. Contents default to zero. -/
def decl {aw dw : Nat} (m : Mem aw dw)
    (init : Nat → BitVec dw := fun _ => 0) : MemDecl where
  name := m.name
  addrWidth := aw
  dataWidth := dw
  init := init

/-- Read at a width-checked address. -/
def rd {aw dw : Nat} (m : Mem aw dw) (addr : Expr aw) : Expr dw :=
  .memRead dw m.name addr

/-- Write through an explicit physical write-port index. -/
def write {aw dw : Nat} (m : Mem aw dw) (port : Nat)
    (addr : Expr aw) (data : Expr dw) : Act :=
  .memWrite aw dw m.name port addr data

end Mem

/-! ## Guarded actions -/

/-- `if c then a` (no else). -/
def Act.when (c : Expr 1) (a : Act) : Act := .ite c a .skip

/-- `if ¬c then a`. -/
def Act.unless (c : Expr 1) (a : Act) : Act := .ite c .skip a

/-! ## The notation, all `scoped` -/

namespace Notation

/-- Numeric literals elaborate to `Expr.lit` at the expected width. -/
scoped instance instOfNatExpr {w n : Nat} : OfNat (Expr w) n :=
  ⟨.lit (BitVec.ofNat w n)⟩

scoped instance {w : Nat} : Add (Expr w) := ⟨Expr.add⟩
scoped instance {w : Nat} : Sub (Expr w) := ⟨Expr.sub⟩
scoped instance {w : Nat} : AndOp (Expr w) := ⟨Expr.and⟩
scoped instance {w : Nat} : OrOp (Expr w) := ⟨Expr.or⟩
scoped instance {w : Nat} : XorOp (Expr w) := ⟨Expr.xor⟩
scoped instance {w : Nat} : Complement (Expr w) := ⟨Expr.not⟩
scoped instance {w : Nat} : ShiftLeft (Expr w) := ⟨Expr.shl⟩
scoped instance {w : Nat} : ShiftRight (Expr w) := ⟨Expr.shr⟩

/-- Equality test (width-1 result). -/
scoped infix:50 " === " => Expr.eq
/-- Unsigned less-than. -/
scoped infix:50 " <ᵤ " => Expr.ult
/-- Signed less-than. -/
scoped infix:50 " <ₛ " => Expr.slt
/-- `c ?? t ::: f` — the multiplexer. -/
scoped notation:20 c " ?? " t " ::: " f => Expr.mux c t f

/-- Register assignment. -/
scoped infix:20 " ⇐ " => Reg.set
/-- Action sequencing (right-nested, last write wins — D9). -/
scoped infixr:15 " ;; " => Act.seq

scoped macro:20 "when " c:term " then " a:term : term => `(Loom.Hw.Act.when $c $a)
scoped macro:20 "unless " c:term " then " a:term : term =>
  `(Loom.Hw.Act.unless $c $a)
scoped macro:20 "ifA " c:term " then " t:term " else " e:term : term =>
  `(Loom.Hw.Act.ite $c $t $e)

/-- A Verilog-shaped statement block: `act! { s1, s2, s3 }`. -/
scoped macro "act!" "{" ts:term,* "}" : term => `(Loom.Hw.actSeq [$ts,*])

/-- A rule from a name and a body. -/
scoped macro "rule!" n:term " => " a:term : term => `(Loom.Hw.Rule.mk $n $a)

end Notation

end Loom.Hw
