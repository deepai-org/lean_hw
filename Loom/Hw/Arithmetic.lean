-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics

/-!
# Width- and interpretation-explicit arithmetic

These are verified-library smart constructors over the existing `Expr` core.
Unsigned and signed views are distinct Lean types: ordering and extension can
therefore never acquire signedness from context or notation.  Conversions are
explicit and erase to the same bits.
-/

namespace Loom.Hw

/-- An expression whose arithmetic interpretation is unsigned. -/
structure UnsignedExpr (width : Nat) where
  bits : Expr width

/-- An expression whose arithmetic interpretation is two's-complement signed. -/
structure SignedExpr (width : Nat) where
  bits : Expr width

namespace UnsignedExpr

variable {width : Nat}

def ofBits (value : Expr width) : UnsignedExpr width := ⟨value⟩

def reinterpretSigned (value : UnsignedExpr width) : SignedExpr width :=
  ⟨value.bits⟩

def add (left right : UnsignedExpr width) : UnsignedExpr width :=
  ⟨.add left.bits right.bits⟩

def sub (left right : UnsignedExpr width) : UnsignedExpr width :=
  ⟨.sub left.bits right.bits⟩

def mul (left right : UnsignedExpr width) : UnsignedExpr width :=
  ⟨.mul left.bits right.bits⟩

def lt (left right : UnsignedExpr width) : Expr 1 :=
  .ult left.bits right.bits

def extend (value : UnsignedExpr width) (targetWidth : Nat) :
    UnsignedExpr targetWidth :=
  ⟨.zext value.bits targetWidth⟩

end UnsignedExpr

namespace SignedExpr

variable {width : Nat}

def ofBits (value : Expr width) : SignedExpr width := ⟨value⟩

def reinterpretUnsigned (value : SignedExpr width) : UnsignedExpr width :=
  ⟨value.bits⟩

def add (left right : SignedExpr width) : SignedExpr width :=
  ⟨.add left.bits right.bits⟩

def sub (left right : SignedExpr width) : SignedExpr width :=
  ⟨.sub left.bits right.bits⟩

def mul (left right : SignedExpr width) : SignedExpr width :=
  ⟨.mul left.bits right.bits⟩

def lt (left right : SignedExpr width) : Expr 1 :=
  .slt left.bits right.bits

def extend (value : SignedExpr width) (targetWidth : Nat) :
    SignedExpr targetWidth :=
  ⟨.sext value.bits targetWidth⟩

end SignedExpr

namespace Expr

/-- Unsigned addition with one extra result bit. -/
def addWide {width : Nat} (left right : Expr width) : Expr (width + 1) :=
  .add (.zext left (width + 1)) (.zext right (width + 1))

structure AddCarry (width : Nat) where
  sum : Expr width
  carry : Expr 1

/-- Modular sum and carry-out derived from one widened addition. -/
def addCarry {width : Nat} (left right : Expr width) : AddCarry width :=
  let full := addWide left right
  ⟨.slice full 0 width, .slice full width 1⟩

structure SubBorrow (width : Nat) where
  difference : Expr width
  borrow : Expr 1

/-- Modular difference and unsigned borrow-out. -/
def subBorrow {width : Nat} (left right : Expr width) : SubBorrow width :=
  ⟨.sub left right, .ult left right⟩

/-- Unsigned saturating addition. -/
def saturatingAdd {width : Nat} (left right : Expr width) : Expr width :=
  let result := addCarry left right
  .mux result.carry (.lit (BitVec.allOnes width)) result.sum

/-- Unsigned saturating subtraction. -/
def saturatingSub {width : Nat} (left right : Expr width) : Expr width :=
  let result := subBorrow left right
  .mux result.borrow (.lit 0) result.difference

/-- OR reduction. The zero-width value reduces to false. -/
def reduceOr {width : Nat} (value : Expr width) : Expr 1 :=
  .not (.eq value (.lit 0))

/-- AND reduction. The zero-width value reduces to true. -/
def reduceAnd {width : Nat} (value : Expr width) : Expr 1 :=
  .eq value (.lit (BitVec.allOnes width))

private def xorBits {width : Nat} (value : Expr width) : List (Expr 1) :=
  (List.range width).map fun index => .slice value index 1

/-- XOR reduction, built as a balanced tree. The zero-width value reduces to
false. -/
def reduceXor {width : Nat} (value : Expr width) : Expr 1 :=
  (xorBits value).foldr .xor (.lit 0)

@[simp] theorem addWide_eval {width : Nat} (left right : Expr width)
    (state : St) :
    (addWide left right).eval state =
      (left.eval state).setWidth (width + 1) +
        (right.eval state).setWidth (width + 1) := rfl

@[simp] theorem addCarry_sum_eval {width : Nat} (left right : Expr width)
    (state : St) :
    (addCarry left right).sum.eval state =
      ((left.eval state).setWidth (width + 1) +
        (right.eval state).setWidth (width + 1)).extractLsb' 0 width := rfl

@[simp] theorem addCarry_carry_eval {width : Nat} (left right : Expr width)
    (state : St) :
    (addCarry left right).carry.eval state =
      ((left.eval state).setWidth (width + 1) +
        (right.eval state).setWidth (width + 1)).extractLsb' width 1 := rfl

@[simp] theorem subBorrow_difference_eval {width : Nat}
    (left right : Expr width) (state : St) :
    (subBorrow left right).difference.eval state =
      left.eval state - right.eval state := rfl

@[simp] theorem subBorrow_borrow_eval {width : Nat}
    (left right : Expr width) (state : St) :
    (subBorrow left right).borrow.eval state =
      if (left.eval state).ult (right.eval state) then 1#1 else 0#1 := rfl

end Expr

end Loom.Hw
