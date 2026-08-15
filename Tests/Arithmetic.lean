-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Arithmetic

/-! # Explicit arithmetic facade regressions -/

namespace Tests.Arithmetic

open Loom.Hw

private def state : St where
  regs := fun _ width => BitVec.ofNat width 0
  mems := fun _ _ width => BitVec.ofNat width 0

example : (Expr.addWide (.lit 255#8) (.lit 1#8)).eval state = 256#9 := by
  decide

example : (Expr.addCarry (.lit 255#8) (.lit 1#8)).sum.eval state = 0#8 := by
  decide

example : (Expr.addCarry (.lit 255#8) (.lit 1#8)).carry.eval state = 1#1 := by
  decide

example : (Expr.saturatingAdd (.lit 250#8) (.lit 20#8)).eval state = 255#8 := by
  decide

example : (Expr.saturatingSub (.lit 3#8) (.lit 8#8)).eval state = 0#8 := by
  decide

example : (Expr.reduceOr (.lit 0#8)).eval state = 0#1 := by decide
example : (Expr.reduceOr (.lit 16#8)).eval state = 1#1 := by decide
example : (Expr.reduceAnd (.lit 255#8)).eval state = 1#1 := by decide
example : (Expr.reduceXor (.lit 0b1011#4)).eval state = 1#1 := by decide

private def unsignedOne : UnsignedExpr 8 := .ofBits (.lit 1#8)
private def signedMinusOne : SignedExpr 8 := .ofBits (.lit 255#8)

private def widened : UnsignedExpr 16 := unsignedOne.extend 16 (by omega)
private def deliberatelyNarrowed : UnsignedExpr 4 := unsignedOne.resize 4

#guard widened.bits.eval state == 1#16
#guard deliberatelyNarrowed.bits.eval state == 1#4

example : (UnsignedExpr.lt unsignedOne signedMinusOne.reinterpretUnsigned).eval state = 1#1 := by
  decide

example : (SignedExpr.lt unsignedOne.reinterpretSigned signedMinusOne).eval state = 0#1 := by
  decide

end Tests.Arithmetic
