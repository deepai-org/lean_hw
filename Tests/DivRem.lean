-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Compile
import Loom.Hw.DagEvalComplete
import Loom.Hw.Notation

/-!
# Total unsigned division and remainder regressions

The zero-divisor contract is part of Loom semantics and the compiler emits an
explicit guard, so downstream Verilog never decides this edge case.
-/

namespace Tests.DivRem

open Loom.Hw

private def zeroSt : St where
  regs := fun _ w => BitVec.ofNat w 0
  mems := fun _ _ w => BitVec.ofNat w 0

example : (Expr.udiv (.lit 100#8) (.lit 7#8)).eval zeroSt = 14#8 := by native_decide
example : (Expr.urem (.lit 100#8) (.lit 7#8)).eval zeroSt = 2#8 := by native_decide
example : (Expr.udiv (.lit 100#8) (.lit 0#8)).eval zeroSt = 0#8 := by native_decide
example : (Expr.urem (.lit 100#8) (.lit 0#8)).eval zeroSt = 100#8 := by native_decide

open Loom.Hw.Notation

example : (((Expr.lit 100#8 : Expr 8) / Expr.lit 7#8).eval zeroSt) = 14#8 := by
  native_decide
example : (((Expr.lit 100#8 : Expr 8) % Expr.lit 7#8).eval zeroSt) = 2#8 := by
  native_decide

/-- Division is guarded before it reaches raw µVerilog. -/
example (a b : Expr 8) : Compile.compileExpr (.udiv a b) =
    .mux (.eq (Compile.compileExpr b) (.lit 0)) (.lit 0)
      (.udiv (Compile.compileExpr a) (Compile.compileExpr b)) := rfl

/-- Remainder uses the dividend on a zero divisor. -/
example (a b : Expr 8) : Compile.compileExpr (.urem a b) =
    .mux (.eq (Compile.compileExpr b) (.lit 0)) (Compile.compileExpr a)
      (.urem (Compile.compileExpr a) (Compile.compileExpr b)) := rfl

end Tests.DivRem
