-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.Compile
import Loom.Hw.Cost

/-!
# Full-width multiplication regressions

The public constructors retain every product bit while lowering through the
existing same-width modular multiplication primitive. Cost reporting records
the operands' meaningful widths rather than charging for extension wiring.
-/

namespace Tests.WideMul

open Loom.Hw

private def zeroSt : St where
  regs := fun _ w => BitVec.ofNat w 0
  mems := fun _ _ w => BitVec.ofNat w 0

private def u8 : Expr 8 := .lit 0xFF#8
private def u4 : Expr 4 := .lit 0xF#4

/-- An 8×4 unsigned product retains all twelve result bits. -/
example : (Expr.umulWide u8 u4).eval zeroSt = 0xEF1#12 := by native_decide

/-- Signed widening uses two's-complement interpretation: -2 × 3 = -6. -/
example :
    (Expr.smulWide (.lit 0xFE#8) (.lit 3#8)).eval zeroSt = 0xFFFA#16 := by
  native_decide

/-- The smart constructor takes the already-proved ordinary compiler path. -/
example : Compile.compileExpr (Expr.umulWide u8 u4) =
    Loom.Emit.MicroVerilog.Expr.mul
      (.zext (Compile.compileExpr u8) 12)
      (.zext (Compile.compileExpr u4) 12) := rfl

private def a8 : Expr 8 := .reg 8 "a"
private def b4 : Expr 4 := .reg 4 "b"

/-- Cost reflects 8×4 meaningful multiplier bits, not a fictitious 12×12. -/
example : (Expr.umulWide a8 b4).cost = 32 := by native_decide

/-- Sign extension is likewise wiring; an 8×8 signed product costs 8×8. -/
example : (Expr.smulWide a8 (.reg 8 "signed_b")).cost = 64 := by native_decide

/-- A genuinely twelve-bit-by-twelve-bit multiply still costs 12×12. -/
example : (Expr.mul (.reg 12 "x") (.reg 12 "y")).cost = 144 := by native_decide

end Tests.WideMul
