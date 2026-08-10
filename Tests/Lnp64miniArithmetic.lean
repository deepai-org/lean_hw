-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64mini.Core
import Loom.Hw.Compile

/-!
# LNP64mini primitive arithmetic regressions

These checks pin the production use of Loom's multiplication and concatenation
operators. Ordinary `MUL` is a direct combinational expression; `MULH` and
`MULHU` deliberately retain the multicycle shift-add state machine.
-/

namespace Tests.Lnp64miniArithmetic

open Loom.Hw
open Machines.Lnp64mini

private def zeroRegs : RegEnv := fun _ w => BitVec.ofNat w 0
private def zeroMems : MemEnv := fun _ _ w => BitVec.ofNat w 0

private def arithmeticState : St where
  regs := (zeroRegs.set aReg.name (13#64)).set bReg.name (20#64)
  mems := zeroMems

private def mulDispatchState : St where
  regs := zeroRegs.set irReg.name
    (BitVec.ofNat 64 (OP_MUL <<< 56))
  mems := zeroMems

private def concatState : St where
  regs := zeroRegs.set curReg.name (21#5)
  mems := zeroMems

/-- The machine's named low-half datapath has fixed-width modular semantics. -/
example : mulE.eval arithmeticState = 260#64 := by native_decide

/-- LNP64mini's ordinary `MUL` is lowered as a real µVerilog multiply node. -/
example : Compile.compileExpr mulE =
    Loom.Emit.MicroVerilog.Expr.mul
      (.reg 64 aReg.name) (.reg 64 bReg.name) := rfl

/-- `MUL` participates in the direct ALU dispatch rather than entering S_MUL. -/
example : is_alu.eval mulDispatchState = 1#1 := by native_decide

/-- Register-file coordinates use the typed 5+5 concatenation constructor. -/
example : (cat55 (L5 26) (L5 11)).eval concatState = 0x34B#10 := by
  native_decide

/-- Gate-stack addresses use the typed 5+2 concatenation constructor. -/
example : (gcIdx (.lit (BitVec.ofNat 3 3))).eval concatState = 87#7 := by
  native_decide

end Tests.Lnp64miniArithmetic
