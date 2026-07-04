-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Hw.Semantics
import Machines.Acc8.Spec

/-!
# The Acc8 core in the hardware EDSL (task 1.11, pathfinder half)

Single-rule, single-cycle-per-instruction design: registers `acc`, `pc`,
`halted`; program ROM and data RAM. Deliberately parallel in structure to
`Acc8.step` so the A-R simulation square is close to definitional.

Lockstep corroboration against the ISS lives in `Tests/Acc8Core.lean`; the
refinement theorem A-R in `Machines/Acc8/Theorems/AR.lean`.
-/

namespace Machines.Acc8.Core

open Loom.Hw

/-- Shorthands. -/
private def rAcc : Expr 8 := .reg 8 "acc"
private def rPc : Expr 8 := .reg 8 "pc"
private def rHalted : Expr 1 := .reg 1 "halted"
/-- The fetched instruction word. -/
private def fetchW : Expr 16 := .memRead 16 "prog" rPc
private def opc : Expr 8 := .slice fetchW 0 8
private def imm : Expr 8 := .slice fetchW 8 8
private def pcNext : Act := .write 8 "pc" (.add rPc (.lit 1))
private def haltNow : Act := .write 1 "halted" (.lit 1)

/-- Dispatch on an opcode value. -/
private def isOp (n : Nat) : Expr 1 := .eq opc (.lit (BitVec.ofNat 8 n))

/-- The instruction-execution rule. -/
private def execRule : Act :=
  .ite rHalted .skip <|
  -- nop (0): just advance
  .ite (isOp 0) pcNext <|
  .ite (isOp 1) (.seq (.write 8 "acc" imm) pcNext) <|
  .ite (isOp 2) (.seq (.write 8 "acc" (.add rAcc imm)) pcNext) <|
  .ite (isOp 3) (.seq (.write 8 "acc" (.memRead 8 "mem" imm)) pcNext) <|
  .ite (isOp 4) (.seq (.memWrite 8 8 "mem" 0 imm rAcc) pcNext) <|
  .ite (isOp 5) (.ite (.eq rAcc (.lit 0)) pcNext (.write 8 "pc" imm)) <|
  .ite (isOp 6) (.seq (.write 8 "acc" (.sub rAcc imm)) pcNext) <|
  -- hlt (7) and every unknown opcode halt
  haltNow

/-- The Acc8 core for a given program image. -/
def design (prog : BitVec 8 → BitVec 16) : Design where
  name := "acc8"
  regs := [⟨"acc", 8, 0⟩, ⟨"pc", 8, 0⟩, ⟨"halted", 1, 0⟩]
  mems :=
    [ { name := "prog", addrWidth := 8, dataWidth := 16
        init := fun a => prog (BitVec.ofNat 8 a) }
    , { name := "mem", addrWidth := 8, dataWidth := 8, init := fun _ => 0 } ]
  rules := [⟨"exec", execRule⟩]

/-- The abstraction function of the A-R refinement: read the architectural
state out of the named signals (the program comes from the ROM contents,
which no rule writes — so the square holds unconditionally). -/
def abs (σ : Loom.Hw.St) : Machines.Acc8.St where
  acc := σ.regs "acc" 8
  pc := σ.regs "pc" 8
  prog := fun a => σ.mems "prog" a.toNat 16
  mem := fun a => σ.mems "mem" a.toNat 8
  halted := σ.regs "halted" 1 == 1#1

end Machines.Acc8.Core
