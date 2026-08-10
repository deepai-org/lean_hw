-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Hw.Declarations
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

/-- Architectural register handles. Each name and width is declared here. -/
abbrev accReg : Reg 8 := ⟨"acc"⟩
abbrev pcReg : Reg 8 := ⟨"pc"⟩
abbrev haltedReg : Reg 1 := ⟨"halted"⟩

/-- Program ROM and data RAM handles. -/
abbrev progMem : Mem 8 16 := ⟨"prog"⟩
abbrev dataMem : Mem 8 8 := ⟨"mem"⟩

/-- Expression shorthands. -/
private def rAcc : Expr 8 := accReg.rd
private def rPc : Expr 8 := pcReg.rd
private def rHalted : Expr 1 := haltedReg.rd
/-- The fetched instruction word. -/
private def fetchW : Expr 16 := progMem.rd rPc
private def opc : Expr 8 := .slice fetchW 0 8
private def imm : Expr 8 := .slice fetchW 8 8
private def pcNext : Act := pcReg.set (.add rPc (.lit 1))
private def haltNow : Act := haltedReg.set (.lit 1)

/-- Dispatch on an opcode value. -/
private def isOp (n : Nat) : Expr 1 := .eq opc (.lit (BitVec.ofNat 8 n))

/-- The instruction-execution rule. -/
private def execRule : Act :=
  .ite rHalted .skip <|
  -- nop (0): just advance
  .ite (isOp 0) pcNext <|
  .ite (isOp 1) (.seq (accReg.set imm) pcNext) <|
  .ite (isOp 2) (.seq (accReg.set (.add rAcc imm)) pcNext) <|
  .ite (isOp 3) (.seq (accReg.set (dataMem.rd imm)) pcNext) <|
  .ite (isOp 4) (.seq (dataMem.write 0 imm rAcc) pcNext) <|
  .ite (isOp 5) (.ite (.eq rAcc (.lit 0)) pcNext (pcReg.set imm)) <|
  .ite (isOp 6) (.seq (accReg.set (.sub rAcc imm)) pcNext) <|
  -- hlt (7) and every unknown opcode halt
  haltNow

/-- Acc8 state, interface, and memory initialization from typed handles. -/
abbrev declarations (prog : BitVec 8 → BitVec 16) : Declarations :=
  Declarations.empty
    |>.addReg accReg (exported := true)
    |>.addReg pcReg (exported := true)
    |>.addReg haltedReg (exported := true)
    |>.addMem progMem (fun a => prog (BitVec.ofNat 8 a))
    |>.addMem dataMem

/-- The Acc8 core for a given program image. -/
def design (prog : BitVec 8 → BitVec 16) : Design :=
  Design.ofDecls "acc8" (declarations prog) [⟨"exec", execRule⟩]

/-- The abstraction function of the A-R refinement: read the architectural
state out of the named signals (the program comes from the ROM contents,
which no rule writes — so the square holds unconditionally). -/
def abs (σ : Loom.Hw.St) : Machines.Acc8.St where
  acc := σ.regs accReg.name 8
  pc := σ.regs pcReg.name 8
  prog := fun a => σ.mems progMem.name a.toNat 16
  mem := fun a => σ.mems dataMem.name a.toNat 8
  halted := σ.regs haltedReg.name 1 == 1#1

end Machines.Acc8.Core
