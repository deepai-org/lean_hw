-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Hw.Declarations
import Loom.Hw.Dsl
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
open Loom.Hw.Dsl

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

/-- The architectural instruction word as a typed packed view. Declaration
order is MSB-first, matching Acc8's immediate/opcode encoding exactly. -/
packed struct Instruction where
  imm : 8
  opc : 8

private def fetched : PackedExpr Instruction :=
  .fromBits (progMem.rd rPc)
private def opc : Expr 8 := [hwexpr| fetched.opc]
private def imm : Expr 8 := [hwexpr| fetched.imm]
private def loadData : Expr 8 := dataMem.rd imm

/-- The instruction-execution rule, written with the optional pretty syntax.
The quotation lowers directly to the same `Act` constructors used previously. -/
private def execRule : Act :=
  [hwstmt|
    if rHalted then skip else
    case opc of
    | 0 => { pcReg <- rPc + 1 }
    | 1 => { accReg <- imm, pcReg <- rPc + 1 }
    | 2 => { accReg <- rAcc + imm, pcReg <- rPc + 1 }
    | 3 => { accReg <- loadData, pcReg <- rPc + 1 }
    | 4 => { dataMem[port 0, imm] <- rAcc, pcReg <- rPc + 1 }
    | 5 => {
        if rAcc == 0 then pcReg <- rPc + 1 else pcReg <- imm
      }
    | 6 => { accReg <- rAcc - imm, pcReg <- rPc + 1 }
    -- hlt (7) and every unknown opcode halt.
    | default => { haltedReg <- 1 }]

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
