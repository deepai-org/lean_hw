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

/-- The architectural instruction word as a typed packed view. Declaration
order is MSB-first, matching Acc8's immediate/opcode encoding exactly. -/
packed struct Instruction where
  imm : 8
  opc : 8

/-! The complete authoring surface lives in a nested namespace because Acc8's
program image is a Lean parameter applied after lowering. The generated
declarations own the handles, opcode labels, memory shapes, and rule; the
outer `design` substitutes only the parameterized ROM initializer. -/
namespace Authored

private def byteWidth : Nat := 4 + 4
private def flagWidth : Nat := 1
private def instructionWidth : Nat := byteWidth * 2

hardware acc8_authored where
  output reg acc : byteWidth
  output reg pc : byteWidth
  output reg halted : flagWidth
  memory prog : instructionWidth [256]
  memory mem : byteWidth [256]

  const NOP : byteWidth := 0
  const LDI : byteWidth := 1
  const ADD : byteWidth := 2
  const LDA : byteWidth := 3
  const STA : byteWidth := 4
  const JNZ : byteWidth := 5
  const SUB : byteWidth := 6

  rule exec := {
    let fetched := Instruction.fromBits(prog[pc]),
    let opc := fetched.opc,
    let imm := fetched.imm,
    let loadData := mem[imm],
    if halted then skip else
    case opc of
    | NOP => pc <- pc + 1
    | LDI => { acc <- imm, pc <- pc + 1 }
    | ADD => { acc <- acc + imm, pc <- pc + 1 }
    | LDA => { acc <- loadData, pc <- pc + 1 }
    | STA => { mem[port 0, imm] <- acc, pc <- pc + 1 }
    | JNZ => {
        if acc == 0 then pc <- pc + 1 else pc <- imm
      }
    | SUB => { acc <- acc - imm, pc <- pc + 1 }
    -- HLT (7) and every unknown opcode halt.
    | default => halted <- 1
  }

end Authored

/-- Compatibility names used by the existing refinement development. The
generated handles are the sole authoring source. -/
abbrev accReg : Reg 8 := Authored.acc
abbrev pcReg : Reg 8 := Authored.pc
abbrev haltedReg : Reg 1 := Authored.halted
abbrev progMem : Mem 8 16 := Authored.prog
abbrev dataMem : Mem 8 8 := Authored.mem

private abbrev execRule : Act := Authored.exec

/-- Acc8 state, interface, and memory initialization from typed handles. -/
abbrev declarations (prog : BitVec 8 → BitVec 16) : Declarations :=
  { Authored.declarations with
    mems := [progMem.decl (fun a => prog (BitVec.ofNat 8 a)), dataMem.decl] }

/-- The Acc8 core for a given program image. -/
def design (prog : BitVec 8 → BitVec 16) : Design :=
  Design.ofDecls "acc8" (declarations prog) [⟨"exec", execRule⟩]

/-- Acc8's executable logic is wholly authored by `hardware`; specializing a
program changes only the ROM initializer and public module name.  This exact
equality is the completeness boundary for the pretty conversion—there is no
parallel hand-written action or declaration list. -/
theorem design_eq_pretty (prog : BitVec 8 → BitVec 16) :
    design prog =
      { Authored.design with
        name := "acc8"
        mems := [progMem.decl (fun a => prog (BitVec.ofNat 8 a)), dataMem.decl] } :=
  rfl

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
