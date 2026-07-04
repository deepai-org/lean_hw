-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Acc8.Spec
import Loom.Isa.Dsl

/-!
# DSL regression (task 0.17)

The Acc8 ISA re-declared through the surface syntax, proved *definitionally
equal* to the structure-level `isa` — the macro layer is sugar with zero
semantic content, so projections and proofs cannot depend on which surface
was used.
-/

namespace Machines.Acc8.DslRegression

open Loom.Isa Loom.Isa.Dsl Machines.Acc8

def dslIsa : Isa sig Sem Unit := #[
  instr "nop" opcode 0 operands ["imm"] cost ()
    sem (fun _ σ => σ.next)
    summary "No operation."
    operation "The machine advances to the next instruction; no other state changes."
  end_instr,
  instr "ldi" opcode 1 operands ["imm"] cost ()
    sem (fun v σ => { σ.next with acc := v })
    summary "Load immediate."
    operation "The accumulator is set to the immediate operand."
  end_instr,
  instr "add" opcode 2 operands ["imm"] cost ()
    sem (fun v σ => { σ.next with acc := σ.acc + v })
    summary "Add immediate."
    operation "The immediate operand is added to the accumulator, modulo 256."
  end_instr,
  instr "lda" opcode 3 operands ["imm"] cost ()
    sem (fun a σ => { σ.next with acc := σ.mem a })
    summary "Load from memory."
    operation "The accumulator is loaded from the data byte at the operand address."
  end_instr,
  instr "sta" opcode 4 operands ["imm"] cost ()
    sem (fun a σ => { σ.next with mem := Loom.Fun.update σ.mem a σ.acc })
    summary "Store to memory."
    operation "The accumulator is stored to the data byte at the operand address."
  end_instr,
  instr "jnz" opcode 5 operands ["imm"] cost ()
    sem (fun a σ => if σ.acc = 0 then σ.next else { σ with pc := a })
    summary "Jump if accumulator nonzero."
    operation "If the accumulator is nonzero, the PC is set to the operand address; \
     otherwise the machine advances to the next instruction."
  end_instr,
  instr "sub" opcode 6 operands ["imm"] cost ()
    sem (fun v σ => { σ.next with acc := σ.acc - v })
    summary "Subtract immediate."
    operation "The immediate operand is subtracted from the accumulator, modulo 256."
  end_instr,
  instr "hlt" opcode 7 operands ["imm"] cost ()
    sem (fun _ σ => { σ with halted := true })
    summary "Halt."
    operation "The machine halts; no further instruction executes."
  end_instr
]

/-- The regression oracle: the surface syntax elaborates to the very same
terms. -/
theorem dsl_defeq : dslIsa = isa := rfl

end Machines.Acc8.DslRegression
