-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Isa.Decode
import Loom.Core.Ts
import Loom.Core.Fun

/-!
# Acc8: the pathfinder machine

A deliberately tiny 8-bit accumulator machine. It exists for one reason: to
keep Loom honest about genericity (P0). Every generic toolchain layer is
exercised by Acc8 before (and as well as) LNP64-µ; any Loom feature Acc8
cannot use without LNP64-µ nouns is machine code in disguise.

The machine: Harvard architecture; 256 × 16-bit program words; 256 × 8-bit
data bytes; one accumulator; 8-bit PC. Eight instructions. Decode failure
halts (Acc8 has no fault machinery — that is machine semantics, which is
exactly why the generic kit leaves totality machine-side).

Encoding: opcode `[7:0]`, immediate/address operand `[15:8]` — a full
partition of the 16-bit word.
-/

namespace Machines.Acc8

open Loom Loom.Isa

/-- Machine state. -/
structure St where
  acc  : BitVec 8
  pc   : BitVec 8
  /-- Program memory (Harvard: instructions are not data). -/
  prog : BitVec 8 → BitVec 16
  /-- Data memory. -/
  mem  : BitVec 8 → BitVec 8
  halted : Bool

/-- Advance the program counter. -/
def St.next (σ : St) : St := { σ with pc := σ.pc + 1 }

/-- The semantics payload: operand value in, state transformer out. Each
instruction handles its own PC update. -/
abbrev Sem := BitVec 8 → St → St

/-- Acc8's encoding signature. -/
def sig : Sig where
  wordBits := 16
  opcode := { name := "op", lo := 0, width := 8 }
  fields := [{ name := "imm", lo := 8, width := 8 }]

/-- The operand field. -/
def immField : Field := { name := "imm", lo := 8, width := 8 }

/-- Shorthand for declaring an Acc8 instruction. -/
private def op (mnemonic : String) (opcode : BitVec 8) (sem : Sem)
    (summary operation : String) : InstrDecl sig Sem Unit where
  mnemonic := mnemonic
  opcode := opcode
  operands := ["imm"]
  sem := sem
  cost := ()
  prose := { summary := summary, operation := operation }

/-- The instruction set: the single source for decode, encode, ISS,
conformance, and the book. -/
def isa : Isa sig Sem Unit := #[
  op "nop" 0 (fun _ σ => σ.next)
    "No operation."
    "The machine advances to the next instruction; no other state changes.",
  op "ldi" 1 (fun v σ => { σ.next with acc := v })
    "Load immediate."
    "The accumulator is set to the immediate operand.",
  op "add" 2 (fun v σ => { σ.next with acc := σ.acc + v })
    "Add immediate."
    "The immediate operand is added to the accumulator, modulo 256.",
  op "lda" 3 (fun a σ => { σ.next with acc := σ.mem a })
    "Load from memory."
    "The accumulator is loaded from the data byte at the operand address.",
  op "sta" 4 (fun a σ => { σ.next with mem := Loom.Fun.update σ.mem a σ.acc })
    "Store to memory."
    "The accumulator is stored to the data byte at the operand address.",
  op "jnz" 5 (fun a σ => if σ.acc = 0 then σ.next else { σ with pc := a })
    "Jump if accumulator nonzero."
    "If the accumulator is nonzero, the PC is set to the operand address; \
     otherwise the machine advances to the next instruction.",
  op "sub" 6 (fun v σ => { σ.next with acc := σ.acc - v })
    "Subtract immediate."
    "The immediate operand is subtracted from the accumulator, modulo 256.",
  op "hlt" 7 (fun _ σ => { σ with halted := true })
    "Halt."
    "The machine halts; no further instruction executes."
]

/-- One machine step: fetch, decode, execute. Decode failure halts. Halted
states are fixed points. -/
def step (σ : St) : St :=
  if σ.halted then σ
  else
    let w := σ.prog σ.pc
    match decode isa w with
    | some d => d.sem (immField.get w) σ
    | none => { σ with halted := true }

/-- Boot state for a program image. -/
def boot (prog : BitVec 8 → BitVec 16) : St where
  acc := 0
  pc := 0
  prog := prog
  mem := fun _ => 0
  halted := false

/-- Acc8 as a transition system (P2): the spec of the machine, and the
abstract side of its refinement once the EDSL core exists (A-R). -/
def machine (prog : BitVec 8 → BitVec 16) : Loom.TSys :=
  Loom.TSys.ofFun St (fun σ => σ = boot prog) step

end Machines.Acc8
