-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Isa.Sig

/-!
# Instruction declarations (L0 framework, P1)

`InstrDecl` is the one-term-per-instruction structure every projection reads:
decoder, assembler, ISS glue, conformance suite, and book all consume
`Isa sig Sem Cost = Array (InstrDecl sig Sem Cost)`, never syntax trees. The
macro DSL (written last) is sugar elaborating to these terms.

Genericity contract (P0): `Sem` (operational semantics) and `Cost` (timing
class) are *opaque payloads* supplied by the machine. Loom handles syntax,
encoding, prose, and projections; the machine's step function interprets
`sem`, and its timing theorems interpret `cost`.
-/

namespace Loom.Isa

/-- The prose attached to an instruction: the book's raw material, structured
rather than stringly so the L6 engine never parses text. Every field is
written as publishable prose from day one. -/
structure ProseBlock where
  /-- One-line summary (the book's table entry). -/
  summary : String
  /-- The operation section: what the instruction does, in prose that
  parallels `sem`. -/
  operation : String := ""
  /-- Additional notes (encodings of packed operands, ABI remarks, …). -/
  notes : List String := []
deriving Repr

/-- One instruction declaration. -/
structure InstrDecl (sig : Sig) (Sem Cost : Type) where
  mnemonic : String
  /-- The opcode value; decode dispatches on this. -/
  opcode : BitVec sig.opcode.width
  /-- Names of the operand fields this instruction uses (⊆ `sig.fields`;
  the audit checks referential integrity, the assembler and book read it). -/
  operands : List String := []
  /-- The machine's operational semantics payload (opaque to Loom). -/
  sem : Sem
  /-- The machine's timing-class payload (opaque to Loom). -/
  cost : Cost
  prose : ProseBlock

/-- A machine's instruction set: the single source every projection reads. -/
abbrev Isa (sig : Sig) (Sem Cost : Type) := Array (InstrDecl sig Sem Cost)

/-- Opcodes are pairwise distinct — the determinism half of the T1 kit.
Decidable at any concrete ISA. -/
def Isa.OpcodesDistinct {sig : Sig} {Sem Cost : Type} (isa : Isa sig Sem Cost) : Prop :=
  ∀ i j : Fin isa.size, isa[i].opcode = isa[j].opcode → i = j

instance {sig : Sig} {Sem Cost : Type} (isa : Isa sig Sem Cost) :
    Decidable isa.OpcodesDistinct :=
  inferInstanceAs (Decidable (∀ _, _))

end Loom.Isa
