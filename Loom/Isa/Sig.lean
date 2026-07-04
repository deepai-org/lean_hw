-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Core.Word

/-!
# Encoding signatures (L0 framework)

A `Sig` describes a machine's fixed-width instruction encoding: the word
width, where the opcode field lives, and the named operand fields. It is the
parameter that makes the instruction-declaration framework machine-generic
(P0/P1): LNP64-µ instantiates it at 32 bits, Acc8 at 16.

Variable-length encodings (6502-style) are a planned extension that lands
only with a consuming machine (decision D7).
-/

namespace Loom.Isa

/-- A named bit-field within an instruction word, LSB-indexed. -/
structure Field where
  name  : String
  lo    : Nat
  width : Nat
deriving Repr, DecidableEq

namespace Field

/-- Bit-range disjointness. -/
def disjoint (a b : Field) : Prop :=
  a.lo + a.width ≤ b.lo ∨ b.lo + b.width ≤ a.lo

instance : DecidablePred fun p : Field × Field => p.1.disjoint p.2 :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

instance (a b : Field) : Decidable (a.disjoint b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Extract this field from a word. -/
def get {n : Nat} (f : Field) (w : BitVec n) : BitVec f.width :=
  Loom.Word.extract f.lo f.width w

/-- Insert a value into this field of a word. -/
def set {n : Nat} (f : Field) (v : BitVec f.width) (w : BitVec n) : BitVec n :=
  Loom.Word.insert f.lo v w

end Field

/-- A machine's encoding signature. -/
structure Sig where
  /-- Instruction word width in bits. -/
  wordBits : Nat
  /-- The opcode field (dispatch key for decode). -/
  opcode : Field
  /-- The named operand fields. -/
  fields : List Field
deriving Repr

namespace Sig

/-- The instruction-word type of this signature. -/
abbrev Word (sig : Sig) := BitVec sig.wordBits

/-- Well-formedness: everything fits in the word, operand fields avoid the
opcode, and operand fields are pairwise disjoint. Decidable; each machine
discharges its instance by `decide`. -/
structure WF (sig : Sig) : Prop where
  opcode_le   : sig.opcode.lo + sig.opcode.width ≤ sig.wordBits
  fields_le   : ∀ f ∈ sig.fields, f.lo + f.width ≤ sig.wordBits
  fields_opc  : ∀ f ∈ sig.fields, f.disjoint sig.opcode
  fields_disj : sig.fields.Pairwise Field.disjoint

instance (sig : Sig) : Decidable sig.WF :=
  decidable_of_iff
    (sig.opcode.lo + sig.opcode.width ≤ sig.wordBits ∧
     (∀ f ∈ sig.fields, f.lo + f.width ≤ sig.wordBits) ∧
     (∀ f ∈ sig.fields, f.disjoint sig.opcode) ∧
     sig.fields.Pairwise Field.disjoint)
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-- The opcode bits of a word. -/
def opcodeOf (sig : Sig) (w : sig.Word) : BitVec sig.opcode.width :=
  sig.opcode.get w

/-- Look up an operand field by name. -/
def field? (sig : Sig) (name : String) : Option Field :=
  sig.fields.find? (·.name = name)

end Sig
end Loom.Isa
