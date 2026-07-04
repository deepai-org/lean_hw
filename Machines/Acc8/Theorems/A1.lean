-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Acc8.Spec

/-!
# A1 — Acc8 encoding soundness (the T1 analog)

The pathfinder's instance of the generic T1 kit: signature well-formedness
and opcode distinctness are discharged by `decide`; round-trip and operand
preservation follow from the generic theorems. Everything here is
kernel-checked with no `native_decide` (Rule 1).
-/

namespace Machines.Acc8.Theorems.A1

open Loom.Isa Machines.Acc8

/-- The encoding signature is well-formed. -/
theorem sig_wf : sig.WF := by decide

/-- Opcodes are pairwise distinct, hence decode is deterministic. -/
theorem opcodes_distinct : isa.OpcodesDistinct := by decide

/-- Round-trip: every encoded instruction decodes to its declaration, for
every operand assignment (assemble ∘ disassemble = id). -/
theorem decode_encode (i : Fin isa.size) (operands : sig.Word) :
    decode isa (encode isa i operands) = some isa[i] :=
  Loom.Isa.decode_encode isa sig_wf opcodes_distinct i operands

/-- Operand preservation: stamping the opcode never disturbs the operand. -/
theorem imm_preserved (i : Fin isa.size) (operands : sig.Word) :
    immField.get (encode isa i operands) = immField.get operands :=
  field_get_encode isa sig_wf (by simp [sig, immField]) i operands

/-- Decode coverage: every word whose opcode value is below 8 decodes. This
is Acc8's totality statement; opcodes ≥ 8 halt the machine by definition of
`step`. -/
theorem decode_coverage (w : sig.Word) (h : (sig.opcodeOf w).toNat < 8) :
    (decode isa w).isSome := by
  rw [isSome_decode_iff]
  generalize hc : sig.opcodeOf w = c at h ⊢
  have hcases : c.toNat = 0 ∨ c.toNat = 1 ∨ c.toNat = 2 ∨ c.toNat = 3 ∨
      c.toNat = 4 ∨ c.toNat = 5 ∨ c.toNat = 6 ∨ c.toNat = 7 := by omega
  have hbv : ∀ k : Nat, k < 8 → c.toNat = k → c = BitVec.ofNat 8 k := by
    intro k hk hck
    apply BitVec.eq_of_toNat_eq
    rw [hck]
    have h2 : (BitVec.ofNat 8 k).toNat = k % 2 ^ 8 := BitVec.toNat_ofNat ..
    omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact ⟨isa[0], by simp [isa], by rw [hbv 0 (by omega) h0]; rfl⟩
  · exact ⟨isa[1], by simp [isa], by rw [hbv 1 (by omega) h1]; rfl⟩
  · exact ⟨isa[2], by simp [isa], by rw [hbv 2 (by omega) h2]; rfl⟩
  · exact ⟨isa[3], by simp [isa], by rw [hbv 3 (by omega) h3]; rfl⟩
  · exact ⟨isa[4], by simp [isa], by rw [hbv 4 (by omega) h4]; rfl⟩
  · exact ⟨isa[5], by simp [isa], by rw [hbv 5 (by omega) h5]; rfl⟩
  · exact ⟨isa[6], by simp [isa], by rw [hbv 6 (by omega) h6]; rfl⟩
  · exact ⟨isa[7], by simp [isa], by rw [hbv 7 (by omega) h7]; rfl⟩

end Machines.Acc8.Theorems.A1
