import Machines.Lnp64u.Step

/-!
# T1 — Encoding and convention soundness

Decode totality (coverage over the legal opcode set, and refusal outside
it), decode determinism (distinct opcodes), assemble∘disassemble identity
(via the generic kit), operand-field preservation, the errno return-ABI
bound, and null-handle unconstructibility. All kernel-checked; the
per-machine halves are `decide`d, the generic halves are instances of
`Loom.Isa`'s T1 kit.
-/

namespace Machines.Lnp64u.Theorems.T1

open Loom.Isa Machines.Lnp64u

/-- The encoding signature is well-formed (D1's layout partitions the
word). -/
theorem sig_wf : sig.WF := by decide

/-- Opcodes are pairwise distinct: decode is deterministic. -/
theorem opcodes_distinct : isa.OpcodesDistinct := by decide

/-- Assemble ∘ disassemble = id: every encoded instruction decodes to its
own declaration, for every operand assignment. -/
theorem decode_encode (i : Fin isa.size) (operands : sig.Word) :
    decode isa (encode isa i operands) = some isa[i] :=
  Loom.Isa.decode_encode isa sig_wf opcodes_distinct i operands

/-- Operand fields survive encoding (frame half of the round-trip), for
each of the four fields. -/
theorem operands_preserved (f : Field) (hf : f ∈ sig.fields)
    (i : Fin isa.size) (operands : sig.Word) :
    f.get (encode isa i operands) = f.get operands :=
  field_get_encode isa sig_wf hf i operands

/-! ## Decode totality over the opcode space -/

/-- The legal opcode values: 0–13 (base), 16–26 (system). -/
def legalOp (n : Nat) : Bool := n < 14 || (16 ≤ n && n ≤ 26)

/-- Index of a legal opcode's declaration in `isa`. -/
def opIdx (n : Nat) : Nat := if n < 14 then n else n - 2

/-- The witness table: each legal opcode value names the declaration at its
index. Kernel-evaluated over all 64 opcode values. -/
theorem opcode_at : ∀ n : Fin 64, legalOp n.val →
    ∀ h : opIdx n.val < isa.size, isa[opIdx n.val].opcode = BitVec.ofNat 6 n.val := by
  decide

/-- No declaration carries an illegal opcode (the refusal half of
totality). Kernel-evaluated over the ISA. -/
theorem opcodes_legal : ∀ i : Fin isa.size, legalOp isa[i].opcode.toNat := by
  decide

/-- Coverage: every word whose opcode value is legal decodes. -/
theorem decode_coverage (w : sig.Word) (h : legalOp (sig.opcodeOf w).toNat) :
    (decode isa w).isSome := by
  rw [isSome_decode_iff]
  have hlt : (sig.opcodeOf w).toNat < 64 := (sig.opcodeOf w).isLt
  have hidx : opIdx (sig.opcodeOf w).toNat < isa.size := by
    simp only [legalOp, Bool.or_eq_true, decide_eq_true_eq,
      Bool.and_eq_true] at h
    have hsz : isa.size = 25 := rfl
    rw [hsz]
    unfold opIdx
    split <;> omega
  refine ⟨isa[opIdx (sig.opcodeOf w).toNat], Array.getElem_mem hidx, ?_⟩
  rw [opcode_at ⟨(sig.opcodeOf w).toNat, hlt⟩ h hidx]
  rw [BitVec.ofNat_toNat]
  exact BitVec.setWidth_eq _

/-- Refusal: a word with an illegal opcode does not decode — illegal
instructions are a fault, never a misinterpretation. -/
theorem decode_illegal (w : sig.Word) (h : ¬ legalOp (sig.opcodeOf w).toNat) :
    decode isa w = none := by
  cases hd : decode isa w with
  | none => rfl
  | some d =>
      exfalso
      have hs : (decode isa w).isSome := by rw [hd]; rfl
      rw [isSome_decode_iff] at hs
      obtain ⟨d', hmem, hop⟩ := hs
      obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hmem
      exact h (hop ▸ opcodes_legal ⟨i, hi⟩)

/-! ## Return-ABI bound and the null handle -/

/-- The errno ABI bound: every errno word is one of the top sixteen
negative words — `-16 ≤ -errno ≤ -1` in two's complement — so no errno
collides with a handle word (handles have bits 31:13 zero) or with
success (0). -/
theorem errno_bound : ∀ e : Errno, 2 ^ 32 - 16 ≤ e.toWord.toNat := by
  intro e; cases e <;> decide

set_option maxHeartbeats 4000000 in
/-- Handle round-trip: decoding an encoded handle recovers it exactly
(both classes; kernel-evaluated over all 16 × 256 slot/generation pairs). -/
theorem handle_roundtrip : ∀ (s : Slot) (g : Gen),
    Handle.decode (Handle.encode ⟨s, g, .mem⟩) = ⟨s, g, .mem⟩ ∧
    Handle.decode (Handle.encode ⟨s, g, .gate⟩) = ⟨s, g, .gate⟩ := by
  decide

/-- Null-handle unconstructibility: no handle with generation ≥ 1 encodes
to the null word. Since every live capability's generation is ≥ 1 (T9's
invariant material), null handles cannot be manufactured from live
capabilities. -/
theorem null_unconstructible : ∀ (s : Slot) (g : Gen), g ≠ 0 →
    ∀ c : CapClass, Handle.encode ⟨s, g, c⟩ ≠ Handle.null := by
  intro s g hg c heq
  have hrt := handle_roundtrip s g
  have hnull : (Handle.decode Handle.null).gen = 0 := by decide
  cases c with
  | mem => have := hrt.1; rw [heq] at this; rw [this] at hnull; exact hg hnull
  | gate => have := hrt.2; rw [heq] at this; rw [this] at hnull; exact hg hnull

end Machines.Lnp64u.Theorems.T1
