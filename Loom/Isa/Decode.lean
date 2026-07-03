import Loom.Isa.Instr

/-!
# Generic decode/encode and the T1 obligation kit (L0 framework)

`decode` dispatches on the opcode field; `encode` stamps an opcode into an
operand word. The kit's theorems are the generic halves of every machine's
T1: encode/decode round-trip and operand-field preservation, proved once
here over the `Sig` well-formedness conditions — the per-machine halves
(opcode distinctness, signature well-formedness) are decidable and
discharged by `decide` at each concrete ISA.

Decode *totality* is deliberately machine-side: whether an unmatched opcode
is an illegal-instruction fault (LNP64-µ) or a halt (Acc8) is machine
semantics, so the kit returns `Option` and each machine's step maps `none`.
-/

namespace Loom.Isa

variable {sig : Sig} {Sem Cost : Type}

/-- Decode a word to the (first) matching declaration index. With
`OpcodesDistinct` "first" is "the": see `decodeIdx_encode`. -/
def decodeIdx (isa : Isa sig Sem Cost) (w : sig.Word) : Option (Fin isa.size) :=
  isa.findFinIdx? (fun d => d.opcode == sig.opcodeOf w)

/-- Decode a word to the matching declaration. -/
def decode (isa : Isa sig Sem Cost) (w : sig.Word) : Option (InstrDecl sig Sem Cost) :=
  (decodeIdx isa w).map (fun i => isa[i])

/-- Encode instruction `i` with the given operand bits: the opcode field is
stamped over `operands`. The assembler builds `operands` by `Field.set` on
zero; semantics read fields of the whole word, so this is also the canonical
instruction-word constructor for conformance vectors. -/
def encode (isa : Isa sig Sem Cost) (i : Fin isa.size) (operands : sig.Word) :
    sig.Word :=
  sig.opcode.set isa[i].opcode operands

/-! ## The generic T1 kit -/

/-- Encoding then reading the opcode yields the declared opcode. -/
theorem opcodeOf_encode (isa : Isa sig Sem Cost) (hwf : sig.WF)
    (i : Fin isa.size) (operands : sig.Word) :
    sig.opcodeOf (encode isa i operands) = isa[i].opcode := by
  unfold Sig.opcodeOf encode Field.set Field.get
  exact Loom.Word.extract_insert_self _ _ _ hwf.opcode_le

/-- Encoding preserves every operand field: stamping the opcode cannot
disturb operands (the frame half of the round-trip). -/
theorem field_get_encode (isa : Isa sig Sem Cost) (hwf : sig.WF)
    {f : Field} (hf : f ∈ sig.fields) (i : Fin isa.size) (operands : sig.Word) :
    f.get (encode isa i operands) = f.get operands := by
  unfold encode Field.set Field.get
  exact Loom.Word.extract_insert_of_disjoint _ _ (hwf.fields_le f hf)
    (hwf.fields_opc f hf)

/-- Decode inverts encode: with distinct opcodes, an encoded instruction
decodes to exactly its declaration, for every operand assignment. The
machine-independent core of "assemble ∘ disassemble = id". -/
theorem decodeIdx_encode (isa : Isa sig Sem Cost) (hwf : sig.WF)
    (hd : isa.OpcodesDistinct) (i : Fin isa.size) (operands : sig.Word) :
    decodeIdx isa (encode isa i operands) = some i := by
  rw [decodeIdx, Array.findFinIdx?_eq_some_iff]
  refine ⟨?_, ?_⟩
  · simp [opcodeOf_encode isa hwf]
  · intro j hji hmatch
    have hop : isa[j].opcode = isa[i].opcode := by
      have := opcodeOf_encode isa hwf i operands
      simpa [this] using hmatch
    exact absurd (hd j i hop) (by omega)

/-- `decode` form of the round-trip. -/
theorem decode_encode (isa : Isa sig Sem Cost) (hwf : sig.WF)
    (hd : isa.OpcodesDistinct) (i : Fin isa.size) (operands : sig.Word) :
    decode isa (encode isa i operands) = some isa[i] := by
  simp [decode, decodeIdx_encode isa hwf hd]

/-- Coverage: decode succeeds exactly when some declaration carries the
word's opcode — the machine-independent core of each machine's decode
totality statement. -/
theorem isSome_decode_iff (isa : Isa sig Sem Cost) (w : sig.Word) :
    (decode isa w).isSome ↔ ∃ d ∈ isa, d.opcode = sig.opcodeOf w := by
  rw [decode, Option.isSome_map, decodeIdx, Array.isSome_findFinIdx?,
    Array.any_eq_true]
  simp only [beq_iff_eq]
  constructor
  · rintro ⟨i, hi, hop⟩
    exact ⟨isa[i], Array.getElem_mem hi, hop⟩
  · rintro ⟨d, hd, hop⟩
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hd
    exact ⟨i, hi, hop⟩

/-- Decoding is stable under operand choice: any two words with the same
opcode decode to the same declaration index. -/
theorem decodeIdx_congr (isa : Isa sig Sem Cost) {w w' : sig.Word}
    (h : sig.opcodeOf w = sig.opcodeOf w') :
    decodeIdx isa w = decodeIdx isa w' := by
  simp [decodeIdx, h]

end Loom.Isa
