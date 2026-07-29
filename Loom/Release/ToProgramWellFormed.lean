-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ToProgram
import Loom.Release.ToProgramLemmas
import Loom.Release.RopeLayout
import Loom.Release.FlattenWF

/-!
# Assembly toward `toProgram_wireWellFormed`

Bridging facts that connect the constructed witness's three faces — the
flat wire list (`FlattenSt.wires` of `flattenModule`), the indexed view
(`Design.toIndexedWires`), and the shaped ropes (`Design.indexedsOf`,
`(d.toProgram).wires`). The first brick: `toIndexedWires` reruns `flatten`
with `for` loops that discard results, and its final state is exactly
`flattenModule`'s, so the indexed wires are literally the numbered
projection of the same flat array the program's raw rope is shaped from.
-/

open private String.Slice.Pattern.Internal.memcmpStr.go from
  Init.Data.String.Pattern.Basic

namespace Loom.Release.SSA

open Loom.Hw Loom.Emit.MicroVerilog

/-- In `Id`, bind is application; making that a rewrite lets `simp` erase
the monadic plumbing `for` desugaring leaves behind. -/
private theorem id_bind_eq {α β : Type} (x : Id α) (f : α → Id β) :
    x >>= f = f x := rfl

private theorem id_pure_eq {α : Type} (a : α) : (pure a : Id α) = a := rfl

/-- The register loop of `toIndexedWires` has the same state effect as
`flattenRegs`. -/
theorem forRegs_state (regs : List RegDef) (s : FlattenSt) :
    ((show StateM FlattenSt Unit from do
        for r in regs do
          _ ← flatten r.next).run s).2 =
      ((flattenRegs regs).run s).2 := by
  induction regs generalizing s with
  | nil => rfl
  | cons r rest ih =>
      rw [flattenRegs_run_cons]
      simp only [List.forIn_cons, StateT.run_bind, StateT.run_pure]
      exact ih ((flatten r.next).run s).2

/-- The write-port loop of `toIndexedWires` has the same state effect as
`flattenWrites`. -/
theorem forWrites_state {aw dw : Nat} (ports : List (WritePort aw dw))
    (s : FlattenSt) :
    ((show StateM FlattenSt Unit from do
        for p in ports do
          _ ← flatten p.en
          _ ← flatten p.addr
          _ ← flatten p.data).run s).2 =
      ((flattenWrites ports).run s).2 := by
  induction ports generalizing s with
  | nil => rfl
  | cons p rest ih =>
      simp only [List.forIn_cons, flattenWrites, StateT.run_bind,
        StateT.run_pure]
      exact ih ((flatten p.data).run
        ((flatten p.addr).run ((flatten p.en).run s).2).2).2

/-- The memory loop of `toIndexedWires` has the same state effect as
`flattenMems` (for any `blockSize`: image chunking allocates no wires). -/
theorem forMems_state (mems : List MemDef) (blockSize : Nat) (s : FlattenSt) :
    ((show StateM FlattenSt Unit from do
        for mm in mems do
          for p in mm.wrPorts do
            _ ← flatten p.en
            _ ← flatten p.addr
            _ ← flatten p.data).run s).2 =
      ((flattenMems blockSize mems).run s).2 := by
  induction mems generalizing s with
  | nil => rfl
  | cons mm rest ih =>
      rw [flattenMems_run_cons]
      simp only [List.forIn_cons, StateT.run_bind, StateT.run_pure,
        id_bind_eq, id_pure_eq]
      have hstate := forWrites_state mm.wrPorts s
      simp only [StateT.run_bind, StateT.run_pure, id_bind_eq,
        id_pure_eq] at hstate
      rw [hstate]
      have tail := ih ((flattenWrites mm.wrPorts).run s).2
      simp only [StateT.run_bind, StateT.run_pure, id_bind_eq,
        id_pure_eq] at tail
      exact tail

/-- The output loop of `toIndexedWires` has the same state effect as
`flattenOuts`. -/
theorem forOuts_state (outs : List OutDef) (s : FlattenSt) :
    ((show StateM FlattenSt Unit from do
        for o in outs do
          _ ← flatten o.val).run s).2 =
      ((flattenOuts outs).run s).2 := by
  induction outs generalizing s with
  | nil => rfl
  | cons o rest ih =>
      rw [flattenOuts_run_cons]
      simp only [List.forIn_cons, StateT.run_bind, StateT.run_pure]
      exact ih ((flatten o.val).run s).2

/-- `toIndexedWires` is the numbered projection of the exact flat wire
array `flattenModule` produces — the two constructions share one state. -/
theorem toIndexedWires_eq_flattenModule (d : Loom.Hw.Design) (blockSize : Nat) :
    d.toIndexedWires =
      ((((flattenModule (Compile.compile d) blockSize).run {}).2).wires.toList.zipIdx.map
        fun (wire, number) =>
          { number, width := wire.width, rhs := indexedRhsOf wire.rhs }) := by
  have state_eq :
      ((show StateM FlattenSt Unit from do
          for r in (Compile.compile d).regs do
            _ ← flatten r.next
          for mm in (Compile.compile d).mems do
            for p in mm.wrPorts do
              _ ← flatten p.en
              _ ← flatten p.addr
              _ ← flatten p.data
          for o in (Compile.compile d).outs do
            _ ← flatten o.val).run {}).2 =
      ((flattenModule (Compile.compile d) blockSize).run {}).2 := by
    rw [flattenModule_run]
    calc ((show StateM FlattenSt Unit from do
            for r in (Compile.compile d).regs do
              _ ← flatten r.next
            for mm in (Compile.compile d).mems do
              for p in mm.wrPorts do
                _ ← flatten p.en
                _ ← flatten p.addr
                _ ← flatten p.data
            for o in (Compile.compile d).outs do
              _ ← flatten o.val).run {}).2
        = ((show StateM FlattenSt Unit from do
            for o in (Compile.compile d).outs do
              _ ← flatten o.val).run
            ((show StateM FlattenSt Unit from do
              for mm in (Compile.compile d).mems do
                for p in mm.wrPorts do
                  _ ← flatten p.en
                  _ ← flatten p.addr
                  _ ← flatten p.data).run
              ((show StateM FlattenSt Unit from do
                for r in (Compile.compile d).regs do
                  _ ← flatten r.next).run {}).2).2).2 := rfl
      _ = _ := by
        rw [forRegs_state, forMems_state (blockSize := blockSize), forOuts_state]
  exact congrArg
    (fun st : FlattenSt => st.wires.toList.zipIdx.map
      fun (wire, number) =>
        ({ number, width := wire.width,
           rhs := indexedRhsOf wire.rhs } : Symbolic.IndexedWire))
    state_eq

/-- Raw-side layout: `lookupRaw?` on the witness shape answers with the
wire the flat list holds at that number — `lookupIndexed?_shaped` without
the number guard. -/
theorem lookupRaw?_shaped (k leafSize : Nat) (hs : 0 < leafSize)
    (xs : List Wire) (n : Nat) (wire : Wire) (hfound : xs[n]? = some wire) :
    Symbolic.lookupRaw?
      (balancedRope ((listChunks (2 ^ k)
        ((listChunks leafSize xs).map Rope.leaf)).map balancedRope))
      { leafSize := leafSize,
        leafCount := (xs.length + leafSize - 1) / leafSize }
      n = some wire := by
  have hn : n < xs.length := lt_of_getElem?_eq_some hfound
  have hcount : n / leafSize < (xs.length + leafSize - 1) / leafSize := by
    rw [show xs.length + leafSize - 1 = xs.length - 1 + leafSize by omega,
      Nat.add_div_right _ hs]
    have := Nat.div_le_div_right (c := leafSize)
      (show n ≤ xs.length - 1 by omega)
    omega
  obtain ⟨path, hpath⟩ :=
    Option.isSome_iff_exists.mp (balancedPath?_isSome _ _ hcount)
  have resolved : (balancedRope ((listChunks (2 ^ k)
      ((listChunks leafSize xs).map Rope.leaf)).map balancedRope)).resolve?
        ⟨path, n % leafSize⟩ = some wire := by
    rw [balancedRope_chunks_pow2,
      balancedRope_resolve_path (listChunks leafSize xs) (n / leafSize) path
        (by rw [listChunks_length leafSize hs xs]; exact hpath) (n % leafSize),
      listChunks_getElem leafSize hs xs n]
    exact hfound
  simp [Symbolic.lookupRaw?, hs, hpath, resolved, guard]

/-! ## Declaration lookup transfer

`refWidthBefore?` consults `program.regs`/`program.mems`; the flatten
invariant speaks about the module's `RegDef`/`MemDef` lists. Flattening
preserves names and widths pointwise in order, so `find?` answers
correspond. -/

/-- `find?` on flattened registers returns the declaration's name and
width. -/
theorem flattenRegs_find?_meta (regs : List RegDef) (s : FlattenSt)
    (name : String) :
    (((flattenRegs regs).run s).1.find? (fun c => c.name == name)).map
        (fun c => (c.name, c.width)) =
      (regs.find? (fun r => r.name == name)).map
        (fun r => (r.name, r.width)) := by
  induction regs generalizing s with
  | nil => rfl
  | cons r rest ih =>
      rw [flattenRegs_run_cons]
      by_cases hname : r.name == name
      · simp [hname]
      · simp only [List.find?_cons, hname]
        exact ih ((flatten r.next).run s).2

/-- `find?` on flattened memories returns the declaration's name and both
widths. -/
theorem flattenMems_find?_meta (mems : List MemDef) (blockSize : Nat)
    (s : FlattenSt) (name : String) :
    (((flattenMems blockSize mems).run s).1.find?
        (fun c => c.name == name)).map
        (fun c => (c.name, c.addrWidth, c.dataWidth)) =
      (mems.find? (fun mm => mm.name == name)).map
        (fun mm => (mm.name, mm.addrWidth, mm.dataWidth)) := by
  induction mems generalizing s with
  | nil => rfl
  | cons mm rest ih =>
      rw [flattenMems_run_cons]
      by_cases hname : mm.name == name
      · simp [hname]
      · simp only [List.find?_cons, hname]
        exact ih ((flattenWrites mm.wrPorts).run s).2

/-! ## A kernel-reducible stand-in for `wireNumber?`

The emission checker must reject register names that collide with the
release witness's canonical wire spelling (`wireNumber? name = none`).
`Symbolic.wireNumber?` itself works through byte-based `String.drop` and
`Slice.toNat?`, which the kernel cannot reduce; `isWireLikeB` re-decides a
superset of "`wireNumber?` answers `some`" by structural recursion over
`String.toList`, which the kernel reduces fine. The soundness bridge below
(`wireNumber?_eq_none_of_not_isWireLike`) needs only one direction: a name
the character-level test rejects is one `wireNumber?` cannot decode. -/

section WireLike

open String Std

/-- A character `Slice.toNat?` can consume: a decimal digit or an
underscore separator. -/
def natCharB (c : Char) : Bool := c.isDigit || c == '_'

/-- Kernel-reducible over-approximation of "`Symbolic.wireNumber?` answers
`some`": the name is `'n'` followed by a nonempty run of digit-or-underscore
characters. (`toNat?` additionally rejects misplaced underscores, so this is
a strict superset — the sound direction for the checker.) -/
def isWireLikeB (s : String) : Bool :=
  match s.toList with
  | 'n' :: rest => !rest.isEmpty && rest.all natCharB
  | _ => false

example : isWireLikeB "acc" = false := by decide
example : isWireLikeB "n17" = true := by decide
example : isWireLikeB "n" = false := by decide
example : isWireLikeB "n0_7" = true := by decide
example : isWireLikeB "" = false := by decide

/-! ### Slice folds as list folds

Replicated from `FlattenWF.lean`'s private `WireName` helpers: the slice
iterator visits exactly the characters of the copied string, so
`Slice.foldl` is a `List.foldl` over `copy.toList`. -/

private theorem posIter_toList {s : String.Slice} (l : List Char) :
    ∀ (p : s.Pos) (t₁ t₂ : String), p.Splits t₁ t₂ → t₂.toList = l →
    (({ internalState := { currPos := p } } : Iter (α := String.Slice.PosIterator s)
        { q : s.Pos // q ≠ s.endPos }).toList).map (fun x => x.1.get x.2) = l := by
  induction l with
  | nil =>
    intro p t₁ t₂ hsp hl
    rw [Iter.toList_eq_match_step]
    have hp := (({ internalState := { currPos := p } } : Iter (α := String.Slice.PosIterator s)
        { q : s.Pos // q ≠ s.endPos }).step).property
    cases hs : (({ internalState := { currPos := p } } : Iter (α := String.Slice.PosIterator s)
        { q : s.Pos // q ≠ s.endPos }).step).val with
    | yield it' out =>
      rw [hs] at hp
      obtain ⟨hne, _, _⟩ := hp
      have ht2 : t₂ = "" := by rwa [← String.toList_eq_nil_iff]
      exact absurd (hsp.eq_endPos_iff.mpr ht2) hne
    | skip it' =>
      rw [hs] at hp
      exact hp.elim
    | done => simp
  | cons c cs ih =>
    intro p t₁ t₂ hsp hl
    rw [Iter.toList_eq_match_step]
    have hp := (({ internalState := { currPos := p } } : Iter (α := String.Slice.PosIterator s)
        { q : s.Pos // q ≠ s.endPos }).step).property
    cases hs : (({ internalState := { currPos := p } } : Iter (α := String.Slice.PosIterator s)
        { q : s.Pos // q ≠ s.endPos }).step).val with
    | yield it' out =>
      rw [hs] at hp
      obtain ⟨hne, hnext, hout⟩ := hp
      subst hout
      obtain ⟨t₂', ht₂'⟩ := hsp.exists_eq_singleton_append hne
      have htl := congrArg String.toList ht₂'
      rw [hl, String.toList_append, String.toList_singleton] at htl
      have hget : out.val.get hne = c := (List.cons.injEq _ _ _ _ ▸ htl).1.symm
      have ht₂'l : t₂'.toList = cs := (List.cons.injEq _ _ _ _ ▸ htl).2.symm
      have hnexts : (out.val.next hne).Splits (t₁ ++ String.singleton (out.val.get hne)) t₂' :=
        (ht₂' ▸ hsp).next
      obtain ⟨⟨cp⟩⟩ := it'
      have hcp : cp = out.val.next hne := hnext
      subst hcp
      rw [List.map_cons]
      congr 1
      exact ih _ _ t₂' hnexts ht₂'l
    | skip it' =>
      rw [hs] at hp
      exact hp.elim
    | done =>
      rw [hs] at hp
      have := hsp.eq_endPos_iff.mp hp
      rw [this] at hl
      simp at hl

private theorem chars_toList (sl : String.Slice) : sl.chars.toList = sl.copy.toList := by
  show (Std.Iter.map _ sl.positions).toList = sl.copy.toList
  rw [Iter.toList_map]
  exact posIter_toList _ sl.startPos "" sl.copy sl.splits_startPos rfl

private theorem slice_foldl_eq {α : Type} (f : α → Char → α) (init : α) (sl : String.Slice) :
    sl.foldl f init = sl.copy.toList.foldl f init := by
  show Std.Iter.fold f init sl.chars = _
  rw [← Iter.foldl_toList, chars_toList]

/-! ### `toNat?` success forces nonempty digit-or-underscore content -/

private theorem foldl_valid_of_valid
    (F : Bool × Bool × Bool × Bool → Char → Bool × Bool × Bool × Bool)
    (hF : ∀ a c, (F a c).2.2.2 = true → a.2.2.2 = true ∧ natCharB c = true) :
    ∀ (l : List Char) (a : Bool × Bool × Bool × Bool),
      (List.foldl F a l).2.2.2 = true → a.2.2.2 = true := by
  intro l
  induction l with
  | nil => intro a h; exact h
  | cons c cs ih =>
    intro a h
    rw [List.foldl_cons] at h
    exact (hF a c (ih (F a c) h)).1

private theorem foldl_valid_chars
    (F : Bool × Bool × Bool × Bool → Char → Bool × Bool × Bool × Bool)
    (hF : ∀ a c, (F a c).2.2.2 = true → a.2.2.2 = true ∧ natCharB c = true) :
    ∀ (l : List Char) (a : Bool × Bool × Bool × Bool),
      (List.foldl F a l).2.2.2 = true → ∀ c ∈ l, natCharB c = true := by
  intro l
  induction l with
  | nil => intro a _ c hc; exact absurd hc (List.not_mem_nil)
  | cons c cs ih =>
    intro a h c' hc'
    rw [List.foldl_cons] at h
    rcases List.mem_cons.mp hc' with hc' | hc'
    · subst hc'
      exact (hF a c' (foldl_valid_of_valid F hF cs (F a c') h)).2
    · exact ih (F a c) h c' hc'

/-- `Slice.toNat?` succeeds only on nonempty content made of digits and
underscores. -/
private theorem toNat?_chars {sl : String.Slice} {k : Nat}
    (h : sl.toNat? = some k) :
    sl.copy.toList ≠ [] ∧ ∀ c ∈ sl.copy.toList, natCharB c = true := by
  rw [String.Slice.toNat?.eq_def] at h
  split at h
  case isFalse => exact absurd h (by simp)
  case isTrue hnat =>
    rw [String.Slice.isNat.eq_def] at hnat
    split at hnat
    case isTrue => exact absurd hnat (by simp)
    case isFalse =>
      rw [slice_foldl_eq] at hnat
      simp only [Bool.and_eq_true] at hnat
      refine ⟨?_, foldl_valid_chars _ ?hF _ _ hnat.1⟩
      case hF =>
        intro a c hv
        simp only [Bool.and_eq_true] at hv
        refine ⟨hv.1.1.1, ?_⟩
        simp only [natCharB, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hv ⊢
        exact hv.1.1.2
      intro hnil
      rw [hnil] at hnat
      exact absurd hnat.2 (by simp)

/-! ### First-byte extraction from `startsWith "n"` -/

private theorem go_one_rev (lhs rhs : String) (lstart rstart : Pos.Raw)
    (h1 : (⟨1⟩ : Pos.Raw).offsetBy lstart ≤ lhs.rawEndPos)
    (h2 : (⟨1⟩ : Pos.Raw).offsetBy rstart ≤ rhs.rawEndPos)
    (hgo : String.Slice.Pattern.Internal.memcmpStr.go lhs rhs lstart rstart
      ⟨1⟩ h1 h2 0 = true)
    (hpl : Pos.Raw.offsetBy 0 lstart < lhs.rawEndPos)
    (hpr : Pos.Raw.offsetBy 0 rstart < rhs.rawEndPos) :
    lhs.getUTF8Byte (Pos.Raw.offsetBy 0 lstart) hpl =
      rhs.getUTF8Byte (Pos.Raw.offsetBy 0 rstart) hpr := by
  rw [String.Slice.Pattern.Internal.memcmpStr.go.eq_def] at hgo
  rw [dif_pos (show (0 : Pos.Raw) < (⟨1⟩ : Pos.Raw) by decide)] at hgo
  replace hgo :
      (if (lhs.getUTF8Byte (Pos.Raw.offsetBy 0 lstart) hpl ==
            rhs.getUTF8Byte (Pos.Raw.offsetBy 0 rstart) hpr) = true then
        String.Slice.Pattern.Internal.memcmpStr.go lhs rhs lstart rstart
          ⟨1⟩ h1 h2 (Pos.Raw.inc 0)
      else false) = true := hgo
  by_cases hb : (lhs.getUTF8Byte (Pos.Raw.offsetBy 0 lstart) hpl ==
      rhs.getUTF8Byte (Pos.Raw.offsetBy 0 rstart) hpr) = true
  · exact eq_of_beq hb
  · rw [if_neg hb] at hgo
    exact absurd hgo (by simp)

private theorem firstByte_of_startsWith {s : String}
    (h : s.startsWith "n" = true) :
    ∃ (hlt : (0 : Pos.Raw) < s.rawEndPos),
      s.getUTF8Byte 0 hlt = 110 := by
  replace h : String.Slice.Pattern.ForwardSliceSearcher.startsWith
      "n".toSlice s.toSlice = true := h
  rw [String.Slice.Pattern.ForwardSliceSearcher.startsWith.eq_def] at h
  split at h
  case isFalse => exact absurd h (by simp)
  case isTrue hle =>
    rw [String.Slice.Pattern.Internal.memcmpSlice] at h
    rw [String.Slice.Pattern.Internal.memcmpStr.eq_def] at h
    have hsize : (0 : Pos.Raw) < s.rawEndPos := by
      rw [String.utf8ByteSize_toSlice, String.utf8ByteSize_toSlice] at hle
      have h1 : "n".utf8ByteSize = 1 := rfl
      simp only [Pos.Raw.lt_iff]
      show 0 < s.utf8ByteSize
      omega
    exact ⟨hsize, go_one_rev _ _ _ _ _ _ h hsize (by decide)⟩

/-! ### First byte `0x6E` forces first character `'n'` -/

private theorem eq_n_of_utf8EncodeChar_head {c : Char}
    (h : (String.utf8EncodeChar c).head? = some 110) : c = 'n' := by
  revert h
  fun_cases String.utf8EncodeChar c
  all_goals
    intro h
    simp only [List.head?_cons, Option.some.injEq] at h
    replace h := congrArg UInt8.toNat h
    simp only [UInt8.toNat_ofNat', UInt8.toNat_ofNat] at h
    try (exfalso; omega)
  apply Char.ext
  apply UInt32.toNat_inj.mp
  have h110 : ('n'.val).toNat = 110 := rfl
  omega

private theorem first_char_eq_n {s : String} {c : Char} {cs : List Char}
    (hlt : (0 : Pos.Raw) < s.rawEndPos) (hb : s.getUTF8Byte 0 hlt = 110)
    (hl : s.toList = c :: cs) : c = 'n' := by
  apply eq_n_of_utf8EncodeChar_head
  have henc : s.toByteArray = (s.toList.flatMap String.utf8EncodeChar).toByteArray :=
    String.utf8Encode_toList.symm
  rw [String.getUTF8Byte] at hb
  simp only [henc, List.getElem_toByteArray] at hb
  have hlen : 0 < (String.utf8EncodeChar c).length := by
    cases henc' : String.utf8EncodeChar c with
    | nil => exact absurd henc' String.utf8EncodeChar_ne_nil
    | cons _ _ => simp
  simp only [String.Pos.Raw.byteIdx_zero, hl, List.flatMap_cons] at hb
  rw [List.getElem_append_left hlen] at hb
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen, hb]

/-! ### `startsWith "n"` forces the `'n' ::` decomposition -/

private theorem nextn_one {sl : String.Slice} (p : sl.Pos) (h : p ≠ sl.endPos) :
    p.nextn 1 = p.next h := by
  simp [String.Slice.Pos.nextn, h]

private theorem toList_drop_one {s : String}
    (hne : s.toSlice.startPos ≠ s.toSlice.endPos) :
    s.toList = s.toSlice.startPos.get hne :: ((s.drop 1).copy).toList := by
  have hcopy : s.toSlice.copy = s := String.copy_toSlice
  have hsplit := s.toSlice.startPos.splits_next_right hne
  have hstart := s.toSlice.splits_startPos
  have heq := hstart.eq hsplit
  rw [hcopy] at heq
  have h2 := congrArg String.toList heq.2
  rw [String.toList_append, String.toList_singleton] at h2
  have hdrop : (s.drop 1).copy =
      (s.toSlice.sliceFrom (s.toSlice.startPos.next hne)).copy := by
    show (s.toSlice.sliceFrom (s.toSlice.startPos.nextn 1)).copy = _
    rw [nextn_one _ hne]
  rw [hdrop]
  exact h2

/-! ### The soundness bridge -/

theorem isWireLikeB_of_wireNumber?_some {s : String} {k : Nat}
    (h : Symbolic.wireNumber? s = some k) : isWireLikeB s = true := by
  rw [Loom.Release.Symbolic.wireNumber?] at h
  by_cases hsw : s.startsWith "n" = true
  · simp only [guard, hsw, if_pos, Option.pure_def] at h
    obtain ⟨hnil, hall⟩ := toNat?_chars h
    obtain ⟨hlt, hbyte⟩ := firstByte_of_startsWith hsw
    have hs0 : s ≠ "" := by
      intro h0
      subst h0
      exact absurd hlt (by decide)
    have hne : s.toSlice.startPos ≠ s.toSlice.endPos := by
      intro h0
      have h1 := (String.Slice.splits_startPos s.toSlice).eq_endPos_iff.mp h0
      rw [String.copy_toSlice] at h1
      exact hs0 h1
    have hl := toList_drop_one hne
    have hc := first_char_eq_n hlt hbyte hl
    rw [hc] at hl
    simp only [isWireLikeB, hl, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, List.all_eq_true]
    refine ⟨?_, hall⟩
    simpa using hnil
  · simp [guard, hsw] at h
    rw [show (failure : Option Unit) = none from rfl] at h
    exact absurd h (by simp)

/-- The checker direction: a name the kernel-reducible test rejects is one
`Symbolic.wireNumber?` cannot decode. -/
theorem wireNumber?_eq_none_of_not_isWireLike (s : String)
    (h : isWireLikeB s = false) : Symbolic.wireNumber? s = none := by
  cases hw : Symbolic.wireNumber? s with
  | none => rfl
  | some k =>
      rw [isWireLikeB_of_wireNumber?_some hw] at h
      exact absurd h (by simp)

end WireLike

/-! ## The decidable emission check

`flattenModule_wf` consumes `ModuleEmitOk`; a concrete design should pay one
kernel-reducible Boolean instead of a hand proof (the same D12 shape as
`Symbolic.designReadsValidB`). The checker mirrors `ExprEmitOk`
case-for-case. -/

/-- Decidable form of `ExprEmitOk`. -/
def exprEmitOkB (regs : List RegDef) (mems : List MemDef) :
    {w : Nat} → Emit.MicroVerilog.Expr w → Bool
  | w, .reg _ name =>
      match regs.find? (fun c => c.name == name) with
      | some r => r.width == w && !(isWireLikeB name)
      | none => false
  | _, .lit _ => true
  | dw, @Emit.MicroVerilog.Expr.memRead _ mem aw addr =>
      (match mems.find? (fun c => c.name == mem) with
       | some header => header.addrWidth == aw && header.dataWidth == dw
       | none => false) &&
      exprEmitOkB regs mems addr
  | _, .and a b | _, .or a b | _, .xor a b | _, .add a b | _, .sub a b
  | _, .shl a b | _, .shr a b | _, .eq a b | _, .ult a b | _, .slt a b =>
      exprEmitOkB regs mems a && exprEmitOkB regs mems b
  | _, .not a => exprEmitOkB regs mems a
  | _, .mux c t f =>
      exprEmitOkB regs mems c && exprEmitOkB regs mems t &&
        exprEmitOkB regs mems f
  | _, @Emit.MicroVerilog.Expr.slice _ a _ w' =>
      decide (0 < w') && exprEmitOkB regs mems a
  | _, .zext a _ => exprEmitOkB regs mems a
  | w', @Emit.MicroVerilog.Expr.sext w a _ =>
      decide (w < w' → 0 < w) && decide (w' < w → 0 < w') &&
        exprEmitOkB regs mems a

theorem exprEmitOkB_sound {regs : List RegDef} {mems : List MemDef}
    {w : Nat} (e : Emit.MicroVerilog.Expr w) :
    exprEmitOkB regs mems e = true → ExprEmitOk regs mems e := by
  induction e with
  | lit v => exact fun _ => trivial
  | reg wr name =>
      intro accepted
      simp only [exprEmitOkB] at accepted
      cases found : regs.find? (fun c => c.name == name) with
      | none => simp [found] at accepted
      | some r =>
          simp only [found, Bool.and_eq_true, beq_iff_eq,
            Bool.not_eq_eq_eq_not, Bool.not_true] at accepted
          exact ⟨wireNumber?_eq_none_of_not_isWireLike name accepted.2,
            r, found, accepted.1⟩
  | memRead dw mem addr ih =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      obtain ⟨hfind, haddr⟩ := accepted
      refine ⟨?_, ih haddr⟩
      cases found : mems.find? (fun c => c.name == mem) with
      | none => simp [found] at hfind
      | some header =>
          simp only [found, Bool.and_eq_true, beq_iff_eq] at hfind
          exact ⟨header, rfl, hfind.1, hfind.2⟩
  | and a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | or a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | xor a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | add a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | sub a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | shl a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | shr a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | eq a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | ult a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | slt a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | not a ih => exact fun accepted => ih accepted
  | mux c t f ihc iht ihf =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨ihc accepted.1.1, iht accepted.1.2, ihf accepted.2⟩
  | slice a lo w' ih =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true, decide_eq_true_eq] at accepted
      exact ⟨accepted.1, ih accepted.2⟩
  | zext a w' ih => exact fun accepted => ih accepted
  | sext a w' ih =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true, decide_eq_true_eq] at accepted
      exact ⟨accepted.1.1, accepted.1.2, ih accepted.2⟩

/-- One kernel-reducible Boolean per design: every expression the printer
traversal flattens meets its emission obligations. -/
def moduleEmitOkB (m : Module) : Bool :=
  m.regs.all (fun r => exprEmitOkB m.regs m.mems r.next) &&
    m.mems.all (fun mm => mm.wrPorts.all fun p =>
      exprEmitOkB m.regs m.mems p.en && exprEmitOkB m.regs m.mems p.addr &&
        exprEmitOkB m.regs m.mems p.data) &&
    m.outs.all (fun o => exprEmitOkB m.regs m.mems o.val)

theorem moduleEmitOkB_sound (m : Module) (accepted : moduleEmitOkB m = true) :
    ModuleEmitOk m := by
  simp only [moduleEmitOkB, Bool.and_eq_true, List.all_eq_true] at accepted
  obtain ⟨⟨hregs, hmems⟩, houts⟩ := accepted
  refine ⟨fun r hr => exprEmitOkB_sound r.next (hregs r hr),
    fun mm hmm p hp => ?_,
    fun o ho => exprEmitOkB_sound o.val (houts o ho)⟩
  have hport := hmems mm hmm p hp
  exact ⟨exprEmitOkB_sound p.en hport.1.1, exprEmitOkB_sound p.addr hport.1.2,
    exprEmitOkB_sound p.data hport.2⟩

-- Kernel-reducibility smoke test: the whole per-design Boolean discharges
-- with `decide` now that the `.reg` arm avoids `wireNumber?`.
example :
    moduleEmitOkB ⟨"t", [⟨"a", 4, 0, .reg 4 "a"⟩], [], []⟩ = true := by decide

/-! ## Default-shape projections

The remaining lemmas fix the default witness shape (`blockSize = 128`,
`chunkLeaves = 16 = 2 ^ 4`) and connect the three faces of the construction
through the shared flattening state. -/

/-- The flattening state underlying `d.toProgram` (default `blockSize`),
shared with `d.toIndexedWires` by `toIndexedWires_eq_flattenModule`. -/
def _root_.Loom.Hw.Design.flattenStOf (d : Loom.Hw.Design) : FlattenSt :=
  ((flattenModule (Compile.compile d) 128).run {}).2

/-- The missing `toProgram` projection: the wire rope is the shaped view of
the flat traversal output. -/
theorem toProgram_wires (d : Loom.Hw.Design) (blockSize chunkLeaves : Nat) :
    (d.toProgram blockSize chunkLeaves).wires =
      shapeWireRope blockSize chunkLeaves
        ((((flattenModule (Compile.compile d) blockSize).run {}).2).wires.toList) :=
  rfl

theorem toProgram_wires_shaped (d : Loom.Hw.Design) :
    (d.toProgram).wires =
      balancedRope ((listChunks (2 ^ 4)
        ((listChunks 128 d.flattenStOf.wires.toList).map Rope.leaf)).map
        balancedRope) := rfl

theorem indexedsOf_shaped (d : Loom.Hw.Design) :
    d.indexedsOf =
      balancedRope ((listChunks (2 ^ 4)
        ((listChunks 128 d.toIndexedWires).map Rope.leaf)).map
        balancedRope) := rfl

theorem tableOf_shaped (d : Loom.Hw.Design) :
    d.tableOf =
      { leafSize := 128,
        leafCount := (d.toIndexedWires.length + 128 - 1) / 128 } := rfl

/-- `toIndexedWires_eq_flattenModule` at the default shape, phrased through
the shared state. -/
theorem toIndexedWires_eq (d : Loom.Hw.Design) :
    d.toIndexedWires =
      d.flattenStOf.wires.toList.zipIdx.map fun (wire, number) =>
        { number, width := wire.width, rhs := indexedRhsOf wire.rhs } :=
  toIndexedWires_eq_flattenModule d 128

/-- Element `i` of the indexed view is the numbered translation of element
`i` of the flat wire list. -/
theorem toIndexedWires_getElem? (d : Loom.Hw.Design) (i : Nat) :
    d.toIndexedWires[i]? =
      (d.flattenStOf.wires.toList[i]?).map fun wire =>
        { number := i, width := wire.width, rhs := indexedRhsOf wire.rhs } := by
  rw [toIndexedWires_eq d, List.getElem?_map, List.getElem?_zipIdx]
  cases d.flattenStOf.wires.toList[i]? <;> simp

theorem toIndexedWires_length (d : Loom.Hw.Design) :
    d.toIndexedWires.length = d.flattenStOf.wires.toList.length := by
  rw [toIndexedWires_eq d, List.length_map, List.length_zipIdx]

/-- Indexed lookup on the default shape answers with the stored wire. -/
theorem lookupIndexed?_toIndexedWires (d : Loom.Hw.Design)
    {n : Nat} {wire : Symbolic.IndexedWire}
    (found : d.toIndexedWires[n]? = some wire) :
    Symbolic.lookupIndexed? d.indexedsOf d.tableOf n = some wire := by
  have hnum : ∀ (i : Nat) (w : Symbolic.IndexedWire),
      d.toIndexedWires[i]? = some w → w.number = i := by
    intro i w hw
    rw [toIndexedWires_getElem?] at hw
    obtain ⟨raw, -, hmap⟩ := Option.map_eq_some_iff.mp hw
    subst hmap
    rfl
  rw [indexedsOf_shaped, tableOf_shaped]
  exact lookupIndexed?_shaped 4 128 (by omega) d.toIndexedWires hnum n wire
    found

/-- Raw lookup on the constructed program answers with the flat list's
wire. -/
theorem lookupRaw?_toProgram (d : Loom.Hw.Design) {n : Nat} {wire : Wire}
    (found : d.flattenStOf.wires.toList[n]? = some wire) :
    Symbolic.lookupRaw? (d.toProgram).wires d.tableOf n = some wire := by
  rw [toProgram_wires_shaped, tableOf_shaped, toIndexedWires_length]
  exact lookupRaw?_shaped 4 128 (by omega) d.flattenStOf.wires.toList n wire
    found

/-- `find?` metadata transfer from module registers to program registers. -/
theorem toProgram_regs_find? (d : Loom.Hw.Design) (name : String) :
    ((d.toProgram).regs.find? (fun c => c.name == name)).map
        (fun c => (c.name, c.width)) =
      ((Compile.compile d).regs.find? (fun r => r.name == name)).map
        (fun r => (r.name, r.width)) := by
  rw [toProgram_regs d 128 16]
  exact flattenRegs_find?_meta (Compile.compile d).regs {} name

/-- `find?` metadata transfer from module memories to program memories. -/
theorem toProgram_mems_find? (d : Loom.Hw.Design) (name : String) :
    ((d.toProgram).mems.find? (fun c => c.name == name)).map
        (fun c => (c.name, c.addrWidth, c.dataWidth)) =
      ((Compile.compile d).mems.find? (fun mm => mm.name == name)).map
        (fun mm => (mm.name, mm.addrWidth, mm.dataWidth)) := by
  rw [toProgram_mems d 128 16]
  exact flattenMems_find?_meta (Compile.compile d).mems 128
    ((flattenRegs (Compile.compile d).regs).run {}).2 name

/-! ## Operand resolution: `OperandOk` → `refWidthBefore?` -/

/-- A resolvable flatten-state operand resolves in the constructed witness at
the same width. -/
theorem refWidthBefore?_of_operandOk (d : Loom.Hw.Design)
    (wf : d.flattenStOf.WF (Compile.compile d).regs (Compile.compile d).mems)
    {i : Nat} {name : String} {w' : Nat}
    (ok : OperandOk (Compile.compile d).regs d.flattenStOf.wires i name w') :
    Symbolic.refWidthBefore? d.toProgram d.indexedsOf d.tableOf i
      (operandRef name) = some w' := by
  cases ok with
  | inl wireCase =>
      obtain ⟨m, wire, hnum, hname, hlt, hfound, hwidth⟩ := wireCase
      have hop : operandRef name = .wire m := by
        simp [operandRef, hnum]
      have hlist : d.flattenStOf.wires.toList[m]? = some wire := by
        rw [Array.getElem?_toList]; exact hfound
      have hidxfound : d.toIndexedWires[m]? =
          some ⟨m, wire.width, indexedRhsOf wire.rhs⟩ := by
        rw [toIndexedWires_getElem?, hlist]; rfl
      have hidx := lookupIndexed?_toIndexedWires d hidxfound
      have hraw := lookupRaw?_toProgram d hlist
      have hrawname : wire.name = Symbolic.wireName m := wf.names m wire hfound
      rw [hop]
      simp [Symbolic.refWidthBefore?, hlt, hidx, hraw, guard,
        Symbolic.Ref.render, hrawname, hwidth]
  | inr regCase =>
      obtain ⟨hnum, r, hfind, hwidth⟩ := regCase
      have hop : operandRef name = .reg name := by
        simp [operandRef, hnum]
      have hmeta := toProgram_regs_find? d name
      rw [hfind] at hmeta
      cases hfindP : (d.toProgram).regs.find? (fun c => c.name == name) with
      | none => rw [hfindP] at hmeta; exact absurd hmeta (by simp)
      | some c =>
          rw [hfindP] at hmeta
          simp only [Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at hmeta
          rw [hop]
          simp [Symbolic.refWidthBefore?, hnum, hfindP, guard, hmeta.2, hwidth]

/-! ## The `RhsOk` → `indexedRhsWellFormed` bridge -/

/-- **The core bridge**: each emitted right-hand side's flatten-state
obligations imply the release checker's per-node type check on the
translated node. -/
theorem indexedRhsWellFormed_of_rhsOk (d : Loom.Hw.Design)
    (wf : d.flattenStOf.WF (Compile.compile d).regs (Compile.compile d).mems)
    {i : Nat} {rhs : Rhs} {w : Nat}
    (ok : RhsOk (Compile.compile d).regs (Compile.compile d).mems
      d.flattenStOf.wires i rhs w) :
    Symbolic.indexedRhsWellFormed d.toProgram d.indexedsOf d.tableOf i w
      (indexedRhsOf rhs) = true := by
  cases rhs with
  | lit lw v =>
      have hlw : lw = w := ok
      subst hlw
      simp [indexedRhsOf, Symbolic.indexedRhsWellFormed]
  | ident value =>
      obtain ⟨w', op⟩ := ok
      simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
        refWidthBefore?_of_operandOk d wf op]
  | memRead mem addr =>
      obtain ⟨header, hfind, hdata, hop⟩ := ok
      have haddr := refWidthBefore?_of_operandOk d wf hop
      have hmeta := toProgram_mems_find? d mem
      rw [hfind] at hmeta
      cases hfindP : (d.toProgram).mems.find? (fun c => c.name == mem) with
      | none => rw [hfindP] at hmeta; exact absurd hmeta (by simp)
      | some c =>
          rw [hfindP] at hmeta
          simp only [Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at hmeta
          simp [indexedRhsOf, Symbolic.indexedRhsWellFormed, hfindP, haddr,
            hmeta.2.1, hmeta.2.2, hdata]
  | slice value hi lo =>
      obtain ⟨⟨w', op⟩, hle, heq⟩ := ok
      simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
        refWidthBefore?_of_operandOk d wf op, hle, heq]
  | not value =>
      simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
        refWidthBefore?_of_operandOk d wf ok]
  | bin op left right =>
      cases op <;> first
        | simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
            refWidthBefore?_of_operandOk d wf ok.1,
            refWidthBefore?_of_operandOk d wf ok.2]
        | (obtain ⟨hw, w', hl, hr⟩ := ok
           subst hw
           simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
             refWidthBefore?_of_operandOk d wf hl,
             refWidthBefore?_of_operandOk d wf hr])
  | slt left right =>
      obtain ⟨hw, w', hl, hr⟩ := ok
      subst hw
      simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
        refWidthBefore?_of_operandOk d wf hl,
        refWidthBefore?_of_operandOk d wf hr]
  | mux c y n =>
      obtain ⟨hc, hy, hn⟩ := ok
      simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
        refWidthBefore?_of_operandOk d wf hc,
        refWidthBefore?_of_operandOk d wf hy,
        refWidthBefore?_of_operandOk d wf hn]
  | sext amount value signBit =>
      obtain ⟨iw, op, hsign, hamount, hlt⟩ := ok
      simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
        refWidthBefore?_of_operandOk d wf op, hsign, hamount, hlt]

/-! ## The `matchesRaw` bridge -/

/-- Operand canonicality: a resolvable operand's translated reference renders
back to the operand string. -/
theorem operandRef_render {regs : List RegDef} {wires : Array Wire}
    {bound : Nat} {name : String} {w : Nat}
    (ok : OperandOk regs wires bound name w) :
    (operandRef name).render = name := by
  cases ok with
  | inl wireCase =>
      obtain ⟨m, wire, hnum, hname, -, -, -⟩ := wireCase
      subst hname
      simp [operandRef, wireNumber?_wireName, Symbolic.Ref.render]
  | inr regCase =>
      simp [operandRef, regCase.1, Symbolic.Ref.render]

/-- A flat wire whose operands are resolvable matches its own indexed
translation at any number. -/
theorem matchesRaw_of_rhsOk {regs : List RegDef} {mems : List MemDef}
    {wires : Array Wire} {bound : Nat} (i : Nat) (raw : Wire)
    (ok : RhsOk regs mems wires bound raw.rhs raw.width) :
    Symbolic.IndexedWire.matchesRaw i raw
      { number := i, width := raw.width, rhs := indexedRhsOf raw.rhs } =
      true := by
  obtain ⟨w, name, rhs⟩ := raw
  cases rhs with
  | lit lw v => simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf]
  | ident value =>
      obtain ⟨w', op⟩ := ok
      simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
        operandRef_render op]
  | memRead mem addr =>
      obtain ⟨header, -, -, op⟩ := ok
      simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
        operandRef_render op]
  | slice value hi lo =>
      obtain ⟨⟨w', op⟩, -, -⟩ := ok
      simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
        operandRef_render op]
  | not value =>
      simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
        operandRef_render ok]
  | bin op left right =>
      cases op <;> first
        | simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
            operandRef_render ok.1, operandRef_render ok.2]
        | (obtain ⟨-, w', hl, hr⟩ := ok
           simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
             operandRef_render hl, operandRef_render hr])
  | slt left right =>
      obtain ⟨-, w', hl, hr⟩ := ok
      simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
        operandRef_render hl, operandRef_render hr]
  | mux c y n =>
      obtain ⟨hc, hy, hn⟩ := ok
      simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
        operandRef_render hc, operandRef_render hy, operandRef_render hn]
  | sext amount value signBit =>
      obtain ⟨iw, op, -, -, -⟩ := ok
      simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
        operandRef_render op]

/-! ## Assembly: the two wire-graph conjuncts -/

/-- Per-element well-formedness of the indexed view. -/
theorem toProgram_indexedWireWellFormedAt (d : Loom.Hw.Design)
    (wf : d.flattenStOf.WF (Compile.compile d).regs (Compile.compile d).mems)
    (i : Nat) (wire : Symbolic.IndexedWire)
    (found : d.toIndexedWires[i]? = some wire) :
    Symbolic.indexedWireWellFormedAt d.toProgram d.indexedsOf d.tableOf i
      wire = true := by
  have hcorr := toIndexedWires_getElem? d i
  rw [found] at hcorr
  obtain ⟨raw, hraw, hwire⟩ := Option.map_eq_some_iff.mp hcorr.symm
  subst hwire
  have harr : d.flattenStOf.wires[i]? = some raw := by
    rw [← Array.getElem?_toList]; exact hraw
  have hrhs := indexedRhsWellFormed_of_rhsOk d wf (wf.rhsOk i raw harr)
  have hlook := lookupIndexed?_toIndexedWires d found
  simp [Symbolic.indexedWireWellFormedAt, hlook, hrhs]

/-- **Well-formedness of the constructed wire graph**, conditional on one
kernel-reducible emission Boolean per design. -/
theorem toProgram_wireWellFormed_of_check (d : Loom.Hw.Design)
    (hemit : moduleEmitOkB (Compile.compile d) = true) :
    Symbolic.IndexedRopeWellFormed d.toProgram d.indexedsOf d.tableOf 0
      d.indexedsOf := by
  have wf : d.flattenStOf.WF (Compile.compile d).regs
      (Compile.compile d).mems :=
    flattenModule_wf (Compile.compile d) 128
      (moduleEmitOkB_sound (Compile.compile d) hemit)
  show Symbolic.IndexedRopeWellFormed d.toProgram d.indexedsOf d.tableOf 0
    (balancedRope ((listChunks (2 ^ 4)
      ((listChunks 128 d.toIndexedWires).map Rope.leaf)).map balancedRope))
  exact indexedRopeWellFormed_shaped d.toProgram d.indexedsOf d.tableOf 4 128
    (by omega) d.toIndexedWires
    (fun i wire h => toProgram_indexedWireWellFormedAt d wf i wire h)

/-- **The raw/indexed match of the constructed wire graph**, conditional on
the same emission Boolean (it supplies the operand-canonicality facts through
`FlattenSt.WF`). -/
theorem toProgram_wireMatches_of_check (d : Loom.Hw.Design)
    (hemit : moduleEmitOkB (Compile.compile d) = true) :
    Symbolic.IndexedRopeMatches 0 (d.toProgram).wires d.indexedsOf := by
  have wf : d.flattenStOf.WF (Compile.compile d).regs
      (Compile.compile d).mems :=
    flattenModule_wf (Compile.compile d) 128
      (moduleEmitOkB_sound (Compile.compile d) hemit)
  show Symbolic.IndexedRopeMatches 0
    (balancedRope ((listChunks (2 ^ 4)
      ((listChunks 128 d.flattenStOf.wires.toList).map Rope.leaf)).map
      balancedRope))
    (balancedRope ((listChunks (2 ^ 4)
      ((listChunks 128 d.toIndexedWires).map Rope.leaf)).map balancedRope))
  refine indexedRopeMatches_shaped 4 128 (by omega)
    d.flattenStOf.wires.toList d.toIndexedWires
    (toIndexedWires_length d).symm ?_
  intro i raw wire hr hw
  have hcorr := toIndexedWires_getElem? d i
  rw [hw, hr] at hcorr
  simp only [Option.map_some, Option.some.injEq] at hcorr
  subst hcorr
  exact matchesRaw_of_rhsOk i raw
    (wf.rhsOk i raw (by rw [← Array.getElem?_toList]; exact hr))

end Loom.Release.SSA
