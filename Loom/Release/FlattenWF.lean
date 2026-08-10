-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ToProgram
import Loom.Release.ToProgramLemmas
import Batteries.Tactic.OpenPrivate
import Batteries.Data.Nat.Digits
import Init.Data.String.Lemmas
import Init.Data.Iterators.Lemmas

/-!
# The flatten-soundness invariant (structural half)

The commitment deferred inside `toProgram_wireWellFormed`'s docstring: what a
consistent `FlattenSt` *is*. This file states the structural (width and
naming) half — the semantic half, environment-consistency for
`toProgram_registerBehavior`, will extend these predicates rather than
replace them.

The invariant (`FlattenSt.WF`): the counter equals the number of emitted
wires; wire `i` is named canonically `n<i>`; every emitted right-hand side
references only registers declared in the module (at the operand's width,
with a name that does not collide with the wire namespace) or strictly
earlier wires at the recorded width; and every CSE-table entry points to an
already-emitted wire of the entry's width under its canonical name.

`flatten` preserves `WF` and returns a resolvable operand
(`flatten_spec`), provided the expression satisfies `ExprEmitOk` — the
per-expression obligations that `indexedRhsWellFormed` will demand of the
emitted node and that neither `Compile.DesignWF` (writes only) nor
`designReadsValidB` (register reads only) fully implies: register reads
resolve in `regs`, memory reads resolve in `mems` at both widths, and
`slice`/`sext` sites have the positive widths the checker's arithmetic
guards assume.
-/

open private String.Slice.Pattern.Internal.memcmpStr.go from
  Init.Data.String.Pattern.Basic

namespace Loom.Release.SSA

open Loom.Emit.MicroVerilog

/-! ## Operand and right-hand-side obligations -/

/-- `name` resolves at width `w` against the wires emitted so far: it is the
canonical name of an already-numbered wire below `bound` at width `w`, or a
register declared at width `w` whose name is outside the wire namespace. -/
def OperandOk (regs : List RegDef) (wires : Array Wire) (bound : Nat)
    (name : String) (w : Nat) : Prop :=
  (∃ m wire, Symbolic.wireNumber? name = some m ∧ name = Symbolic.wireName m ∧
    m < bound ∧ wires[m]? = some wire ∧ wire.width = w) ∨
  (Symbolic.wireNumber? name = none ∧
    ∃ r, regs.find? (fun c => c.name == name) = some r ∧ r.width = w)

/-- The exact obligations `indexedRhsWellFormed` imposes on one emitted
right-hand side at result width `w`, stated against the flattening state
rather than the finished witness. -/
def RhsOk (regs : List RegDef) (mems : List MemDef) (wires : Array Wire)
    (bound : Nat) : Rhs → Nat → Prop
  | .lit literalWidth _, w => literalWidth = w
  | .ident value, _ => ∃ w', OperandOk regs wires bound value w'
  | .memRead mem addr, w =>
      ∃ header, mems.find? (fun c => c.name == mem) = some header ∧
        header.dataWidth = w ∧
        OperandOk regs wires bound addr header.addrWidth
  | .slice value hi lo, w =>
      (∃ w', OperandOk regs wires bound value w') ∧ lo ≤ hi ∧ hi + 1 - lo = w
  | .not value, w => OperandOk regs wires bound value w
  | .bin op left right, w =>
      match op with
      | .and | .or | .xor | .add | .sub | .mul | .shl | .shr =>
          OperandOk regs wires bound left w ∧ OperandOk regs wires bound right w
      | .eq | .ult =>
          w = 1 ∧ ∃ w', OperandOk regs wires bound left w' ∧
            OperandOk regs wires bound right w'
  | .slt left right, w =>
      w = 1 ∧ ∃ w', OperandOk regs wires bound left w' ∧
        OperandOk regs wires bound right w'
  | .mux condition yes no, w =>
      OperandOk regs wires bound condition 1 ∧
        OperandOk regs wires bound yes w ∧ OperandOk regs wires bound no w
  | .sext amount value signBit, w =>
      ∃ inputWidth, OperandOk regs wires bound value inputWidth ∧
        signBit + 1 = inputWidth ∧ inputWidth + amount = w ∧ inputWidth < w

/-! ## The state invariant -/

/-- A consistent flattening state (structural half). -/
structure FlattenSt.WF (regs : List RegDef) (mems : List MemDef)
    (st : FlattenSt) : Prop where
  sizeEq : st.next = st.wires.size
  names : ∀ (i : Nat) (wire : Wire),
    st.wires[i]? = some wire → wire.name = Symbolic.wireName i
  rhsOk : ∀ (i : Nat) (wire : Wire), st.wires[i]? = some wire →
    RhsOk regs mems st.wires i wire.rhs wire.width
  cse : ∀ (w : Nat) (key name : String), st.cse[(w, key)]? = some name →
    ∃ (m : Nat) (wire : Wire), name = Symbolic.wireName m ∧ m < st.next ∧
      st.wires[m]? = some wire ∧ wire.width = w

/-- The empty state is consistent. -/
theorem FlattenSt.WF.empty (regs : List RegDef) (mems : List MemDef) :
    FlattenSt.WF regs mems {} where
  sizeEq := rfl
  names := by intro i wire found; simp at found
  rhsOk := by intro i wire found; simp at found
  cse := by intro w key name found; simp at found

/-- Flattening only appends: earlier wires persist at their indices and the
counter is monotone. -/
def FlattenSt.Extends (st st' : FlattenSt) : Prop :=
  st.next ≤ st'.next ∧
    ∀ (i : Nat) (wire : Wire),
      st.wires[i]? = some wire → st'.wires[i]? = some wire

theorem FlattenSt.Extends.rfl (st : FlattenSt) : st.Extends st :=
  ⟨Nat.le_refl _, fun _ _ found => found⟩

theorem FlattenSt.Extends.trans {a b c : FlattenSt}
    (ab : a.Extends b) (bc : b.Extends c) : a.Extends c :=
  ⟨Nat.le_trans ab.1 bc.1, fun i wire found => bc.2 i wire (ab.2 i wire found)⟩

/-! ## Monotonicity: obligations persist as wires are appended -/

theorem OperandOk.mono {regs : List RegDef} {wires wires' : Array Wire}
    {bound bound' : Nat} {name : String} {w : Nat}
    (boundLe : bound ≤ bound')
    (persist : ∀ (i : Nat) (wire : Wire),
      wires[i]? = some wire → wires'[i]? = some wire)
    (ok : OperandOk regs wires bound name w) :
    OperandOk regs wires' bound' name w := by
  cases ok with
  | inl wireCase =>
      obtain ⟨m, wire, numberEq, nameEq, mLt, found, widthEq⟩ := wireCase
      exact .inl ⟨m, wire, numberEq, nameEq, Nat.lt_of_lt_of_le mLt boundLe,
        persist m wire found, widthEq⟩
  | inr regCase => exact .inr regCase

theorem RhsOk.mono {regs : List RegDef} {mems : List MemDef}
    {wires wires' : Array Wire} {bound bound' : Nat} {rhs : Rhs} {w : Nat}
    (boundLe : bound ≤ bound')
    (persist : ∀ (i : Nat) (wire : Wire),
      wires[i]? = some wire → wires'[i]? = some wire)
    (ok : RhsOk regs mems wires bound rhs w) :
    RhsOk regs mems wires' bound' rhs w := by
  cases rhs with
  | lit literalWidth value => exact ok
  | ident value =>
      obtain ⟨w', operand⟩ := ok
      exact ⟨w', operand.mono boundLe persist⟩
  | memRead mem addr =>
      obtain ⟨header, found, dataEq, operand⟩ := ok
      exact ⟨header, found, dataEq, operand.mono boundLe persist⟩
  | slice value hi lo =>
      obtain ⟨⟨w', operand⟩, loLe, widthEq⟩ := ok
      exact ⟨⟨w', operand.mono boundLe persist⟩, loLe, widthEq⟩
  | not value => exact OperandOk.mono boundLe persist ok
  | bin op left right =>
      cases op <;>
        first
          | exact ⟨ok.1.mono boundLe persist, ok.2.mono boundLe persist⟩
          | exact ⟨ok.1, ok.2.choose,
              (ok.2.choose_spec.1).mono boundLe persist,
              (ok.2.choose_spec.2).mono boundLe persist⟩
  | slt left right =>
      exact ⟨ok.1, ok.2.choose, (ok.2.choose_spec.1).mono boundLe persist,
        (ok.2.choose_spec.2).mono boundLe persist⟩
  | mux condition yes no =>
      exact ⟨ok.1.mono boundLe persist, ok.2.1.mono boundLe persist,
        ok.2.2.mono boundLe persist⟩
  | sext amount value signBit =>
      obtain ⟨inputWidth, operand, signEq, amountEq, inputLt⟩ := ok
      exact ⟨inputWidth, operand.mono boundLe persist, signEq, amountEq, inputLt⟩

/-! ## Per-expression emission obligations -/

/-- Everything the flattened form of an expression needs from its context:
register reads resolve in `regs` at their intrinsic width outside the wire
namespace, memory reads resolve in `mems` at both widths, and the
`slice`/`sext` cases have the positive widths whose arithmetic the
release checker's guards assume. Neither `Compile.DesignWF` (writes only)
nor `designReadsValidB` (register reads only) implies all of this; the
design-level decidable check that discharges it for `Compile.compile d` is
introduced with the assembly of `toProgram_wireWellFormed`. -/
def ExprEmitOk (regs : List RegDef) (mems : List MemDef) :
    {w : Nat} → Emit.MicroVerilog.Expr w → Prop
  | w, .reg _ name =>
      Symbolic.wireNumber? name = none ∧
        ∃ r, regs.find? (fun c => c.name == name) = some r ∧ r.width = w
  | _, .lit _ => True
  | dw, @Emit.MicroVerilog.Expr.memRead _ mem aw addr =>
      (∃ header, mems.find? (fun c => c.name == mem) = some header ∧
        header.addrWidth = aw ∧ header.dataWidth = dw) ∧
      ExprEmitOk regs mems addr
  | _, .and a b | _, .or a b | _, .xor a b | _, .add a b | _, .sub a b
  | _, .mul a b
  | _, .shl a b | _, .shr a b | _, .eq a b | _, .ult a b | _, .slt a b =>
      ExprEmitOk regs mems a ∧ ExprEmitOk regs mems b
  | _, .not a => ExprEmitOk regs mems a
  | _, .mux c t f =>
      ExprEmitOk regs mems c ∧ ExprEmitOk regs mems t ∧ ExprEmitOk regs mems f
  | _, @Emit.MicroVerilog.Expr.slice _ a _ w' => 0 < w' ∧ ExprEmitOk regs mems a
  | _, .zext a _ => ExprEmitOk regs mems a
  | w', @Emit.MicroVerilog.Expr.sext w a _ =>
      (w < w' → 0 < w) ∧ (w' < w → 0 < w') ∧ ExprEmitOk regs mems a

/-- Emission obligations for every expression a module flattens, in the
printer traversal. -/
def ModuleEmitOk (m : Module) : Prop :=
  (∀ r ∈ m.regs, ExprEmitOk m.regs m.mems r.next) ∧
  (∀ mm ∈ m.mems, ∀ p ∈ mm.wrPorts,
    ExprEmitOk m.regs m.mems p.en ∧ ExprEmitOk m.regs m.mems p.addr ∧
      ExprEmitOk m.regs m.mems p.data) ∧
  (∀ o ∈ m.outs, ExprEmitOk m.regs m.mems o.val)

/-! ## Wire-name facts

`freshWire` names its wires `s!"n{next}"` while the invariant speaks of
`Symbolic.wireName` and `Symbolic.wireNumber?`. The two lemmas below close
that gap: the canonical name printed for `m` is exactly `"n" ++ toString m`,
and decoding a canonical name recovers its number.
-/

section WireName

open String Std

/-! ### Generic bridge: slice folds as list folds over the copied string -/

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

private theorem slice_isEmpty_false {sl : String.Slice} (h : sl.copy ≠ "") :
    sl.isEmpty = false := by
  show (sl.utf8ByteSize == 0) = false
  have he : sl.utf8ByteSize = sl.copy.utf8ByteSize := by
    rw [String.Slice.utf8ByteSize_copy, String.Slice.utf8ByteSize_eq]
  rw [he]
  simp only [beq_eq_false_iff_ne, ne_eq, String.utf8ByteSize_eq_zero_iff]
  exact h

/-! ### `("n" ++ t).startsWith "n"` -/

private theorem byte_key (t : String) (p q : Pos.Raw) (hp : p < ("n" ++ t).rawEndPos)
    (hq : q < "n".rawEndPos) (hp0 : p.byteIdx = 0) (hq0 : q.byteIdx = 0) :
    (("n" ++ t).getUTF8Byte p hp == "n".getUTF8Byte q hq) = true := by
  obtain ⟨pb⟩ := p
  obtain ⟨qb⟩ := q
  subst hp0
  subst hq0
  simp only [String.getUTF8Byte, String.toByteArray_append]
  rw [ByteArray.getElem_append_left (show (0:Nat) < "n".toByteArray.size by decide)]
  exact beq_self_eq_true _

private theorem go_one (lhs rhs : String) (lstart rstart : Pos.Raw)
    (h1 : (⟨1⟩ : Pos.Raw).offsetBy lstart ≤ lhs.rawEndPos)
    (h2 : (⟨1⟩ : Pos.Raw).offsetBy rstart ≤ rhs.rawEndPos)
    (hb : ∀ hpl hpr,
      (lhs.getUTF8Byte (Pos.Raw.offsetBy 0 lstart) hpl ==
        rhs.getUTF8Byte (Pos.Raw.offsetBy 0 rstart) hpr) = true) :
    String.Slice.Pattern.Internal.memcmpStr.go lhs rhs lstart rstart ⟨1⟩ h1 h2 0 = true := by
  rw [String.Slice.Pattern.Internal.memcmpStr.go.eq_def]
  rw [dif_pos (show (0 : Pos.Raw) < (⟨1⟩ : Pos.Raw) by decide)]
  simp only [hb, if_pos]
  rw [String.Slice.Pattern.Internal.memcmpStr.go.eq_def]
  rw [dif_neg (show ¬ ((0 : Pos.Raw).inc < (⟨1⟩ : Pos.Raw)) by decide)]

private theorem startsWith_n (t : String) : ("n" ++ t).startsWith "n" = true := by
  show String.Slice.Pattern.ForwardSliceSearcher.startsWith "n".toSlice ("n" ++ t).toSlice = true
  rw [String.Slice.Pattern.ForwardSliceSearcher.startsWith.eq_def]
  rw [dif_pos (by
    rw [String.utf8ByteSize_toSlice, String.utf8ByteSize_toSlice, String.utf8ByteSize_append]
    have h1 : "n".utf8ByteSize = 1 := rfl
    omega)]
  rw [String.Slice.Pattern.Internal.memcmpSlice]
  rw [String.Slice.Pattern.Internal.memcmpStr.eq_def]
  exact go_one _ _ _ _ _ _ (fun hpl hpr => byte_key t _ _ hpl hpr rfl rfl)

/-! ### `("n" ++ t).drop 1` -/

private theorem nextn_one {sl : String.Slice} (p : sl.Pos) (h : p ≠ sl.endPos) :
    p.nextn 1 = p.next h := by
  simp [String.Slice.Pos.nextn, h]

private theorem drop_one_copy (t : String) : (("n" ++ t).drop 1).copy = t := by
  have hcopy : ("n" ++ t).toSlice.copy = "n" ++ t := String.copy_toSlice
  have hne : ("n" ++ t).toSlice.startPos ≠ ("n" ++ t).toSlice.endPos := by
    intro h
    have h1 := (("n" ++ t).toSlice.splits_startPos).eq_endPos_iff.mp h
    rw [hcopy] at h1
    have h2 := congrArg String.toList (String.append_eq_empty_iff.mp h1).1
    simp at h2
  have hsplit := ("n" ++ t).toSlice.startPos.splits_next_right hne
  have hstart := ("n" ++ t).toSlice.splits_startPos
  have heq := hstart.eq hsplit
  rw [hcopy] at heq
  have h2 := congrArg String.toList heq.2
  rw [String.toList_append, String.toList_append, String.toList_singleton,
    show "n".toList = ['n'] from rfl] at h2
  have hrest : ((("n" ++ t).toSlice).sliceFrom
      (("n" ++ t).toSlice.startPos.next hne)).copy.toList = t.toList :=
    (List.cons.injEq _ _ _ _ ▸ h2).2.symm
  show ((("n" ++ t).toSlice).sliceFrom (("n" ++ t).toSlice.startPos.nextn 1)).copy = t
  rw [nextn_one _ hne]
  exact String.toList_inj.mp hrest

/-! ### Decimal digit arithmetic -/

private theorem toDigitsCore_fuel {b : Nat} (hb : 1 < b) :
    ∀ (f₁ : Nat), ∀ (f₂ n : Nat) (cs : List Char), n < b ^ f₁ → n < b ^ f₂ →
      0 < f₁ → 0 < f₂ → Nat.toDigitsCore b f₁ n cs = Nat.toDigitsCore b f₂ n cs := by
  intro f₁
  induction f₁ with
  | zero => intro _ _ _ _ _ h; exact absurd h (by omega)
  | succ k ih =>
    intro f₂ n cs h₁ h₂ _ hf₂
    cases f₂ with
    | zero => exact absurd hf₂ (by omega)
    | succ j =>
      rw [Nat.toDigitsCore, Nat.toDigitsCore]
      by_cases h : n / b = 0
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
        have hbpos : 0 < b := by omega
        have hnb₁ : n / b < b ^ k := by
          rw [Nat.div_lt_iff_lt_mul hbpos]
          calc n < b ^ (k+1) := h₁
            _ = b ^ k * b := by rw [Nat.pow_succ]
        have hnb₂ : n / b < b ^ j := by
          rw [Nat.div_lt_iff_lt_mul hbpos]
          calc n < b ^ (j+1) := h₂
            _ = b ^ j * b := by rw [Nat.pow_succ]
        cases k with
        | zero =>
          exact absurd (Nat.div_eq_of_lt
            (by rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] at h₁; exact h₁)) h
        | succ k' =>
          cases j with
          | zero =>
            exact absurd (Nat.div_eq_of_lt
              (by rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] at h₂; exact h₂)) h
          | succ j' => exact ih _ _ _ hnb₁ hnb₂ (by omega) (by omega)

private theorem toDigitsCore_log2 (m : Nat) :
    Nat.toDigitsCore 10 (m.log2 + 1) m [] = Nat.toDigits 10 m := by
  rw [Nat.toDigits]
  apply toDigitsCore_fuel (by omega)
  · calc m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
      _ ≤ 10 ^ (m.log2 + 1) := Nat.pow_le_pow_left (by omega) _
  · calc m < 2 ^ m := Nat.lt_two_pow_self
      _ ≤ 10 ^ m := Nat.pow_le_pow_left (by omega) _
      _ ≤ 10 ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  · omega
  · omega

private theorem toString_eq_ofList_toDigits (m : Nat) :
    (toString m : String) = String.ofList (Nat.toDigits 10 m) := by
  show Nat.repr m = _
  rw [Nat.repr.eq_def]

private theorem digitChar_ne_underscore {d : Nat} (h : d < 10) : Nat.digitChar d ≠ '_' := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide

private theorem toNat_digitChar {d : Nat} (h : d < 10) :
    (Nat.digitChar d).toNat - '0'.toNat = d := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide

private theorem toDigits_ne_nil (m : Nat) : Nat.toDigits 10 m ≠ [] := by
  by_cases h : m < 10
  · rw [Nat.toDigits_of_lt_base h]; simp
  · have h10 : 0 < m / 10 := Nat.div_pos (by omega) (by omega)
    have hdec := Nat.toDigits_append_toDigits (b := 10) (n := m / 10) (d := m % 10)
      (by omega) h10 (by omega)
    have hn : 10 * (m / 10) + m % 10 = m := by omega
    rw [hn] at hdec
    rw [← hdec, Nat.toDigits_of_lt_base (by omega : m % 10 < 10)]
    simp

private theorem foldl_toDigits (step : Nat → Char → Nat)
    (hstep : ∀ a c, step a c = if c = '_' then a else a * 10 + (c.toNat - '0'.toNat)) :
    ∀ (n : Nat), ∀ (a : Nat),
      List.foldl step a (Nat.toDigits 10 n) =
        a * 10 ^ (Nat.toDigits 10 n).length + n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a
    by_cases h : n < 10
    · rw [Nat.toDigits_of_lt_base h]
      simp only [List.foldl_cons, List.foldl_nil, List.length_cons, List.length_nil]
      rw [hstep, if_neg (digitChar_ne_underscore h), toNat_digitChar h]
    · have h10 : 0 < n / 10 := Nat.div_pos (by omega) (by omega)
      have hdec := Nat.toDigits_append_toDigits (b := 10) (n := n / 10) (d := n % 10)
        (by omega) h10 (by omega)
      have hn : 10 * (n / 10) + n % 10 = n := by omega
      rw [hn] at hdec
      rw [← hdec, List.foldl_append, ih (n / 10) (by omega) a,
        Nat.toDigits_of_lt_base (by omega : n % 10 < 10)]
      simp only [List.foldl_cons, List.foldl_nil, List.length_append, List.length_cons,
        List.length_nil]
      rw [hstep, if_neg (digitChar_ne_underscore (by omega)), toNat_digitChar (by omega)]
      have hpow : 10 ^ ((Nat.toDigits 10 (n / 10)).length + (0 + 1)) =
          10 ^ (Nat.toDigits 10 (n / 10)).length * 10 := by
        rw [Nat.zero_add, Nat.pow_succ]
      rw [hpow]
      generalize (10 : Nat) ^ (Nat.toDigits 10 (n / 10)).length = X
      have hassoc : a * (X * 10) = a * X * 10 := by rw [Nat.mul_assoc]
      rw [hassoc]
      generalize a * X = Y
      omega

private theorem foldl_isNat_digits
    (F : Bool × Bool × Bool × Bool → Char → Bool × Bool × Bool × Bool)
    (hF : ∀ b₁ b₂ b₃ c, c.isDigit = true → F (b₁, b₂, b₃, true) c = (false, false, true, true)) :
    ∀ (l : List Char), (∀ c ∈ l, c.isDigit = true) → l ≠ [] →
      ∀ b₁ b₂ b₃, List.foldl F (b₁, b₂, b₃, true) l = (false, false, true, true) := by
  intro l
  induction l with
  | nil => intro _ h; exact absurd rfl h
  | cons c cs ih =>
    intro hd _ b₁ b₂ b₃
    rw [List.foldl_cons, hF b₁ b₂ b₃ c (hd c List.mem_cons_self)]
    cases cs with
    | nil => rfl
    | cons c' cs' =>
      exact ih (fun x hx => hd x (List.mem_cons_of_mem _ hx)) (by simp) false false true

/-! ### The two main theorems -/

theorem wireName_eq_append (m : Nat) :
    Loom.Release.Symbolic.wireName m = "n" ++ toString m := by
  rw [Loom.Release.Symbolic.wireName, toDigitsCore_log2, toString_eq_ofList_toDigits]

theorem wireNumber?_wireName (m : Nat) :
    Loom.Release.Symbolic.wireNumber? (Loom.Release.Symbolic.wireName m) = some m := by
  have hw : Loom.Release.Symbolic.wireName m =
      "n" ++ String.ofList (Nat.toDigits 10 m) := by
    rw [Loom.Release.Symbolic.wireName, toDigitsCore_log2]
  rw [hw]
  have hDne : String.ofList (Nat.toDigits 10 m) ≠ "" := by
    rw [ne_eq, String.ofList_eq_empty_iff]
    exact toDigits_ne_nil m
  have hcopy : (("n" ++ String.ofList (Nat.toDigits 10 m)).drop 1).copy =
      String.ofList (Nat.toDigits 10 m) := drop_one_copy _
  have hisNat : (("n" ++ String.ofList (Nat.toDigits 10 m)).drop 1).isNat = true := by
    rw [String.Slice.isNat.eq_def]
    rw [slice_isEmpty_false (by rw [hcopy]; exact hDne)]
    simp only [Bool.false_eq_true, if_false]
    rw [slice_foldl_eq, hcopy, String.toList_ofList]
    rw [foldl_isNat_digits _ ?hF _ ?hdig (toDigits_ne_nil m)]
    case _ => rfl
    case hF =>
      intro b₁ b₂ b₃ c hc
      have hcu : ¬ (c = '_') := by
        intro h
        subst h
        exact absurd hc (by decide)
      simp [hc, hcu]
    case hdig =>
      intro c hc
      exact Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc
  rw [Loom.Release.Symbolic.wireNumber?]
  simp only [startsWith_n, guard, if_pos]
  rw [String.Slice.toNat?.eq_def, hisNat]
  simp only [if_pos]
  rw [slice_foldl_eq, hcopy, String.toList_ofList]
  rw [foldl_toDigits _ (fun a c => rfl) m 0]
  simp

end WireName

/-! ## The `freshWire` case lemma -/

/-- `freshWire` either returns a CSE hit unchanged or appends one wire and
records it in the table. -/
theorem freshWire_run (w : Nat) (key : String) (rhs : Rhs) (st : FlattenSt) :
    (freshWire w key rhs).run st =
      match st.cse[(w, key)]? with
      | some name => (name, st)
      | none => ("n" ++ toString st.next,
          { wires := st.wires.push ⟨w, "n" ++ toString st.next, rhs⟩,
            next := st.next + 1,
            cse := st.cse.insert (w, key) ("n" ++ toString st.next) }) := by
  cases h : st.cse[(w, key)]? <;>
    · simp only [freshWire, StateT.run, bind, StateT.bind, get, getThe,
        MonadStateOf.get, StateT.get, set, StateT.set, pure, StateT.pure, h]
      try rfl

/-- Pushing a wire preserves every earlier lookup. -/
theorem push_persist {wires : Array Wire} {newWire : Wire} :
    ∀ (i : Nat) (wire : Wire), wires[i]? = some wire →
      (wires.push newWire)[i]? = some wire := by
  intro i wire found
  have lt : i < wires.size := by
    cases Nat.lt_or_ge i wires.size with
    | inl h => exact h
    | inr h => rw [Array.getElem?_eq_none h] at found; cases found
  rw [Array.getElem?_push_lt lt]
  rw [Array.getElem?_eq_getElem lt] at found
  exact found

/-- `freshWire` preserves consistency and returns a resolvable operand,
provided the emitted right-hand side meets its obligations in the current
state. -/
theorem freshWire_spec {regs : List RegDef} {mems : List MemDef}
    (w : Nat) (key : String) (rhs : Rhs) (st : FlattenSt)
    (wf : st.WF regs mems) (ok : RhsOk regs mems st.wires st.next rhs w) :
    (((freshWire w key rhs).run st).2).WF regs mems ∧
    st.Extends ((freshWire w key rhs).run st).2 ∧
    OperandOk regs (((freshWire w key rhs).run st).2).wires
      (((freshWire w key rhs).run st).2).next
      ((freshWire w key rhs).run st).1 w := by
  rw [freshWire_run]
  cases hit : st.cse[(w, key)]? with
  | some name =>
      refine ⟨wf, FlattenSt.Extends.rfl st, ?_⟩
      obtain ⟨m, wire, nameEq, mLt, found, widthEq⟩ := wf.cse w key name hit
      refine .inl ⟨m, wire, ?_, nameEq, mLt, found, widthEq⟩
      rw [nameEq]; exact wireNumber?_wireName m
  | none =>
      have nameEq : "n" ++ toString st.next = Symbolic.wireName st.next :=
        (wireName_eq_append st.next).symm
      have newFound :
          (st.wires.push ⟨w, "n" ++ toString st.next, rhs⟩)[st.next]? =
            some ⟨w, "n" ++ toString st.next, rhs⟩ := by
        rw [wf.sizeEq]
        exact Array.getElem?_push_size
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨Nat.le_succ _, fun i wire found =>
        push_persist i wire found⟩, ?_⟩
      · simp [Array.size_push, wf.sizeEq]
      · intro i wire found
        rw [Array.getElem?_push] at found
        split at found
        · cases found
          rename_i isize
          rw [isize, ← wf.sizeEq]
          exact nameEq
        · exact wf.names i wire found
      · intro i wire found
        rw [Array.getElem?_push] at found
        split at found
        · cases found
          rename_i isize
          subst isize
          rw [← wf.sizeEq]
          exact ok.mono (Nat.le_refl _) push_persist
        · exact (wf.rhsOk i wire found).mono (Nat.le_refl _) push_persist
      · intro wq keyq nameq foundq
        rw [Std.HashMap.getElem?_insert] at foundq
        split at foundq
        · rename_i keysEq
          cases foundq
          have pairEq : (w, key) = (wq, keyq) := beq_iff_eq.mp keysEq
          have weq : w = wq := congrArg Prod.fst pairEq
          exact ⟨st.next, ⟨w, "n" ++ toString st.next, rhs⟩, nameEq,
            Nat.lt_succ_self _, newFound, weq⟩
        · obtain ⟨m, wire, nameEq2, mLt, found2, widthEq⟩ :=
            wf.cse wq keyq nameq foundq
          exact ⟨m, wire, nameEq2, Nat.lt_succ_of_lt mLt,
            push_persist m wire found2, widthEq⟩
      · refine .inl ⟨st.next, ⟨w, "n" ++ toString st.next, rhs⟩, ?_, nameEq,
          Nat.lt_succ_self _, newFound, rfl⟩
        rw [nameEq]; exact wireNumber?_wireName st.next

/-! ## The flatten-soundness invariant, structural half -/

/-- The three-way `sext` emission, with the width test lifted out of the
state monad. -/
theorem flatten_sext_run {w : Nat} (a : Emit.MicroVerilog.Expr w) (w' : Nat)
    (st : FlattenSt) :
    (flatten (.sext a w')).run st =
      if w' > w then
        (freshWire w'
          ("{" ++ ("{" ++ toString (w' - w) ++ "{" ++ ((flatten a).run st).1 ++
            "[" ++ toString (w - 1) ++ "]}}") ++ ", " ++
            ((flatten a).run st).1 ++ "}")
          (.sext (w' - w) ((flatten a).run st).1 (w - 1))).run
          ((flatten a).run st).2
      else if w' = w then
        (freshWire w' s!"{((flatten a).run st).1}"
          (.ident ((flatten a).run st).1)).run ((flatten a).run st).2
      else
        (freshWire w' s!"{((flatten a).run st).1}[{w' - 1}:0]"
          (.slice ((flatten a).run st).1 (w' - 1) 0)).run
          ((flatten a).run st).2 := by
  show (if w' > w then _ else if w' = w then _ else _ :
    StateM FlattenSt String).run ((flatten a).run st).2 = _
  split
  · rfl
  · split <;> rfl

/-- **The flatten-soundness invariant, structural half.** `flatten`
preserves consistency and returns a resolvable operand at the expression's
width: a `freshWire` case lemma per node, with `Extends`-transport of the
recursively obtained operand facts across sibling flattens. -/
theorem flatten_spec (regs : List RegDef) (mems : List MemDef)
    {w : Nat} (e : Emit.MicroVerilog.Expr w) (st : FlattenSt)
    (wf : st.WF regs mems) (ok : ExprEmitOk regs mems e) :
    (((flatten e).run st).2).WF regs mems ∧
    st.Extends ((flatten e).run st).2 ∧
    OperandOk regs (((flatten e).run st).2).wires
      (((flatten e).run st).2).next ((flatten e).run st).1 w := by
  induction e generalizing st with
  | @lit w v =>
      exact freshWire_spec w s!"{w}'d{v.toNat}" (.lit w v.toNat) st wf rfl
  | reg wr name => exact ⟨wf, .rfl st, .inr ok⟩
  | memRead dw mem addr ih =>
      obtain ⟨⟨header, find, addrEq, dataEq⟩, okAddr⟩ := ok
      obtain ⟨wf1, ext1, op1⟩ := ih st wf okAddr
      have fs := freshWire_spec (regs := regs) (mems := mems) dw
        s!"{mem}[{((flatten addr).run st).1}]"
        (.memRead mem ((flatten addr).run st).1) ((flatten addr).run st).2 wf1
        ⟨header, find, dataEq, by rw [addrEq]; exact op1⟩
      exact ⟨fs.1, ext1.trans fs.2.1, fs.2.2⟩
  | and a b iha ihb =>
      obtain ⟨oka, okb⟩ := ok
      obtain ⟨wf1, ext1, op1⟩ := iha st wf oka
      obtain ⟨wf2, ext2, op2⟩ := ihb ((flatten a).run st).2 wf1 okb
      have fs := freshWire_spec (regs := regs) (mems := mems) _
        s!"{((flatten a).run st).1} & {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .and ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2
        ⟨op1.mono ext2.1 ext2.2, op2⟩
      exact ⟨fs.1, (ext1.trans ext2).trans fs.2.1, fs.2.2⟩
  | or a b iha ihb =>
      obtain ⟨oka, okb⟩ := ok
      obtain ⟨wf1, ext1, op1⟩ := iha st wf oka
      obtain ⟨wf2, ext2, op2⟩ := ihb ((flatten a).run st).2 wf1 okb
      have fs := freshWire_spec (regs := regs) (mems := mems) _
        s!"{((flatten a).run st).1} | {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .or ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2
        ⟨op1.mono ext2.1 ext2.2, op2⟩
      exact ⟨fs.1, (ext1.trans ext2).trans fs.2.1, fs.2.2⟩
  | xor a b iha ihb =>
      obtain ⟨oka, okb⟩ := ok
      obtain ⟨wf1, ext1, op1⟩ := iha st wf oka
      obtain ⟨wf2, ext2, op2⟩ := ihb ((flatten a).run st).2 wf1 okb
      have fs := freshWire_spec (regs := regs) (mems := mems) _
        s!"{((flatten a).run st).1} ^ {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .xor ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2
        ⟨op1.mono ext2.1 ext2.2, op2⟩
      exact ⟨fs.1, (ext1.trans ext2).trans fs.2.1, fs.2.2⟩
  | add a b iha ihb =>
      obtain ⟨oka, okb⟩ := ok
      obtain ⟨wf1, ext1, op1⟩ := iha st wf oka
      obtain ⟨wf2, ext2, op2⟩ := ihb ((flatten a).run st).2 wf1 okb
      have fs := freshWire_spec (regs := regs) (mems := mems) _
        s!"{((flatten a).run st).1} + {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .add ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2
        ⟨op1.mono ext2.1 ext2.2, op2⟩
      exact ⟨fs.1, (ext1.trans ext2).trans fs.2.1, fs.2.2⟩
  | sub a b iha ihb =>
      obtain ⟨oka, okb⟩ := ok
      obtain ⟨wf1, ext1, op1⟩ := iha st wf oka
      obtain ⟨wf2, ext2, op2⟩ := ihb ((flatten a).run st).2 wf1 okb
      have fs := freshWire_spec (regs := regs) (mems := mems) _
        s!"{((flatten a).run st).1} - {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .sub ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2
        ⟨op1.mono ext2.1 ext2.2, op2⟩
      exact ⟨fs.1, (ext1.trans ext2).trans fs.2.1, fs.2.2⟩
  | mul a b iha ihb =>
      obtain ⟨oka, okb⟩ := ok
      obtain ⟨wf1, ext1, op1⟩ := iha st wf oka
      obtain ⟨wf2, ext2, op2⟩ := ihb ((flatten a).run st).2 wf1 okb
      have fs := freshWire_spec (regs := regs) (mems := mems) _
        s!"{((flatten a).run st).1} * {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .mul ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2
        ⟨op1.mono ext2.1 ext2.2, op2⟩
      exact ⟨fs.1, (ext1.trans ext2).trans fs.2.1, fs.2.2⟩
  | shl a b iha ihb =>
      obtain ⟨oka, okb⟩ := ok
      obtain ⟨wf1, ext1, op1⟩ := iha st wf oka
      obtain ⟨wf2, ext2, op2⟩ := ihb ((flatten a).run st).2 wf1 okb
      have fs := freshWire_spec (regs := regs) (mems := mems) _
        s!"{((flatten a).run st).1} << {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .shl ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2
        ⟨op1.mono ext2.1 ext2.2, op2⟩
      exact ⟨fs.1, (ext1.trans ext2).trans fs.2.1, fs.2.2⟩
  | shr a b iha ihb =>
      obtain ⟨oka, okb⟩ := ok
      obtain ⟨wf1, ext1, op1⟩ := iha st wf oka
      obtain ⟨wf2, ext2, op2⟩ := ihb ((flatten a).run st).2 wf1 okb
      have fs := freshWire_spec (regs := regs) (mems := mems) _
        s!"{((flatten a).run st).1} >> {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .shr ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2
        ⟨op1.mono ext2.1 ext2.2, op2⟩
      exact ⟨fs.1, (ext1.trans ext2).trans fs.2.1, fs.2.2⟩
  | eq a b iha ihb =>
      obtain ⟨oka, okb⟩ := ok
      obtain ⟨wf1, ext1, op1⟩ := iha st wf oka
      obtain ⟨wf2, ext2, op2⟩ := ihb ((flatten a).run st).2 wf1 okb
      have fs := freshWire_spec (regs := regs) (mems := mems) 1
        s!"{((flatten a).run st).1} == {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .eq ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2
        ⟨rfl, _, op1.mono ext2.1 ext2.2, op2⟩
      exact ⟨fs.1, (ext1.trans ext2).trans fs.2.1, fs.2.2⟩
  | ult a b iha ihb =>
      obtain ⟨oka, okb⟩ := ok
      obtain ⟨wf1, ext1, op1⟩ := iha st wf oka
      obtain ⟨wf2, ext2, op2⟩ := ihb ((flatten a).run st).2 wf1 okb
      have fs := freshWire_spec (regs := regs) (mems := mems) 1
        s!"{((flatten a).run st).1} < {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .ult ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2
        ⟨rfl, _, op1.mono ext2.1 ext2.2, op2⟩
      exact ⟨fs.1, (ext1.trans ext2).trans fs.2.1, fs.2.2⟩
  | slt a b iha ihb =>
      obtain ⟨oka, okb⟩ := ok
      obtain ⟨wf1, ext1, op1⟩ := iha st wf oka
      obtain ⟨wf2, ext2, op2⟩ := ihb ((flatten a).run st).2 wf1 okb
      have fs := freshWire_spec (regs := regs) (mems := mems) 1
        s!"$signed({((flatten a).run st).1}) < $signed({((flatten b).run ((flatten a).run st).2).1})"
        (.slt ((flatten a).run st).1 ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2
        ⟨rfl, _, op1.mono ext2.1 ext2.2, op2⟩
      exact ⟨fs.1, (ext1.trans ext2).trans fs.2.1, fs.2.2⟩
  | not a ih =>
      obtain ⟨wf1, ext1, op1⟩ := ih st wf ok
      have fs := freshWire_spec (regs := regs) (mems := mems) _
        s!"~{((flatten a).run st).1}" (.not ((flatten a).run st).1)
        ((flatten a).run st).2 wf1 op1
      exact ⟨fs.1, ext1.trans fs.2.1, fs.2.2⟩
  | mux c t f ihc iht ihf =>
      obtain ⟨okc, okt, okf⟩ := ok
      obtain ⟨wf1, ext1, op1⟩ := ihc st wf okc
      obtain ⟨wf2, ext2, op2⟩ := iht ((flatten c).run st).2 wf1 okt
      obtain ⟨wf3, ext3, op3⟩ :=
        ihf ((flatten t).run ((flatten c).run st).2).2 wf2 okf
      have fs := freshWire_spec (regs := regs) (mems := mems) _
        s!"{((flatten c).run st).1} ? {((flatten t).run ((flatten c).run st).2).1} : {((flatten f).run ((flatten t).run ((flatten c).run st).2).2).1}"
        (.mux ((flatten c).run st).1 ((flatten t).run ((flatten c).run st).2).1
          ((flatten f).run ((flatten t).run ((flatten c).run st).2).2).1)
        ((flatten f).run ((flatten t).run ((flatten c).run st).2).2).2 wf3
        ⟨(op1.mono ext2.1 ext2.2).mono ext3.1 ext3.2, op2.mono ext3.1 ext3.2, op3⟩
      exact ⟨fs.1, ((ext1.trans ext2).trans ext3).trans fs.2.1, fs.2.2⟩
  | slice a lo w' ih =>
      obtain ⟨wPos, oka⟩ := ok
      obtain ⟨wf1, ext1, op1⟩ := ih st wf oka
      have fs := freshWire_spec (regs := regs) (mems := mems) w'
        s!"{((flatten a).run st).1}[{lo + w' - 1}:{lo}]"
        (.slice ((flatten a).run st).1 (lo + w' - 1) lo)
        ((flatten a).run st).2 wf1
        ⟨⟨_, op1⟩, by omega, by omega⟩
      exact ⟨fs.1, ext1.trans fs.2.1, fs.2.2⟩
  | zext a w' ih =>
      obtain ⟨wf1, ext1, op1⟩ := ih st wf ok
      have fs := freshWire_spec (regs := regs) (mems := mems) w'
        s!"{((flatten a).run st).1}" (.ident ((flatten a).run st).1)
        ((flatten a).run st).2 wf1 ⟨_, op1⟩
      exact ⟨fs.1, ext1.trans fs.2.1, fs.2.2⟩
  | @sext wa a w' ih =>
      obtain ⟨posW, posW', oka⟩ := ok
      obtain ⟨wf1, ext1, op1⟩ := ih st wf oka
      rcases Nat.lt_trichotomy wa w' with hlt | heq | hgt
      · rw [flatten_sext_run, if_pos hlt]
        have waPos : 0 < wa := posW hlt
        have fs := freshWire_spec (regs := regs) (mems := mems) w'
          ("{" ++ ("{" ++ toString (w' - wa) ++ "{" ++ ((flatten a).run st).1 ++
            "[" ++ toString (wa - 1) ++ "]}}") ++ ", " ++
            ((flatten a).run st).1 ++ "}")
          (.sext (w' - wa) ((flatten a).run st).1 (wa - 1))
          ((flatten a).run st).2 wf1
          ⟨wa, op1, by omega, by omega, hlt⟩
        exact ⟨fs.1, ext1.trans fs.2.1, fs.2.2⟩
      · rw [flatten_sext_run, if_neg (by omega), if_pos heq.symm]
        have fs := freshWire_spec (regs := regs) (mems := mems) w'
          s!"{((flatten a).run st).1}" (.ident ((flatten a).run st).1)
          ((flatten a).run st).2 wf1 ⟨wa, op1⟩
        exact ⟨fs.1, ext1.trans fs.2.1, fs.2.2⟩
      · rw [flatten_sext_run, if_neg (by omega), if_neg (by omega)]
        have wPos : 0 < w' := posW' hgt
        have fs := freshWire_spec (regs := regs) (mems := mems) w'
          s!"{((flatten a).run st).1}[{w' - 1}:0]"
          (.slice ((flatten a).run st).1 (w' - 1) 0)
          ((flatten a).run st).2 wf1
          ⟨⟨wa, op1⟩, by omega, by omega⟩
        exact ⟨fs.1, ext1.trans fs.2.1, fs.2.2⟩

/-! ## The whole-module corollary -/

theorem flattenRegs_spec (regs : List RegDef) (mems : List MemDef)
    (rs : List RegDef) (st : FlattenSt) (wf : st.WF regs mems)
    (ok : ∀ r ∈ rs, ExprEmitOk regs mems r.next) :
    (((flattenRegs rs).run st).2).WF regs mems ∧
    st.Extends ((flattenRegs rs).run st).2 := by
  induction rs generalizing st with
  | nil => exact ⟨wf, .rfl st⟩
  | cons r rest ih =>
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems r.next st wf
        (ok r List.mem_cons_self)
      obtain ⟨wf2, ext2⟩ := ih ((flatten r.next).run st).2 wf1
        (fun r' mem => ok r' (List.mem_cons_of_mem _ mem))
      exact ⟨wf2, ext1.trans ext2⟩

theorem flattenWrites_spec (regs : List RegDef) (mems : List MemDef)
    {aw dw : Nat} (ports : List (WritePort aw dw)) (st : FlattenSt)
    (wf : st.WF regs mems)
    (ok : ∀ p ∈ ports, ExprEmitOk regs mems p.en ∧
      ExprEmitOk regs mems p.addr ∧ ExprEmitOk regs mems p.data) :
    (((flattenWrites ports).run st).2).WF regs mems ∧
    st.Extends ((flattenWrites ports).run st).2 := by
  induction ports generalizing st with
  | nil => exact ⟨wf, .rfl st⟩
  | cons p rest ih =>
      obtain ⟨okEn, okAddr, okData⟩ := ok p List.mem_cons_self
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems p.en st wf okEn
      obtain ⟨wf2, ext2, -⟩ := flatten_spec regs mems p.addr
        ((flatten p.en).run st).2 wf1 okAddr
      obtain ⟨wf3, ext3, -⟩ := flatten_spec regs mems p.data
        ((flatten p.addr).run ((flatten p.en).run st).2).2 wf2 okData
      obtain ⟨wf4, ext4⟩ := ih
        ((flatten p.data).run
          ((flatten p.addr).run ((flatten p.en).run st).2).2).2 wf3
        (fun p' mem => ok p' (List.mem_cons_of_mem _ mem))
      exact ⟨wf4, ((ext1.trans ext2).trans (ext3.trans ext4))⟩

theorem flattenMems_spec (regs : List RegDef) (mems : List MemDef)
    (blockSize : Nat) (ms : List MemDef) (st : FlattenSt)
    (wf : st.WF regs mems)
    (ok : ∀ mm ∈ ms, ∀ p ∈ mm.wrPorts, ExprEmitOk regs mems p.en ∧
      ExprEmitOk regs mems p.addr ∧ ExprEmitOk regs mems p.data) :
    (((flattenMems blockSize ms).run st).2).WF regs mems ∧
    st.Extends ((flattenMems blockSize ms).run st).2 := by
  induction ms generalizing st with
  | nil => exact ⟨wf, .rfl st⟩
  | cons mm rest ih =>
      obtain ⟨wf1, ext1⟩ := flattenWrites_spec regs mems mm.wrPorts st wf
        (ok mm List.mem_cons_self)
      obtain ⟨wf2, ext2⟩ := ih ((flattenWrites mm.wrPorts).run st).2 wf1
        (fun mm' mem => ok mm' (List.mem_cons_of_mem _ mem))
      exact ⟨wf2, ext1.trans ext2⟩

theorem flattenOuts_spec (regs : List RegDef) (mems : List MemDef)
    (os : List OutDef) (st : FlattenSt) (wf : st.WF regs mems)
    (ok : ∀ o ∈ os, ExprEmitOk regs mems o.val) :
    (((flattenOuts os).run st).2).WF regs mems ∧
    st.Extends ((flattenOuts os).run st).2 := by
  induction os generalizing st with
  | nil => exact ⟨wf, .rfl st⟩
  | cons o rest ih =>
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems o.val st wf
        (ok o List.mem_cons_self)
      obtain ⟨wf2, ext2⟩ := ih ((flatten o.val).run st).2 wf1
        (fun o' mem => ok o' (List.mem_cons_of_mem _ mem))
      exact ⟨wf2, ext1.trans ext2⟩

/-- The final state of the printer-order traversal is consistent. -/
theorem flattenModule_wf (m : Module) (blockSize : Nat)
    (ok : ModuleEmitOk m) :
    (((flattenModule m blockSize).run {}).2).WF m.regs m.mems := by
  obtain ⟨okRegs, okWrites, okOuts⟩ := ok
  obtain ⟨wf1, -⟩ := flattenRegs_spec m.regs m.mems m.regs {}
    (FlattenSt.WF.empty m.regs m.mems) okRegs
  obtain ⟨wf2, -⟩ := flattenMems_spec m.regs m.mems blockSize m.mems
    ((flattenRegs m.regs).run {}).2 wf1 okWrites
  obtain ⟨wf3, -⟩ := flattenOuts_spec m.regs m.mems m.outs
    ((flattenMems blockSize m.mems).run ((flattenRegs m.regs).run {}).2).2
    wf2 okOuts
  exact wf3

end Loom.Release.SSA
