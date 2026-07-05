-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCFrames
import Machines.Lnp64u.Theorems.RMCEnc

/-!
# R-MC support: kind-word canonicality is preserved by every rule

The `Coupled.kind_canon` clause says every `d*_cap*_kind` register is an
encoder image (`encKind (decKind kw) = kw`), *unconditionally* — dead
slots keep their last canonical word, reset words are `0` (canonical).

This file proves the clause is preserved by a design cycle, syntactically:

* `isCanonE` — a kernel-decidable recognizer for "this expression
  evaluates to a canonical kind word in every state satisfying the
  invariant": encoder-image literals, copies of kind registers (canonical
  by the *unconditional* invariant — no liveness reasoning needed),
  `encMemKindE` packings (canonical by construction: the packed fields
  live in bits `[28:1]`, exactly what `decKind` keeps), and muxes thereof.
* `CanonWritesAll` — one act walk checking every write to any of the 64
  kind registers has an `isCanonE` value. A single kernel reduction per
  rule covers all 64 registers at once.
* `cycle_kind_canon` — the invariant is preserved by `(core m).cycle`.

Every kind write in the design goes through `installA`'s `kindE` argument;
the five call sites pass narrowed packings (`narrowKindE`), kind-register
copies (`capSel`, `transferA`), or muxes of the two (`cap_dup`), so the
checker accepts all of them.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

/-- The unconditional kind-word canonicality invariant of a raw state
(the `Coupled.kind_canon` clause, standalone). -/
def KindCanon (σ : Loom.Hw.St) : Prop :=
  ∀ (c : DomainId) (s : Slot),
    Hw.encKind (Hw.decKind (σ.regs (Hw.dcapKind c s) 32)) =
      σ.regs (Hw.dcapKind c s) 32

/-- All 64 capability kind register names. -/
def capKindNames : List String :=
  (List.finRange numDomains).flatMap fun c =>
    (List.finRange numSlots).map fun s => Hw.dcapKind c s

theorem dcapKind_mem_capKindNames (c : DomainId) (s : Slot) :
    Hw.dcapKind c s ∈ capKindNames := by
  simp only [capKindNames, List.mem_flatMap, List.mem_map]
  exact ⟨c, List.mem_finRange c, s, List.mem_finRange s, rfl⟩

theorem mem_capKindNames_iff (n : String) :
    n ∈ capKindNames ↔ ∃ (c : DomainId) (s : Slot), n = Hw.dcapKind c s := by
  simp only [capKindNames, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨c, -, s, -, rfl⟩; exact ⟨c, s, rfl⟩
  · rintro ⟨c, s, rfl⟩; exact ⟨c, List.mem_finRange c, s, List.mem_finRange s, rfl⟩

/-! ## The packing lemma: `encMemKindE`'s bit layout is an encoder image -/

private theorem bv1_cases (b : BitVec 1) : b = 0#1 ∨ b = 1#1 := by
  have : ∀ x : BitVec 1, x = 0#1 ∨ x = 1#1 := by decide
  exact this b

/-- The three permission bits, packed at `[28:26]`, are `encPerms` of the
decoded booleans. -/
private theorem perms_pack (r w x : BitVec 1) :
    (r.setWidth 32 <<< 26) ||| ((w.setWidth 32 <<< 27) |||
      (x.setWidth 32 <<< 28)) =
    (Hw.encPerms { r := r = 1#1, w := w = 1#1, x := x = 1#1 }).setWidth 32
      <<< 26 := by
  rcases bv1_cases r with hr | hr <;> rcases bv1_cases w with hw | hw <;>
    rcases bv1_cases x with hx | hx <;> subst hr <;> subst hw <;> subst hx <;>
    decide

/-- The circuit-side field packing evaluates to `encKind` of a memory
kind — canonical by `decKind_encKind`. -/
theorem encMem_pack (b : BitVec 12) (l : BitVec 13) (r w x : BitVec 1) :
    (b.setWidth 32 <<< 1) ||| ((l.setWidth 32 <<< 13) |||
      ((r.setWidth 32 <<< 26) ||| ((w.setWidth 32 <<< 27) |||
        (x.setWidth 32 <<< 28)))) =
    Hw.encKind (.mem b l { r := r = 1#1, w := w = 1#1, x := x = 1#1 }) := by
  rw [perms_pack]
  simp [Hw.encKind, BitVec.or_assoc]

/-! ## The canonical-expression recognizer -/

/-- Non-`mux` canonical leaves: encoder-image literals, kind-register
copies, `encMemKindE` packings. -/
def isCanonLeaf (e : Expr 32) : Bool :=
  match e with
  | .lit v => decide (Hw.encKind (Hw.decKind v) = v)
  | .reg _ n => decide (n ∈ capKindNames)
  | .or (.shl (@Expr.zext wb _ _) (.lit s1))
      (.or (.shl (@Expr.zext wl _ _) (.lit s2))
        (.or (.shl (@Expr.zext wr _ _) (.lit s3))
          (.or (.shl (@Expr.zext ww _ _) (.lit s4))
            (.shl (@Expr.zext wx _ _) (.lit s5))))) =>
      wb == 12 && wl == 13 && wr == 1 && ww == 1 && wx == 1 &&
      s1 == 1#32 && s2 == 13#32 && s3 == 26#32 && s4 == 27#32 && s5 == 28#32
  | _ => false

/-- Kind-canonical expressions: mux trees over canonical leaves.
Fuel-based recursion (`Expr 32` is an indexed family, so structural
recursion is unavailable; well-founded recursion would not reduce in the
kernel). The design's deepest kind mux tree is a `muxFin` over 16 slots
under one narrowing mux, far below the fuel. -/
def isCanonE : Nat → Expr 32 → Bool
  | 0, _ => false
  | fuel + 1, .mux _ t f => isCanonE fuel t && isCanonE fuel f
  | _ + 1, e => isCanonLeaf e

/-- Mux depth budget for the design's kind expressions. -/
def canonFuel : Nat := 64

theorem isCanonLeaf_eval {σ : Loom.Hw.St} (hσ : KindCanon σ)
    (e : Expr 32) (h : isCanonLeaf e = true) :
    Hw.encKind (Hw.decKind (e.eval σ)) = e.eval σ := by
  unfold isCanonLeaf at h
  split at h
  · exact of_decide_eq_true h
  · next n =>
      obtain ⟨c, s, rfl⟩ := (mem_capKindNames_iff n).mp (of_decide_eq_true h)
      exact hσ c s
  · next wb _ wl _ wr _ ww _ wx _ s1 s2 s3 s4 s5 =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hwb, hwl⟩, hwr⟩, hww⟩, hwx⟩, hs1⟩, hs2⟩, hs3⟩, hs4⟩, hs5⟩ := h
      subst hwb; subst hwl; subst hwr; subst hww; subst hwx
      subst hs1; subst hs2; subst hs3; subst hs4; subst hs5
      show Hw.encKind (Hw.decKind _) = _
      simp only [Expr.eval]
      norm_num
      rw [encMem_pack, decKind_encKind]
  · simp at h

/-- Recognized expressions evaluate to canonical kind words in any state
satisfying the invariant. -/
theorem isCanonE_eval {σ : Loom.Hw.St} (hσ : KindCanon σ) :
    ∀ (fuel : Nat) (e : Expr 32), isCanonE fuel e = true →
      Hw.encKind (Hw.decKind (e.eval σ)) = e.eval σ
  | 0, e, h => by simp [isCanonE] at h
  | fuel + 1, .mux c t f, h => by
      simp only [isCanonE, Bool.and_eq_true] at h
      show Hw.encKind (Hw.decKind (if c.eval σ = 1#1 then t.eval σ else f.eval σ))
        = if c.eval σ = 1#1 then t.eval σ else f.eval σ
      split
      · exact isCanonE_eval hσ fuel t h.1
      · exact isCanonE_eval hσ fuel f h.2
  | _ + 1, .lit v, h => isCanonLeaf_eval hσ _ (by simpa [isCanonE] using h)
  | _ + 1, .reg _ n, h => isCanonLeaf_eval hσ _ (by simpa [isCanonE] using h)
  | _ + 1, .memRead _ _ a, h => isCanonLeaf_eval hσ _ (by simpa [isCanonE] using h)
  | _ + 1, .and a b, h => isCanonLeaf_eval hσ _ (by simpa [isCanonE] using h)
  | _ + 1, .or a b, h => isCanonLeaf_eval hσ _ (by simpa [isCanonE] using h)
  | _ + 1, .xor a b, h => isCanonLeaf_eval hσ _ (by simpa [isCanonE] using h)
  | _ + 1, .not a, h => isCanonLeaf_eval hσ _ (by simpa [isCanonE] using h)
  | _ + 1, .add a b, h => isCanonLeaf_eval hσ _ (by simpa [isCanonE] using h)
  | _ + 1, .sub a b, h => isCanonLeaf_eval hσ _ (by simpa [isCanonE] using h)
  | _ + 1, .shl a b, h => isCanonLeaf_eval hσ _ (by simpa [isCanonE] using h)
  | _ + 1, .shr a b, h => isCanonLeaf_eval hσ _ (by simpa [isCanonE] using h)
  | _ + 1, .slice a lo _, h => isCanonLeaf_eval hσ _ (by simpa [isCanonE] using h)
  | _ + 1, .zext a _, h => isCanonLeaf_eval hσ _ (by simpa [isCanonE] using h)
  | _ + 1, .sext a _, h => isCanonLeaf_eval hσ _ (by simpa [isCanonE] using h)

/-! ## The act-level checker (one walk covers all 64 kind registers) -/

/-- Every write to any name in `names` (at width 32) has an `isCanonE`
value; writes at other widths never alias a 32-bit read. -/
def CanonWritesAll (names : List String) : Act → Bool
  | .skip => true
  | .seq a b => CanonWritesAll names a && CanonWritesAll names b
  | .ite _ t e => CanonWritesAll names t && CanonWritesAll names e
  | .memWrite _ _ _ _ _ _ => true
  | .write w r v =>
      if r ∈ names then
        if h : w = 32 then isCanonE canonFuel (h ▸ v) else true
      else true

/-- Preservation: running a checked act keeps every tracked register
canonical (values evaluate against the pre-state `σ`, which satisfies the
invariant). -/
theorem run_CanonWritesAll {σ : Loom.Hw.St} (hσ : KindCanon σ)
    {names : List String} {rn : String} (hrn : rn ∈ names) :
    ∀ (a : Act), CanonWritesAll names a = true →
      ∀ (acc : Loom.Hw.St),
        Hw.encKind (Hw.decKind (acc.regs rn 32)) = acc.regs rn 32 →
        Hw.encKind (Hw.decKind ((a.run σ acc).regs rn 32))
          = (a.run σ acc).regs rn 32
  | .skip, _, _, hP => hP
  | .seq a b, h, acc, hP => by
      simp only [CanonWritesAll, Bool.and_eq_true] at h
      exact run_CanonWritesAll hσ hrn b h.2 _
        (run_CanonWritesAll hσ hrn a h.1 acc hP)
  | .ite c t e, h, acc, hP => by
      simp only [CanonWritesAll, Bool.and_eq_true] at h
      show Hw.encKind (Hw.decKind
          ((if c.eval σ = 1#1 then t.run σ acc else e.run σ acc).regs rn 32))
        = (if c.eval σ = 1#1 then t.run σ acc else e.run σ acc).regs rn 32
      split
      · exact run_CanonWritesAll hσ hrn t h.1 acc hP
      · exact run_CanonWritesAll hσ hrn e h.2 acc hP
  | .memWrite .., _, _, hP => hP
  | .write w r v, h, acc, hP => by
      show Hw.encKind (Hw.decKind ((acc.regs.set r (v.eval σ)) rn 32))
        = (acc.regs.set r (v.eval σ)) rn 32
      simp only [RegEnv.set]
      by_cases hr : rn = r
      · rw [if_pos hr]
        by_cases hw : w = 32
        · subst hw
          rw [dif_pos rfl]
          simp only [CanonWritesAll] at h
          rw [if_pos (hr ▸ hrn)] at h
          simp only [dite_true] at h
          exact isCanonE_eval hσ canonFuel v h
        · rw [dif_neg hw]; exact hP
      · rw [if_neg hr]; exact hP

/-! ## Per-rule instances (single kernel walks) -/

private theorem retire_canon :
    CanonWritesAll capKindNames Hw.retireAct = true := by decide +kernel

private theorem rvInit_canon :
    CanonWritesAll capKindNames Hw.rvInit = true := by decide +kernel

private theorem rvStep_canon :
    CanonWritesAll capKindNames Hw.rvStep = true := by decide +kernel

private theorem issueFor_canon (m : Manifest) (x : DomainId) :
    CanonWritesAll capKindNames (Hw.issueFor m x) = true := by
  fin_cases x <;> exact rfl

private theorem mover_canon :
    CanonWritesAll capKindNames Hw.moverAct = true := by decide +kernel

private theorem refill_canon (m : Manifest) :
    CanonWritesAll capKindNames (Hw.refillAct m) = true := rfl

private theorem tick_canon :
    CanonWritesAll capKindNames Hw.tickAct = true := by decide +kernel

private theorem issueFold_canon (m : Manifest)
    (h : ∀ x : DomainId, CanonWritesAll capKindNames (Hw.issueFor m x) = true) :
    ∀ l : List DomainId,
      CanonWritesAll capKindNames
        (l.foldr (fun d acc => Act.ite (Hw.eligE m d) (Hw.issueFor m d) acc)
          Act.skip) = true
  | [] => rfl
  | d :: t => by
      simp only [List.foldr, CanonWritesAll, Bool.and_eq_true]
      exact ⟨h d, issueFold_canon m h t⟩

private theorem coreAct_canon (m : Manifest) :
    CanonWritesAll capKindNames (Hw.coreAct m) = true := by
  have hfold := issueFold_canon m (issueFor_canon m) (Hw.schedOrder m)
  have hcnt : CanonWritesAll capKindNames
      (.write 8 "if_cl" (.sub (.reg 8 "if_cl") (.lit 1))) = true := by
    simp only [CanonWritesAll]
    rw [if_neg (by decide : ¬"if_cl" ∈ capKindNames)]
  simp only [Hw.coreAct, CanonWritesAll, Bool.and_eq_true]
  exact ⟨⟨retire_canon, hcnt, ⟨rvInit_canon, rvStep_canon⟩, trivial⟩, hfold⟩

/-! ## The cycle-level preservation theorem -/

/-- One design cycle preserves the unconditional kind canonicality. -/
theorem cycle_kind_canon (m : Manifest) (σ : Loom.Hw.St)
    (hσ : KindCanon σ) : KindCanon ((Hw.core m).cycle σ) := by
  intro c s
  have hrn := dcapKind_mem_capKindNames c s
  rw [core_cycle_unfold]
  refine run_CanonWritesAll hσ hrn _ tick_canon _ ?_
  refine run_CanonWritesAll hσ hrn _ mover_canon _ ?_
  refine run_CanonWritesAll hσ hrn _ (coreAct_canon m) _ ?_
  refine run_CanonWritesAll hσ hrn _ (refill_canon m) _ ?_
  exact hσ c s

end Machines.Lnp64u.Theorems.RMC
