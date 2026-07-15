-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateAbs

/-!
# R-MC retirement: semantic gate-transfer instantiation

Semantic freshness and liveness facts used to instantiate the whole-state
`transferA` abstraction for both gate operations.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 3200000
set_option maxRecDepth 200000

/-! ## Liveness of the structural transfer state -/

/-- A live abstract capability exposes the canonical raw kind word stored in
its selected slot. -/
theorem capKindWord_of_some (σ : Loom.Hw.St) (D : DomainId) (S : Slot)
    (e : CapEntry) (hkc : KindCanon σ)
    (hcap : ((Hw.abs σ).doms D).caps S = some e) :
    σ.regs (Hw.dcapKind D S) 32 = Hw.encKind e.kind := by
  have hv : σ.regs (Hw.dcapV D S) 1 = 1#1 := by
    by_contra hn
    have hz := bv1_ne_one.mp hn
    change (if σ.regs (Hw.dcapV D S) 1 = 1#1 then _ else none) = some e
      at hcap
    rw [if_neg (by simpa [hz])] at hcap
    contradiction
  have he : Hw.decKind (σ.regs (Hw.dcapKind D S) 32) = e.kind := by
    change (if σ.regs (Hw.dcapV D S) 1 = 1#1 then some _ else none) = some e
      at hcap
    rw [if_pos hv] at hcap
    exact congrArg CapEntry.kind (Option.some.inj hcap)
  rw [← hkc D S, he]

/-- A spec-live handle makes the corresponding hardware selector live. -/
theorem capSel_live_of_liveRef (σ : Loom.Hw.St) (D : DomainId)
    (hwE : Expr 32) (S : Slot)
    (hslot : S.val = ((hwE.eval σ).extractLsb' 0 4).toNat)
    (hlive : (Hw.abs σ).liveRef
      ⟨D, S, (hwE.eval σ).extractLsb' 4 8⟩ = true) :
    (Hw.capSel D hwE).live.eval σ = 1#1 := by
  apply (capSel_live_eval σ D hwE S hslot).mpr
  exact (abs_liveRef σ D S ((hwE.eval σ).extractLsb' 4 8)).mp hlive

/-- Once its slot is decoded, a selector over a live abstract capability
reads that capability's canonical kind encoding. -/
theorem capSel_kind_of_some (σ : Loom.Hw.St) (D : DomainId) (hwE : Expr 32)
    (S : Slot) (e : CapEntry) (hkc : KindCanon σ)
    (hslot : S.val = ((hwE.eval σ).extractLsb' 0 4).toNat)
    (hcap : ((Hw.abs σ).doms D).caps S = some e) :
    (Hw.capSel D hwE).kindW.eval σ = Hw.encKind e.kind := by
  rw [capSel_kindW_eval σ D hwE S hslot]
  exact capKindWord_of_some σ D S e hkc hcap

/-- A selector over a live capability whose handle class agrees with the
entry passes the hardware class check. -/
theorem capSel_clsOk_of_some (σ : Loom.Hw.St) (D : DomainId)
    (hwE : Expr 32) (S : Slot) (e : CapEntry) (hkc : KindCanon σ)
    (hslot : S.val = ((hwE.eval σ).extractLsb' 0 4).toNat)
    (hcap : ((Hw.abs σ).doms D).caps S = some e)
    (hcls : (Handle.decode (hwE.eval σ)).cls = e.kind.cls) :
    (Hw.capSel D hwE).clsOk.eval σ = 1#1 := by
  have hkind := capSel_kind_of_some σ D hwE S e hkc hslot hcap
  show (if ((Hw.capSel D hwE).kindW.eval σ).extractLsb' 0 1 =
      (hwE.eval σ).extractLsb' 12 1 then 1#1 else 0#1) = 1#1
  rw [hkind]
  rw [if_pos]
  have hb := (cls_eq_iff_bits (hwE.eval σ) (Hw.encKind e.kind)).mp (by
    rw [decKind_encKind]
    exact hcls)
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  interval_cases k
  simpa [BitVec.getLsbD_extractLsb'] using hb.symm

/-- For a selected canonical entry, the hardware class predicate is exactly
the specification handle-class check. -/
theorem capSel_clsOk_iff_some (σ : Loom.Hw.St) (D : DomainId)
    (hwE : Expr 32) (S : Slot) (e : CapEntry) (hkc : KindCanon σ)
    (hslot : S.val = ((hwE.eval σ).extractLsb' 0 4).toNat)
    (hcap : ((Hw.abs σ).doms D).caps S = some e) :
    (Hw.capSel D hwE).clsOk.eval σ = 1#1 ↔
      (Handle.decode (hwE.eval σ)).cls = e.kind.cls := by
  constructor
  · intro hok
    have hkind := capSel_kind_of_some σ D hwE S e hkc hslot hcap
    have hbits : (Hw.encKind e.kind).extractLsb' 0 1 =
        (hwE.eval σ).extractLsb' 12 1 := by
      change (if ((Hw.capSel D hwE).kindW.eval σ).extractLsb' 0 1 =
          (hwE.eval σ).extractLsb' 12 1 then 1#1 else 0#1) = 1#1 at hok
      rw [hkind] at hok
      split at hok
      next h => exact h
      next => contradiction
    have hb : (hwE.eval σ).getLsbD 12 =
        (Hw.encKind e.kind).getLsbD 0 :=
      ((extract1_eq_iff (Hw.encKind e.kind) (hwE.eval σ) 0 12).mp
        hbits).symm
    have hc := (cls_eq_iff_bits (hwE.eval σ)
      (Hw.encKind e.kind)).mpr hb
    simpa [decKind_encKind] using hc
  · exact capSel_clsOk_of_some σ D hwE S e hkc hslot hcap

/-- For a selected canonical entry, the hardware memory-kind predicate is
true exactly for a specification memory capability. -/
theorem capSel_isMem_iff_some (σ : Loom.Hw.St) (D : DomainId)
    (hwE : Expr 32) (S : Slot) (e : CapEntry) (hkc : KindCanon σ)
    (hslot : S.val = ((hwE.eval σ).extractLsb' 0 4).toNat)
    (hcap : ((Hw.abs σ).doms D).caps S = some e) :
    (Hw.kIsMem (Hw.capSel D hwE).kindW).eval σ = 1#1 ↔
      ∃ base len perms, e.kind = .mem base len perms := by
  have hkind := capSel_kind_of_some σ D hwE S e hkc hslot hcap
  cases hk : e.kind with
  | mem base len perms =>
      constructor
      · intro _
        exact ⟨base, len, perms, rfl⟩
      · intro _
        change (if ((Hw.capSel D hwE).kindW.eval σ).extractLsb' 0 1 = 0#1
          then 1#1 else 0#1) = 1#1
        rw [hkind, hk, if_pos]
        exact (extract1_eq_zero_iff _ 0).mpr (by simp [Hw.encKind])
  | gate g =>
      constructor
      · intro hm
        change (if ((Hw.capSel D hwE).kindW.eval σ).extractLsb' 0 1 = 0#1
          then 1#1 else 0#1) = 1#1 at hm
        rw [hkind, hk, if_neg] at hm
        · contradiction
        · intro hx
          have hb := (extract1_eq_zero_iff _ 0).mp hx
          simp [Hw.encKind] at hb
      · rintro ⟨base, len, perms, heq⟩
        cases heq

/-- A live hardware selector yields both the exact specification `liveCap`
witness and the corresponding abstract capability-table entry.  The view
equality is intentionally generic: gate call and gate return instantiate it
after their respective PC-only retirement prefixes. -/
theorem capSel_entry_of_live (σ : Loom.Hw.St)
    (τ : MachineState) (D : DomainId) (hwE : Expr 32)
    (hbridge : ∀ (S : Slot) (G : Gen),
      (τ.doms D).liveCap S G = ((Hw.abs σ).doms D).liveCap S G)
    (hlive : (Hw.capSel D hwE).live.eval σ = 1#1) :
    ∃ e : CapEntry,
      (τ.doms D).liveCap (Handle.decode (hwE.eval σ)).slot
          (Handle.decode (hwE.eval σ)).gen = some e ∧
      ((Hw.abs σ).doms D).caps
          (Handle.decode (hwE.eval σ)).slot = some e := by
  let S : Slot := finOfBv (by decide) ((hwE.eval σ).extractLsb' 0 4)
  have hraw := (capSel_live_eval σ D hwE S rfl).mp hlive
  let e : CapEntry :=
    { kind := Hw.decKind (σ.regs (Hw.dcapKind D S) 32)
      lineage := if σ.regs (Hw.dcapLinV D S) 1 = 1#1 then
        some (finOfBv (by decide) (σ.regs (Hw.dcapLin D S) 4))
      else none }
  refine ⟨e, ?_, ?_⟩
  · change (τ.doms D).liveCap S
      ((hwE.eval σ).extractLsb' 4 8) = some e
    rw [hbridge, abs_liveCap, if_pos hraw]
  · change (if σ.regs (Hw.dcapV D S) 1 = 1#1 then some e else none) = some e
    rw [if_pos hraw.1]

/-- A canonical gate-kind word yields its encoded gate identifier. -/
theorem kGid_encGate_eval (σ : Loom.Hw.St) (kw : Expr 32) (g : GateId)
    (hkw : kw.eval σ = Hw.encKind (.gate g)) :
    finOfBv (by decide : 2 ^ 2 = numGates) ((Hw.kGid kw).eval σ) = g := by
  change finOfBv (by decide : 2 ^ 2 = numGates)
    ((kw.eval σ).extractLsb' 1 2) = g
  rw [hkw]
  fin_cases g <;> rfl

/-- Installing into a genuinely free slot preserves every reference that
was live before the installation. A pre-existing live reference cannot name
the selected free slot. -/
theorem installTransferred_liveRef_of_live (τ : MachineState)
    (T : DomainId) (NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef)) (r : CapRef)
    (hfree : (τ.doms T).caps NS = none)
    (hlive : τ.liveRef r = true) :
    (installTransferred τ T NS kind moved).liveRef r = true := by
  rcases r with ⟨rd, rs, rg⟩
  unfold MachineState.liveRef at hlive ⊢
  by_cases hd : rd = T
  · subst rd
    by_cases hs : rs = NS
    · subst rs
      simp [hfree, DomainState.liveCap] at hlive
    · simpa [installTransferred, MachineState.setDom, hs,
        DomainState.liveCap] using hlive
  · simpa [installTransferred, MachineState.setDom, hd,
      DomainState.liveCap] using hlive

/-- For a reference that was live before transfer installation, the
install/reparent/clear prefix makes it dead exactly when it names the source
domain and slot. Reparenting is liveness-neutral, and the fresh install
cannot invalidate any pre-existing live reference. -/
theorem transferStructural_dead_iff_of_live (τ : MachineState)
    (T : DomainId) (NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef))
    (oldRef newRef : CapRef) (D : DomainId) (S : Slot) (r : CapRef)
    (hfree : (τ.doms T).caps NS = none)
    (hlive : τ.liveRef r = true) :
    ((((installTransferred τ T NS kind moved).reparent oldRef newRef).clearSlot
        D S).liveRef r = false) ↔
      r.dom = D ∧ r.slot = S := by
  rw [clearSlot_liveRef]
  by_cases hsrc : r.dom = D ∧ r.slot = S
  · simp [hsrc]
  · rw [if_neg hsrc, reparent_liveRef]
    have hi := installTransferred_liveRef_of_live τ T NS kind moved r
      hfree hlive
    simp [hsrc, hi]

/-- Exact liveness of a pre-existing live reference through the structural
transfer prefix.  Only the removed source slot can make it dead. -/
theorem transferStructural_liveRef_of_live (τ : MachineState)
    (T : DomainId) (NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef))
    (oldRef newRef : CapRef) (D : DomainId) (S : Slot) (r : CapRef)
    (hfree : (τ.doms T).caps NS = none)
    (hlive : τ.liveRef r = true) :
    (((installTransferred τ T NS kind moved).reparent oldRef newRef).clearSlot
        D S).liveRef r =
      if r.dom = D ∧ r.slot = S then false else true := by
  rw [clearSlot_liveRef]
  by_cases hsrc : r.dom = D ∧ r.slot = S
  · simp [hsrc]
  · rw [if_neg hsrc, reparent_liveRef]
    simpa [hsrc] using
      installTransferred_liveRef_of_live τ T NS kind moved r hfree hlive

/-- A reference that was live before transfer and does not name the removed
source slot retains its Mover-relevant capability kind.  The freshly
installed destination cannot alias such a reference because its slot was
free in the pre-transfer state. -/
theorem transferStructural_liveKind_of_live (τ : MachineState)
    (T : DomainId) (NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef))
    (oldRef newRef : CapRef) (D : DomainId) (S : Slot) (r : CapRef)
    (hfree : (τ.doms T).caps NS = none)
    (hlive : τ.liveRef r = true)
    (hout : ¬(r.dom = D ∧ r.slot = S)) :
    Option.map CapEntry.kind
        (((((installTransferred τ T NS kind moved).reparent oldRef newRef)
          |>.clearSlot D S).sweepRegions.doms r.dom).liveCap r.slot r.gen) =
      Option.map CapEntry.kind
        ((τ.doms r.dom).liveCap r.slot r.gen) := by
  have hdst : ¬(r.dom = T ∧ r.slot = NS) := by
    rintro ⟨hd, hs⟩
    subst hd
    subst hs
    unfold MachineState.liveRef DomainState.liveCap at hlive
    simp [hfree] at hlive
  unfold DomainState.liveCap
  rw [sweepRegions_caps, sweepRegions_slotGen, clearSlot_caps,
    clearSlot_slotGen, if_neg hout]
  by_cases hd : r.dom = T
  · have hs : r.slot ≠ NS := fun h => hdst ⟨hd, h⟩
    have hout' : ¬(T = D ∧ r.slot = S) := by
      rintro ⟨hTD, hrs⟩
      exact hout ⟨hd.trans hTD, hrs⟩
    simp [installTransferred, MachineState.reparent, MachineState.setDom, hd,
      hs, hout']
  · simp [installTransferred, MachineState.reparent, MachineState.setDom, hd,
      hout]

/-- On a valid pre-transfer region, the hardware source-slot predicate is
equivalent to the backing becoming dead after install/reparent/clear. The
Wf region invariant supplies the crucial pre-transfer liveness premise. -/
theorem transferKilled_structural_iff_dead (σ : Loom.Hw.St)
    (D : DomainId) (sourceSlotE : Expr 4) (S : Slot)
    (hsourceSlot : sourceSlotE.eval σ = BitVec.ofNat 4 S.val)
    (T : DomainId) (NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef)) (oldRef newRef : CapRef)
    (hfree : ((Hw.abs σ).doms T).caps NS = none)
    (hwf : Wf (Hw.abs σ)) (c : DomainId) (r : RegionId)
    (hv : σ.regs (Hw.drgnV c r) 1 = 1#1) :
    ((Expr.and (.eq
        (Hw.field (.reg 42 (Hw.drgn c r)) 40 2) (Hw.dLit D))
      (.eq (Hw.field (.reg 42 (Hw.drgn c r)) 36 4) sourceSlotE)).eval σ =
        1#1) ↔
      ((((installTransferred (Hw.abs σ) T NS kind moved).reparent
          oldRef newRef).clearSlot D S).liveRef
        (Hw.decRegion (σ.regs (Hw.drgn c r) 42)).backing = false) := by
  let rg := Hw.decRegion (σ.regs (Hw.drgn c r) 42)
  have hrg : ((Hw.abs σ).doms c).regions r = some rg := by
    change (if σ.regs (Hw.drgnV c r) 1 = 1#1 then
      some (Hw.decRegion (σ.regs (Hw.drgn c r) 42)) else none) = some rg
    simp [hv, rg]
  have hlive : (Hw.abs σ).liveRef rg.backing = true :=
    regionBacking_live hwf hrg
  exact (transferKilled_region_eval σ D sourceSlotE S hsourceSlot
    (.reg 42 (Hw.drgn c r))).trans
      (transferStructural_dead_iff_of_live (Hw.abs σ) T NS kind moved
        oldRef newRef D S rg.backing hfree hlive).symm

/-- Accumulator-general form of `transferKilled_structural_iff_dead`.
The sampled state supplies the kill predicate, while the accumulator supplies
the abstract state being transformed; equality of the region banks is the
only bridge required between them. -/
theorem transferKilled_structural_iff_dead_acc (σ acc : Loom.Hw.St)
    (D : DomainId) (sourceSlotE : Expr 4) (S : Slot)
    (hsourceSlot : sourceSlotE.eval σ = BitVec.ofNat 4 S.val)
    (T : DomainId) (NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef)) (oldRef newRef : CapRef)
    (hregionV : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgnV c r) 1 = σ.regs (Hw.drgnV c r) 1)
    (hregion : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgn c r) 42 = σ.regs (Hw.drgn c r) 42)
    (hfree : ((Hw.abs acc).doms T).caps NS = none)
    (hwf : Wf (Hw.abs acc)) (c : DomainId) (r : RegionId)
    (hv : σ.regs (Hw.drgnV c r) 1 = 1#1) :
    ((Expr.and (.eq
        (Hw.field (.reg 42 (Hw.drgn c r)) 40 2) (Hw.dLit D))
      (.eq (Hw.field (.reg 42 (Hw.drgn c r)) 36 4) sourceSlotE)).eval σ =
        1#1) ↔
      ((((installTransferred (Hw.abs acc) T NS kind moved).reparent
          oldRef newRef).clearSlot D S).liveRef
        (Hw.decRegion (σ.regs (Hw.drgn c r) 42)).backing = false) := by
  let rg := Hw.decRegion (σ.regs (Hw.drgn c r) 42)
  have hrg : ((Hw.abs acc).doms c).regions r = some rg := by
    change (if acc.regs (Hw.drgnV c r) 1 = 1#1 then
      some (Hw.decRegion (acc.regs (Hw.drgn c r) 42)) else none) = some rg
    rw [hregionV c r, hregion c r]
    simp [hv, rg]
  have hlive : (Hw.abs acc).liveRef rg.backing = true :=
    regionBacking_live hwf hrg
  exact (transferKilled_region_eval σ D sourceSlotE S hsourceSlot
    (.reg 42 (Hw.drgn c r))).trans
      (transferStructural_dead_iff_of_live (Hw.abs acc) T NS kind moved
        oldRef newRef D S rg.backing hfree hlive).symm

/-! ## Whole transfer action with semantic sweep discharge -/

/-- Whole-domain abstraction of the four transfer actions when run directly
from the sampled state. Compared with the syntactic composition theorem,
the Wf invariant and target-slot freshness now discharge the region-sweep
obligation automatically. -/
theorem absDom_transferActions_selected (σ : Loom.Hw.St)
    (T : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE oldE newE : Expr 14)
    (NS : Slot) (kind : CapKind)
    (D : DomainId) (sourceSlotE : Expr 4)
    (sourceLinVE : Expr 1) (sourceLinE : Expr 4) (S : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val)
    (hkind : kindE.eval σ = Hw.encKind kind)
    (hfreeCell : linVE.eval σ = 1#1 →
      σ.regs (Hw.dcellV T (finOfBv (by decide) (nlE.eval σ))) 1 ≠ 1#1)
    (hparent : linVE.eval σ = 1#1 →
      Hw.decRef (parE.eval σ) ≠ Hw.decRef (oldE.eval σ))
    (hsourceSlot : sourceSlotE.eval σ = BitVec.ofNat 4 S.val)
    (hremoved : removedCell
      ((installTransferred (Hw.abs σ) T NS kind
        (if linVE.eval σ = 1#1 then
          some (finOfBv (by decide) (nlE.eval σ), Hw.decRef (parE.eval σ))
        else none)).reparent (Hw.decRef (oldE.eval σ))
          (Hw.decRef (newE.eval σ))) D S =
      if sourceLinVE.eval σ = 1#1 then
        some (finOfBv (by decide) (sourceLinE.eval σ)) else none)
    (htargetFree : ((Hw.abs σ).doms T).caps NS = none)
    (hwf : Wf (Hw.abs σ)) (c : DomainId) :
    Hw.absDom ((Hw.sweepRegionsA
      (fun dm sl => .and (.eq dm (Hw.dLit D)) (.eq sl sourceSlotE))).run σ
      ((Hw.clearSlotA D sourceSlotE sourceLinVE sourceLinE).run σ
        ((Hw.reparentA oldE newE).run σ
          ((Hw.installA T nsE kindE linVE nlE parE).run σ σ)))) c =
      (((((installTransferred (Hw.abs σ) T NS kind
        (if linVE.eval σ = 1#1 then
          some (finOfBv (by decide) (nlE.eval σ), Hw.decRef (parE.eval σ))
        else none)).reparent (Hw.decRef (oldE.eval σ))
          (Hw.decRef (newE.eval σ))).clearSlot D S).sweepRegions).doms c) := by
  apply absDom_install_reparent_clear_sweep_selected σ σ T nsE kindE linVE
    nlE parE oldE newE NS kind D sourceSlotE sourceLinVE sourceLinE S
    (fun dm sl => .and (.eq dm (Hw.dLit D)) (.eq sl sourceSlotE))
    hns hkind
  · intro c' l
    rfl
  · intro c' l
    rfl
  · intro c' r
    rfl
  · intro c' r
    rfl
  · exact hfreeCell
  · exact hparent
  · exact hsourceSlot
  · rfl
  · exact hremoved
  · intro c' r hv
    exact transferKilled_structural_iff_dead σ D sourceSlotE S hsourceSlot
      T NS kind
      (if linVE.eval σ = 1#1 then
        some (finOfBv (by decide) (nlE.eval σ), Hw.decRef (parE.eval σ))
      else none)
      (Hw.decRef (oldE.eval σ)) (Hw.decRef (newE.eval σ)) htargetFree
      hwf c' r hv

/-- Accumulator-general whole-domain abstraction of the four transfer
actions.  This is the form needed by retirement, whose accumulator already
contains refill and in-flight-clear updates. -/
theorem absDom_transferActions_selected_acc (σ acc : Loom.Hw.St)
    (T : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE oldE newE : Expr 14)
    (NS : Slot) (kind : CapKind)
    (D : DomainId) (sourceSlotE : Expr 4)
    (sourceLinVE : Expr 1) (sourceLinE : Expr 4) (S : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val)
    (hkind : kindE.eval σ = Hw.encKind kind)
    (hV : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hP : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14)
    (hregionV : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgnV c r) 1 = σ.regs (Hw.drgnV c r) 1)
    (hregion : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgn c r) 42 = σ.regs (Hw.drgn c r) 42)
    (hgen : acc.regs (Hw.dgen D S) 8 = σ.regs (Hw.dgen D S) 8)
    (hfreeCell : linVE.eval σ = 1#1 →
      σ.regs (Hw.dcellV T (finOfBv (by decide) (nlE.eval σ))) 1 ≠ 1#1)
    (hparent : linVE.eval σ = 1#1 →
      Hw.decRef (parE.eval σ) ≠ Hw.decRef (oldE.eval σ))
    (hsourceSlot : sourceSlotE.eval σ = BitVec.ofNat 4 S.val)
    (hremoved : removedCell
      ((installTransferred (Hw.abs acc) T NS kind
        (if linVE.eval σ = 1#1 then
          some (finOfBv (by decide) (nlE.eval σ), Hw.decRef (parE.eval σ))
        else none)).reparent (Hw.decRef (oldE.eval σ))
          (Hw.decRef (newE.eval σ))) D S =
      if sourceLinVE.eval σ = 1#1 then
        some (finOfBv (by decide) (sourceLinE.eval σ)) else none)
    (htargetFree : ((Hw.abs acc).doms T).caps NS = none)
    (hwf : Wf (Hw.abs acc)) (c : DomainId) :
    Hw.absDom ((Hw.sweepRegionsA
      (fun dm sl => .and (.eq dm (Hw.dLit D)) (.eq sl sourceSlotE))).run σ
      ((Hw.clearSlotA D sourceSlotE sourceLinVE sourceLinE).run σ
        ((Hw.reparentA oldE newE).run σ
          ((Hw.installA T nsE kindE linVE nlE parE).run σ acc)))) c =
      (((((installTransferred (Hw.abs acc) T NS kind
        (if linVE.eval σ = 1#1 then
          some (finOfBv (by decide) (nlE.eval σ), Hw.decRef (parE.eval σ))
        else none)).reparent (Hw.decRef (oldE.eval σ))
          (Hw.decRef (newE.eval σ))).clearSlot D S).sweepRegions).doms c) := by
  apply absDom_install_reparent_clear_sweep_selected σ acc T nsE kindE linVE
    nlE parE oldE newE NS kind D sourceSlotE sourceLinVE sourceLinE S
    (fun dm sl => .and (.eq dm (Hw.dLit D)) (.eq sl sourceSlotE))
    hns hkind hV hP hregionV hregion hfreeCell hparent hsourceSlot hgen
    hremoved
  intro c' r hv
  exact transferKilled_structural_iff_dead_acc σ acc D sourceSlotE S
    hsourceSlot T NS kind
    (if linVE.eval σ = 1#1 then
      some (finOfBv (by decide) (nlE.eval σ), Hw.decRef (parE.eval σ))
    else none)
    (Hw.decRef (oldE.eval σ)) (Hw.decRef (newE.eval σ)) hregionV hregion
    htargetFree hwf c' r hv

/-! ## Identifying the abstract source and destination updates -/

/-- Installing into a free destination cannot overwrite the occupied source
slot. Consequently the later reparent pass leaves `removedCell` at the
source equal to the original entry's lineage selector. -/
theorem removedCell_installTransferred_reparent_source (τ : MachineState)
    (D : DomainId) (S : Slot) (e : CapEntry)
    (hsource : (τ.doms D).caps S = some e)
    (T : DomainId) (NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef))
    (hfree : (τ.doms T).caps NS = none)
    (oldRef newRef : CapRef) :
    removedCell ((installTransferred τ T NS kind moved).reparent
      oldRef newRef) D S = e.lineage := by
  have hpair : ¬(D = T ∧ S = NS) := by
    rintro ⟨rfl, rfl⟩
    rw [hfree] at hsource
    contradiction
  unfold removedCell
  rw [reparent_caps]
  unfold installTransferred MachineState.setDom
  by_cases hd : D = T
  · subst D
    have hs : S ≠ NS := fun h => hpair ⟨rfl, h⟩
    simp [Loom.Fun.update_same, hs, hsource]
  · simp [Loom.Fun.update_ne _ _ _ _ hd, hsource]

/-- The parent mux used by `transferA` never leaves the moved cell pointing
at the old reference: an old-parent match selects the new reference, while a
non-match retains a provably different packed parent. -/
theorem decRef_transfer_parent_mux_ne (σ : Loom.Hw.St)
    (srcPar oldE newE : Expr 14)
    (hnew : Hw.decRef (newE.eval σ) ≠ Hw.decRef (oldE.eval σ)) :
    Hw.decRef ((Expr.mux (.eq srcPar oldE) newE srcPar).eval σ) ≠
      Hw.decRef (oldE.eval σ) := by
  by_cases hp : srcPar.eval σ = oldE.eval σ
  · simpa [Expr.eval, hp] using hnew
  · have hdec : Hw.decRef (srcPar.eval σ) ≠ Hw.decRef (oldE.eval σ) := by
      intro h
      apply hp
      rw [← encRef_decRef (srcPar.eval σ), h, encRef_decRef]
    simpa [Expr.eval, hp] using hdec

/-- The reference formed from a free destination slot differs from the
reference of an occupied source slot, even for an intra-domain transfer. -/
theorem fresh_destination_ref_ne_source (τ : MachineState)
    (D : DomainId) (S : Slot) (e : CapEntry)
    (hsource : (τ.doms D).caps S = some e)
    (T : DomainId) (NS : Slot)
    (hfree : (τ.doms T).caps NS = none) :
    (⟨T, NS, (τ.doms T).slotGen NS⟩ : CapRef) ≠
      ⟨D, S, (τ.doms D).slotGen S⟩ := by
  intro h
  injection h with hd hs hg
  rw [hd, hs] at hfree
  rw [hfree] at hsource
  contradiction

/-- Decoding a packed hardware reference with selected slot/generation
values yields the corresponding abstract reference. -/
theorem encRefE_decoded_selected (σ : Loom.Hw.St) (D : DomainId)
    (slotE : Expr 4) (genE : Expr 8) (S : Slot) (G : Gen)
    (hslot : slotE.eval σ = BitVec.ofNat 4 S.val)
    (hgen : genE.eval σ = G) :
    Hw.decRef ((Hw.encRefE (Hw.dLit D) slotE genE).eval σ) =
      ⟨D, S, G⟩ := by
  have henc : (Hw.encRefE (Hw.dLit D) slotE genE).eval σ =
      Hw.encRef ⟨D, S, G⟩ := by
    show (genE.eval σ).setWidth 14 |||
      ((slotE.eval σ).setWidth 14 <<< 8 |||
        (BitVec.ofNat 2 D.val).setWidth 14 <<< 12) = _
    rw [hslot, hgen]
    have hSv : BitVec.ofNat 14 S.val =
        (BitVec.ofNat 4 S.val).setWidth 14 := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    have hDv : BitVec.ofNat 14 D.val =
        (BitVec.ofNat 2 D.val).setWidth 14 := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    show G.setWidth 14 |||
      ((BitVec.ofNat 4 S.val).setWidth 14 <<< 8 |||
        (BitVec.ofNat 2 D.val).setWidth 14 <<< 12) =
      G.setWidth 14 ||| (BitVec.ofNat 14 S.val <<< 8) |||
        (BitVec.ofNat 14 D.val <<< 12)
    rw [hSv, hDv, BitVec.or_assoc]
  rw [henc, decRef_encRef]

/-! ## Exact `transferCap` branch equations -/

/-! ## Exact `transferByHandle` outcomes -/

/-- The null handle is the identity transfer and returns the null handle.
This equation is shared by the successful `gate_call` and `gate_return`
retirement arms. -/
theorem transferByHandle_eq_zero (τ : MachineState) (D T : DomainId) :
    Machines.Lnp64u.Isa.transferByHandle D T 0 τ = .ok 0 τ := by
  rfl

/-- Exact successful capability lookup from its decoded handle and live-slot
fact.  Gate call and return both need this bridge before invoking the shared
transfer semantics. -/
theorem capLive_eq_selected (τ : MachineState) (D : DomainId)
    (hw : Loom.Word32) (S : Slot) (G : Gen) (e : CapEntry)
    (hdecode : Handle.decode hw = ⟨S, G, e.kind.cls⟩)
    (hlive : (τ.doms D).liveCap S G = some e) :
    Machines.Lnp64u.Isa.capLive D hw τ = .ok (S, G, e) τ := by
  unfold Machines.Lnp64u.Isa.capLive
  simp only [specM_bind, SpecM.get]
  rw [hdecode, hlive]
  simp [SpecM.require]

/-- Once capability lookup and structural transfer have been selected,
`transferByHandle` only installs the returned state and re-encodes the new
recipient-relative reference.  Keeping this monadic reduction here prevents
the two gate retirement arms from duplicating the specification bind tree. -/
theorem transferByHandle_eq_selected (τ τ' : MachineState)
    (D T : DomainId) (hw : Loom.Word32) (S : Slot) (G : Gen)
    (e : CapEntry) (ref : CapRef)
    (hnz : hw ≠ 0)
    (hlive : Machines.Lnp64u.Isa.capLive D hw τ = .ok (S, G, e) τ)
    (htransfer : τ.transferCap D S T = some (τ', ref)) :
    Machines.Lnp64u.Isa.transferByHandle D T hw τ =
      .ok (Handle.encode ⟨ref.slot, ref.gen, e.kind.cls⟩) τ' := by
  unfold Machines.Lnp64u.Isa.transferByHandle
  rw [if_neg hnz]
  change (Machines.Lnp64u.Isa.capLive D hw >>= fun x =>
    let (s, _, e') := x
    SpecM.get >>= fun σ' =>
      match σ'.transferCap D s T with
      | none => SpecM.raise .slotOccupied
      | some (σ'', ref') =>
          SpecM.set σ'' >>= fun _ =>
          pure (Handle.encode ⟨ref'.slot, ref'.gen, e'.kind.cls⟩)) τ = _
  rw [specM_bind, hlive]
  simp only [specM_bind, SpecM.get]
  rw [htransfer]
  rfl

/-- The root-capability branch of `transferCap`, exposed in the same
`installTransferred` vocabulary used by the hardware abstraction. -/
theorem transferCap_eq_selected_none (τ : MachineState)
    (D : DomainId) (S : Slot) (T : DomainId) (NS : Slot) (e : CapEntry)
    (hsource : (τ.doms D).caps S = some e)
    (hslot : τ.freeSlot T = some NS)
    (hlin : e.lineage = none) :
    τ.transferCap D S T =
      some ((((((installTransferred τ T NS e.kind none).reparent
        ⟨D, S, (τ.doms D).slotGen S⟩
        ⟨T, NS, (τ.doms T).slotGen NS⟩).clearSlot D S).sweepRegions).sweepMover,
        ⟨T, NS, (τ.doms T).slotGen NS⟩)) := by
  unfold MachineState.transferCap
  simp only [Option.bind_eq_bind]
  rw [hsource]
  simp only [Option.bind_some]
  rw [hslot]
  simp only [Option.bind_some, hlin]
  rfl

/-- The derived-capability branch of `transferCap`, likewise exposed through
`installTransferred`; the selected free lineage cell receives the moved
source cell unchanged. -/
theorem transferCap_eq_selected_some (τ : MachineState)
    (D : DomainId) (S : Slot) (T : DomainId) (NS : Slot) (e : CapEntry)
    (L : LineageId) (cell : LineageCell) (NL : LineageId)
    (hsource : (τ.doms D).caps S = some e)
    (hslot : τ.freeSlot T = some NS)
    (hlin : e.lineage = some L)
    (hcell : (τ.doms D).lineage L = some cell)
    (hfreeCell : τ.freeCell T = some NL) :
    τ.transferCap D S T =
      some ((((((installTransferred τ T NS e.kind
        (some (NL, cell.parent))).reparent
          ⟨D, S, (τ.doms D).slotGen S⟩
          ⟨T, NS, (τ.doms T).slotGen NS⟩).clearSlot D S).sweepRegions).sweepMover,
        ⟨T, NS, (τ.doms T).slotGen NS⟩)) := by
  unfold MachineState.transferCap
  simp only [Option.bind_eq_bind]
  rw [hsource]
  simp only [Option.bind_some]
  rw [hslot]
  simp only [Option.bind_some, hlin]
  rw [hcell]
  simp only [Option.bind_some]
  rw [hfreeCell]
  simp only [Option.bind_some]
  cases cell
  rfl

/-- Whole-state strengthening of the adjusted-parent algebra: both sides
already agree on every non-domain component, so the domain-map theorem is
enough to rewrite through subsequent clear and sweep operations. -/
theorem installTransferred_reparent_adjusted (τ : MachineState)
    (T : DomainId) (NS : Slot) (kind : CapKind) (NL : LineageId)
    (parent oldRef newRef : CapRef) (hne : newRef ≠ oldRef) :
    (installTransferred τ T NS kind
        (some (NL, if parent = oldRef then newRef else parent))).reparent
      oldRef newRef =
    (installTransferred τ T NS kind (some (NL, parent))).reparent
      oldRef newRef := by
  apply machineState_ext <;> try rfl
  exact installTransferred_reparent_adjusted_doms τ T NS kind NL parent
    oldRef newRef hne

/-! ## Non-domain framing -/

/-- The structural transfer circuit only writes the capability, lineage,
generation, and region-valid banks. This single write-shape theorem is the
frame boundary used to lift the per-domain abstraction to a complete
`MachineState` abstraction. -/
theorem transferChosenA_frame_nondomain (σ acc : Loom.Hw.St)
    (D T : DomainId) (acs : Hw.CapSel) (q : String) (qW : Nat)
    (hcapV : ∀ c : DomainId, ∀ s : Slot, q ≠ Hw.dcapV c s)
    (hkind : ∀ c : DomainId, ∀ s : Slot, q ≠ Hw.dcapKind c s)
    (hlinV : ∀ c : DomainId, ∀ s : Slot, q ≠ Hw.dcapLinV c s)
    (hlin : ∀ c : DomainId, ∀ s : Slot, q ≠ Hw.dcapLin c s)
    (hgen : ∀ c : DomainId, ∀ s : Slot, q ≠ Hw.dgen c s)
    (hcellV : ∀ c : DomainId, ∀ l : LineageId, q ≠ Hw.dcellV c l)
    (hcellPar : ∀ c : DomainId, ∀ l : LineageId, q ≠ Hw.dcellPar c l)
    (hrgnV : ∀ c : DomainId, ∀ r : RegionId, q ≠ Hw.drgnV c r) :
    ((transferChosenA D T acs).run σ acc).regs q qW = acc.regs q qW := by
  let nsE := Hw.freeSlotIdx T
  let oldE := Hw.encRefE (Hw.dLit D) acs.slot acs.gen
  let newE := Hw.encRefE (Hw.dLit T) nsE (Hw.genOfE T nsE)
  let parE := Expr.mux (.eq (Hw.cellParAt D acs.lin) oldE) newE
    (Hw.cellParAt D acs.lin)
  let NS : Slot := finOfBv (by decide) (nsE.eval σ)
  have hns : nsE.eval σ = BitVec.ofNat 4 NS.val :=
    (bv4_slot_iff _ NS).mpr rfl
  rw [show (transferChosenA D T acs).run σ acc =
      (Hw.sweepRegionsA
        (fun dm sl => .and (.eq dm (Hw.dLit D)) (.eq sl acs.slot))).run σ
        ((Hw.clearSlotA D acs.slot acs.linV acs.lin).run σ
          ((Hw.reparentA oldE newE).run σ
            ((Hw.installA T nsE acs.kindW acs.linV (Hw.freeCellIdx T)
              parE).run σ acc))) from rfl]
  rw [sweepRegionsA_frame σ _ _ q qW hrgnV]
  rw [clearSlotA_frame σ _ D acs.slot acs.linV acs.lin q qW
    (hcapV D) (hgen D) (hcellV D)]
  rw [reparentA_frame σ _ oldE newE q qW hcellPar]
  apply installA_selected_frame σ acc T nsE acs.kindW acs.linV
    (Hw.freeCellIdx T) parE NS (q, qW) hns
  · intro h; exact hcapV T NS (congrArg Prod.fst h)
  · intro h; exact hkind T NS (congrArg Prod.fst h)
  · intro h; exact hlinV T NS (congrArg Prod.fst h)
  · intro h; exact hlin T NS (congrArg Prod.fst h)
  · intro h
    exact hcellV T (finOfBv (by decide) ((Hw.freeCellIdx T).eval σ))
      (congrArg Prod.fst h)
  · intro h
    exact hcellPar T (finOfBv (by decide) ((Hw.freeCellIdx T).eval σ))
      (congrArg Prod.fst h)

/-- All register keys read by the non-domain faces of `Hw.abs`. -/
private def transferQuietNames : List (String × Nat) :=
  [ ("cycle", 32),
    ("mov_v", 1), ("mov_owner", 2), ("mov_src", 14), ("mov_dst", 14),
    ("mov_srccur", 12), ("mov_dstcur", 12), ("mov_rem", 13),
    ("mov_status", 12),
    ("if_v", 1), ("if_dom", 2), ("if_word", 32), ("if_cl", 8) ] ++
  (List.finRange numGates).flatMap gateReadNames

/-- Every non-domain register read by `Hw.abs` is framed by a structural
transfer. The disjointness certificate is a finite kernel computation. -/
private theorem transferChosenA_frame_quiet (σ acc : Loom.Hw.St)
    (D T : DomainId) (acs : Hw.CapSel) (q : String × Nat)
    (hq : q ∈ transferQuietNames) :
    ((transferChosenA D T acs).run σ acc).regs q.1 q.2 =
      acc.regs q.1 q.2 := by
  apply transferChosenA_frame_nondomain σ acc D T acs q.1 q.2
  · intro c s
    exact (show ∀ p ∈ transferQuietNames, p.1 ≠ Hw.dcapV c s from by
      fin_cases c <;> fin_cases s <;> decide +kernel) q hq
  · intro c s
    exact (show ∀ p ∈ transferQuietNames, p.1 ≠ Hw.dcapKind c s from by
      fin_cases c <;> fin_cases s <;> decide +kernel) q hq
  · intro c s
    exact (show ∀ p ∈ transferQuietNames, p.1 ≠ Hw.dcapLinV c s from by
      fin_cases c <;> fin_cases s <;> decide +kernel) q hq
  · intro c s
    exact (show ∀ p ∈ transferQuietNames, p.1 ≠ Hw.dcapLin c s from by
      fin_cases c <;> fin_cases s <;> decide +kernel) q hq
  · intro c s
    exact (show ∀ p ∈ transferQuietNames, p.1 ≠ Hw.dgen c s from by
      fin_cases c <;> fin_cases s <;> decide +kernel) q hq
  · intro c l
    exact (show ∀ p ∈ transferQuietNames, p.1 ≠ Hw.dcellV c l from by
      fin_cases c <;> fin_cases l <;> decide +kernel) q hq
  · intro c l
    exact (show ∀ p ∈ transferQuietNames, p.1 ≠ Hw.dcellPar c l from by
      fin_cases c <;> fin_cases l <;> decide +kernel) q hq
  · intro c r
    exact (show ∀ p ∈ transferQuietNames, p.1 ≠ Hw.drgnV c r from by
      fin_cases c <;> fin_cases r <;> decide +kernel) q hq

/-- Accumulator-general structural-transfer frame. A transfer changes only
the abstract domain map; memory, gates, Mover, cycle, and in-flight state are
inherited from the supplied accumulator. -/
theorem abs_transferChosenA_frame_acc (σ acc : Loom.Hw.St)
    (D T : DomainId) (acs : Hw.CapSel) :
    Hw.abs ((transferChosenA D T acs).run σ acc) =
      { Hw.abs acc with
        doms := fun c => Hw.absDom ((transferChosenA D T acs).run σ acc) c } := by
  let out := (transferChosenA D T acs).run σ acc
  apply machineState_ext
  · exact transferChosenA_frame_quiet σ acc D T acs ("cycle", 32)
      (by simp [transferQuietNames])
  · funext a
    exact Loom.Hw.Compile.run_mems_notin "mem" (transferChosenA D T acs)
      (of_decide_eq_true rfl) σ acc a.toNat 32
  · rfl
  · funext g
    apply absGate_congr
    intro q hq
    apply transferChosenA_frame_quiet σ acc D T acs q
    simp only [transferQuietNames, List.mem_append]
    right
    exact List.mem_flatMap.mpr ⟨g, List.mem_finRange g, hq⟩
  · change Hw.absMover ((transferChosenA D T acs).run σ acc) = Hw.absMover acc
    unfold Hw.absMover
    rw [transferChosenA_frame_quiet σ acc D T acs ("mov_v", 1)
        (by simp [transferQuietNames]),
      transferChosenA_frame_quiet σ acc D T acs ("mov_owner", 2)
        (by simp [transferQuietNames]),
      transferChosenA_frame_quiet σ acc D T acs ("mov_src", 14)
        (by simp [transferQuietNames]),
      transferChosenA_frame_quiet σ acc D T acs ("mov_dst", 14)
        (by simp [transferQuietNames]),
      transferChosenA_frame_quiet σ acc D T acs ("mov_srccur", 12)
        (by simp [transferQuietNames]),
      transferChosenA_frame_quiet σ acc D T acs ("mov_dstcur", 12)
        (by simp [transferQuietNames]),
      transferChosenA_frame_quiet σ acc D T acs ("mov_rem", 13)
        (by simp [transferQuietNames]),
      transferChosenA_frame_quiet σ acc D T acs ("mov_status", 12)
        (by simp [transferQuietNames])]
  · change Hw.absInflight ((transferChosenA D T acs).run σ acc) =
      Hw.absInflight acc
    unfold Hw.absInflight
    rw [transferChosenA_frame_quiet σ acc D T acs ("if_v", 1)
        (by simp [transferQuietNames]),
      transferChosenA_frame_quiet σ acc D T acs ("if_dom", 2)
        (by simp [transferQuietNames]),
      transferChosenA_frame_quiet σ acc D T acs ("if_word", 32)
        (by simp [transferQuietNames]),
      transferChosenA_frame_quiet σ acc D T acs ("if_cl", 8)
        (by simp [transferQuietNames])]

/-- Sampled-state specialization retained for existing callers. -/
theorem abs_transferChosenA_frame (σ : Loom.Hw.St)
    (D T : DomainId) (acs : Hw.CapSel) :
    Hw.abs ((transferChosenA D T acs).run σ σ) =
      { Hw.abs σ with
        doms := fun c => Hw.absDom ((transferChosenA D T acs).run σ σ) c } :=
  abs_transferChosenA_frame_acc σ σ D T acs

/-! ## Selected `transferChosenA` branches -/

/-- Accumulator-general root branch of the selected-recipient transfer.
The sampled state supplies all combinational indices; the accumulator is the
architectural base being transformed.  Retirement discharges the bank
agreement hypotheses from refill framing. -/
theorem absDom_transferChosenA_none_acc (σ acc : Loom.Hw.St)
    (D T : DomainId) (acs : Hw.CapSel) (S NS : Slot) (e : CapEntry)
    (hsourceSlot : acs.slot.eval σ = BitVec.ofNat 4 S.val)
    (hsource : ((Hw.abs acc).doms D).caps S = some e)
    (hslot : (Hw.abs acc).freeSlot T = some NS)
    (hslotSample : (Hw.abs σ).freeSlot T = some NS)
    (hlin : e.lineage = none)
    (hlinV : acs.linV.eval σ = 0#1)
    (hkind : acs.kindW.eval σ = Hw.encKind e.kind)
    (hold : Hw.decRef ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩)
    (hV : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hP : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14)
    (hregionV : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgnV c r) 1 = σ.regs (Hw.drgnV c r) 1)
    (hregion : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgn c r) 42 = σ.regs (Hw.drgn c r) 42)
    (hgenAll : ∀ c : DomainId, ∀ s : Slot,
      acc.regs (Hw.dgen c s) 8 = σ.regs (Hw.dgen c s) 8)
    (hwf : Wf (Hw.abs acc)) (c : DomainId) :
    Hw.absDom (transferChosenA D T acs |>.run σ acc) c =
      (((((installTransferred (Hw.abs acc) T NS e.kind none).reparent
        ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩
        ⟨T, NS, ((Hw.abs acc).doms T).slotGen NS⟩).clearSlot D S).sweepRegions).doms c) := by
  let oldE := Hw.encRefE (Hw.dLit D) acs.slot acs.gen
  let nsE := Hw.freeSlotIdx T
  let newE := Hw.encRefE (Hw.dLit T) nsE (Hw.genOfE T nsE)
  let parE := Expr.mux (.eq (Hw.cellParAt D acs.lin) oldE) newE
    (Hw.cellParAt D acs.lin)
  have hns : nsE.eval σ = BitVec.ofNat 4 NS.val :=
    freeSlotIdx_eval σ T NS hslotSample
  have hfin : finOfBv (by decide : 2 ^ 4 = numSlots) (nsE.eval σ) = NS :=
    (bv4_slot_iff _ NS).mp hns
  have hgen : (Hw.genOfE T nsE).eval σ =
      ((Hw.abs acc).doms T).slotGen NS := by
    rw [Hw.genOfE, muxFin_eval (by decide : 2 ^ 4 = numSlots), hfin]
    exact (hgenAll T NS).symm
  have hnew : Hw.decRef (newE.eval σ) =
      ⟨T, NS, ((Hw.abs acc).doms T).slotGen NS⟩ := by
    exact encRefE_decoded_selected σ T nsE (Hw.genOfE T nsE) NS
      (((Hw.abs acc).doms T).slotGen NS) hns hgen
  have hold' : Hw.decRef (oldE.eval σ) =
      ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩ := hold
  have htargetFree : ((Hw.abs acc).doms T).caps NS = none :=
    freeSlot_caps_none (Hw.abs acc) T hslot
  have hnewne : Hw.decRef (newE.eval σ) ≠ Hw.decRef (oldE.eval σ) := by
    rw [hnew, hold]
    exact fresh_destination_ref_ne_source (Hw.abs acc) D S e hsource T NS
      htargetFree
  have hparent : acs.linV.eval σ = 1#1 →
      Hw.decRef (parE.eval σ) ≠ Hw.decRef (oldE.eval σ) := by
    intro _
    exact decRef_transfer_parent_mux_ne σ (Hw.cellParAt D acs.lin) oldE
      newE hnewne
  have hfreeCell : acs.linV.eval σ = 1#1 →
      σ.regs (Hw.dcellV T
        (finOfBv (by decide) ((Hw.freeCellIdx T).eval σ))) 1 ≠ 1#1 := by
    intro h
    rw [hlinV] at h
    contradiction
  have hremoved : removedCell
      ((installTransferred (Hw.abs acc) T NS e.kind
        (if acs.linV.eval σ = 1#1 then
          some (finOfBv (by decide) ((Hw.freeCellIdx T).eval σ),
            Hw.decRef (parE.eval σ)) else none)).reparent
        (Hw.decRef (oldE.eval σ)) (Hw.decRef (newE.eval σ))) D S =
      if acs.linV.eval σ = 1#1 then
        some (finOfBv (by decide) (acs.lin.eval σ)) else none := by
    have hr := removedCell_installTransferred_reparent_source (Hw.abs acc)
      D S e hsource T NS e.kind none htargetFree
      (Hw.decRef (oldE.eval σ)) (Hw.decRef (newE.eval σ))
    simpa [hlinV, hlin] using hr
  rw [show (transferChosenA D T acs).run σ acc =
      (Hw.sweepRegionsA
        (fun dm sl => .and (.eq dm (Hw.dLit D)) (.eq sl acs.slot))).run σ
        ((Hw.clearSlotA D acs.slot acs.linV acs.lin).run σ
          ((Hw.reparentA oldE newE).run σ
            ((Hw.installA T nsE acs.kindW acs.linV (Hw.freeCellIdx T)
              parE).run σ acc))) from rfl]
  simpa [hlinV, hold', hnew] using
    (absDom_transferActions_selected_acc σ acc T nsE acs.kindW acs.linV
      (Hw.freeCellIdx T) parE oldE newE NS e.kind D acs.slot acs.linV
      acs.lin S hns hkind hV hP hregionV hregion (hgenAll D S) hfreeCell
      hparent hsourceSlot hremoved htargetFree hwf c)

/-- Whole-state accumulator-general root transfer. -/
theorem abs_transferChosenA_none_acc (σ acc : Loom.Hw.St)
    (D T : DomainId) (acs : Hw.CapSel) (S NS : Slot) (e : CapEntry)
    (hsourceSlot : acs.slot.eval σ = BitVec.ofNat 4 S.val)
    (hsource : ((Hw.abs acc).doms D).caps S = some e)
    (hslot : (Hw.abs acc).freeSlot T = some NS)
    (hslotSample : (Hw.abs σ).freeSlot T = some NS)
    (hlin : e.lineage = none)
    (hlinV : acs.linV.eval σ = 0#1)
    (hkind : acs.kindW.eval σ = Hw.encKind e.kind)
    (hold : Hw.decRef ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩)
    (hV : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hP : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14)
    (hregionV : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgnV c r) 1 = σ.regs (Hw.drgnV c r) 1)
    (hregion : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgn c r) 42 = σ.regs (Hw.drgn c r) 42)
    (hgenAll : ∀ c : DomainId, ∀ s : Slot,
      acc.regs (Hw.dgen c s) 8 = σ.regs (Hw.dgen c s) 8)
    (hwf : Wf (Hw.abs acc)) :
    Hw.abs ((transferChosenA D T acs).run σ acc) =
      ((((installTransferred (Hw.abs acc) T NS e.kind none).reparent
        ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩
        ⟨T, NS, ((Hw.abs acc).doms T).slotGen NS⟩).clearSlot D S).sweepRegions) := by
  rw [abs_transferChosenA_frame_acc]
  apply machineState_ext <;> try rfl
  funext c
  exact absDom_transferChosenA_none_acc σ acc D T acs S NS e hsourceSlot
    hsource hslot hslotSample hlin hlinV hkind hold hV hP hregionV hregion
    hgenAll hwf c

/-- The selected-recipient hardware transfer of a root capability implements
the explicit root branch of the abstract transfer through its region sweep.
The final abstract Mover sweep is domain-neutral and is composed by the gate
arm's existing Mover bridge. -/
theorem absDom_transferChosenA_none (σ : Loom.Hw.St)
    (D T : DomainId) (acs : Hw.CapSel) (S NS : Slot) (e : CapEntry)
    (hsourceSlot : acs.slot.eval σ = BitVec.ofNat 4 S.val)
    (hsource : ((Hw.abs σ).doms D).caps S = some e)
    (hslot : (Hw.abs σ).freeSlot T = some NS)
    (hlin : e.lineage = none)
    (hlinV : acs.linV.eval σ = 0#1)
    (hkind : acs.kindW.eval σ = Hw.encKind e.kind)
    (hold : Hw.decRef ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩)
    (hwf : Wf (Hw.abs σ)) (c : DomainId) :
    Hw.absDom (transferChosenA D T acs |>.run σ σ) c =
      (((((installTransferred (Hw.abs σ) T NS e.kind none).reparent
        ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩
        ⟨T, NS, ((Hw.abs σ).doms T).slotGen NS⟩).clearSlot D S).sweepRegions).doms c) := by
  let oldE := Hw.encRefE (Hw.dLit D) acs.slot acs.gen
  let nsE := Hw.freeSlotIdx T
  let newE := Hw.encRefE (Hw.dLit T) nsE (Hw.genOfE T nsE)
  let parE := Expr.mux (.eq (Hw.cellParAt D acs.lin) oldE) newE
    (Hw.cellParAt D acs.lin)
  have hns : nsE.eval σ = BitVec.ofNat 4 NS.val :=
    freeSlotIdx_eval σ T NS hslot
  have hfin : finOfBv (by decide : 2 ^ 4 = numSlots) (nsE.eval σ) = NS :=
    (bv4_slot_iff _ NS).mp hns
  have hgen : (Hw.genOfE T nsE).eval σ =
      ((Hw.abs σ).doms T).slotGen NS := by
    rw [Hw.genOfE, muxFin_eval (by decide : 2 ^ 4 = numSlots), hfin]
    rfl
  have hnew : Hw.decRef (newE.eval σ) =
      ⟨T, NS, ((Hw.abs σ).doms T).slotGen NS⟩ := by
    exact encRefE_decoded_selected σ T nsE (Hw.genOfE T nsE) NS
      (((Hw.abs σ).doms T).slotGen NS) hns hgen
  have hold' : Hw.decRef (oldE.eval σ) =
      ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩ := hold
  have htargetFree : ((Hw.abs σ).doms T).caps NS = none :=
    freeSlot_caps_none (Hw.abs σ) T hslot
  have hnewne : Hw.decRef (newE.eval σ) ≠ Hw.decRef (oldE.eval σ) := by
    rw [hnew, hold]
    exact fresh_destination_ref_ne_source (Hw.abs σ) D S e hsource T NS
      htargetFree
  have hparent : acs.linV.eval σ = 1#1 →
      Hw.decRef (parE.eval σ) ≠ Hw.decRef (oldE.eval σ) := by
    intro _
    exact decRef_transfer_parent_mux_ne σ (Hw.cellParAt D acs.lin) oldE
      newE hnewne
  have hfreeCell : acs.linV.eval σ = 1#1 →
      σ.regs (Hw.dcellV T
        (finOfBv (by decide) ((Hw.freeCellIdx T).eval σ))) 1 ≠ 1#1 := by
    intro h
    rw [hlinV] at h
    contradiction
  have hremoved : removedCell
      ((installTransferred (Hw.abs σ) T NS e.kind
        (if acs.linV.eval σ = 1#1 then
          some (finOfBv (by decide) ((Hw.freeCellIdx T).eval σ),
            Hw.decRef (parE.eval σ)) else none)).reparent
        (Hw.decRef (oldE.eval σ)) (Hw.decRef (newE.eval σ))) D S =
      if acs.linV.eval σ = 1#1 then
        some (finOfBv (by decide) (acs.lin.eval σ)) else none := by
    have hr := removedCell_installTransferred_reparent_source (Hw.abs σ)
      D S e hsource T NS e.kind none htargetFree
      (Hw.decRef (oldE.eval σ)) (Hw.decRef (newE.eval σ))
    simpa [hlinV, hlin] using hr
  rw [show (transferChosenA D T acs).run σ σ =
      (Hw.sweepRegionsA
        (fun dm sl => .and (.eq dm (Hw.dLit D)) (.eq sl acs.slot))).run σ
        ((Hw.clearSlotA D acs.slot acs.linV acs.lin).run σ
          ((Hw.reparentA oldE newE).run σ
            ((Hw.installA T nsE acs.kindW acs.linV (Hw.freeCellIdx T)
              parE).run σ σ))) from rfl]
  simpa [hlinV, hold', hnew] using
    (absDom_transferActions_selected σ T nsE acs.kindW acs.linV
      (Hw.freeCellIdx T) parE oldE newE NS e.kind D acs.slot acs.linV
      acs.lin S hns hkind hfreeCell hparent hsourceSlot hremoved htargetFree
      hwf c)

/-- The selected-recipient hardware transfer of a derived capability
implements the explicit derived branch of the abstract transfer. The
hardware pre-adjusts the moved cell's parent; the whole-state adjustment
lemma shows this is equivalent to the specification's later reparent pass. -/
theorem absDom_transferChosenA_some_acc (σ acc : Loom.Hw.St)
    (D T : DomainId) (acs : Hw.CapSel) (S NS : Slot) (e : CapEntry)
    (L : LineageId) (cell : LineageCell) (NL : LineageId)
    (hsourceSlot : acs.slot.eval σ = BitVec.ofNat 4 S.val)
    (hsource : ((Hw.abs acc).doms D).caps S = some e)
    (hslot : (Hw.abs acc).freeSlot T = some NS)
    (hslotSample : (Hw.abs σ).freeSlot T = some NS)
    (hlin : e.lineage = some L)
    (hcell : ((Hw.abs acc).doms D).lineage L = some cell)
    (hcellSample : ((Hw.abs σ).doms D).lineage L = some cell)
    (hfreeCell : (Hw.abs acc).freeCell T = some NL)
    (hfreeCellSample : (Hw.abs σ).freeCell T = some NL)
    (hlinV : acs.linV.eval σ = 1#1)
    (hlinIdx : acs.lin.eval σ = BitVec.ofNat 4 L.val)
    (hkind : acs.kindW.eval σ = Hw.encKind e.kind)
    (hold : Hw.decRef ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩)
    (hV : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hP : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14)
    (hregionV : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgnV c r) 1 = σ.regs (Hw.drgnV c r) 1)
    (hregion : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgn c r) 42 = σ.regs (Hw.drgn c r) 42)
    (hgenAll : ∀ c : DomainId, ∀ s : Slot,
      acc.regs (Hw.dgen c s) 8 = σ.regs (Hw.dgen c s) 8)
    (hwf : Wf (Hw.abs acc)) (c : DomainId) :
    Hw.absDom (transferChosenA D T acs |>.run σ acc) c =
      (((((installTransferred (Hw.abs acc) T NS e.kind
        (some (NL, cell.parent))).reparent
          ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩
          ⟨T, NS, ((Hw.abs acc).doms T).slotGen NS⟩).clearSlot D S).sweepRegions).doms c) := by
  let oldE := Hw.encRefE (Hw.dLit D) acs.slot acs.gen
  let nsE := Hw.freeSlotIdx T
  let newE := Hw.encRefE (Hw.dLit T) nsE (Hw.genOfE T nsE)
  let srcPar := Hw.cellParAt D acs.lin
  let parE := Expr.mux (.eq srcPar oldE) newE srcPar
  have hns : nsE.eval σ = BitVec.ofNat 4 NS.val :=
    freeSlotIdx_eval σ T NS hslotSample
  have hnl : (Hw.freeCellIdx T).eval σ = BitVec.ofNat 4 NL.val :=
    freeCellIdx_eval σ T NL hfreeCellSample
  have hfin : finOfBv (by decide : 2 ^ 4 = numSlots) (nsE.eval σ) = NS :=
    (bv4_slot_iff _ NS).mp hns
  have hgen : (Hw.genOfE T nsE).eval σ =
      ((Hw.abs acc).doms T).slotGen NS := by
    rw [Hw.genOfE, muxFin_eval (by decide : 2 ^ 4 = numSlots), hfin]
    exact (hgenAll T NS).symm
  have hnew : Hw.decRef (newE.eval σ) =
      ⟨T, NS, ((Hw.abs acc).doms T).slotGen NS⟩ := by
    exact encRefE_decoded_selected σ T nsE (Hw.genOfE T nsE) NS
      (((Hw.abs acc).doms T).slotGen NS) hns hgen
  have hold' : Hw.decRef (oldE.eval σ) =
      ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩ := hold
  have htargetFree : ((Hw.abs acc).doms T).caps NS = none :=
    freeSlot_caps_none (Hw.abs acc) T hslot
  have hnewne : Hw.decRef (newE.eval σ) ≠ Hw.decRef (oldE.eval σ) := by
    rw [hnew, hold']
    exact fresh_destination_ref_ne_source (Hw.abs acc) D S e hsource T NS
      htargetFree
  have hparent : acs.linV.eval σ = 1#1 →
      Hw.decRef (parE.eval σ) ≠ Hw.decRef (oldE.eval σ) := by
    intro _
    exact decRef_transfer_parent_mux_ne σ srcPar oldE newE hnewne
  have htargetCellFree : acs.linV.eval σ = 1#1 →
      σ.regs (Hw.dcellV T
        (finOfBv (by decide) ((Hw.freeCellIdx T).eval σ))) 1 ≠ 1#1 := by
    intro _ hv
    have hnone := freeCell_none (Hw.abs σ) T hfreeCellSample
    have hNL : finOfBv (by decide : 2 ^ 4 = numLineage)
        ((Hw.freeCellIdx T).eval σ) = NL := (bv4_slot_iff _ NL).mp hnl
    change (if σ.regs (Hw.dcellV T NL) 1 = 1#1 then
      some (LineageCell.mk (Hw.decRef (σ.regs (Hw.dcellPar T NL) 14)))
      else none) = none at hnone
    have hvNL : σ.regs (Hw.dcellV T NL) 1 = 1#1 := by
      rw [← hNL]
      exact hv
    rw [hvNL, if_pos rfl] at hnone
    contradiction
  have hremoved : removedCell
      ((installTransferred (Hw.abs acc) T NS e.kind
        (if acs.linV.eval σ = 1#1 then
          some (finOfBv (by decide) ((Hw.freeCellIdx T).eval σ),
            Hw.decRef (parE.eval σ)) else none)).reparent
        (Hw.decRef (oldE.eval σ)) (Hw.decRef (newE.eval σ))) D S =
      if acs.linV.eval σ = 1#1 then
        some (finOfBv (by decide) (acs.lin.eval σ)) else none := by
    have hr := removedCell_installTransferred_reparent_source (Hw.abs acc)
      D S e hsource T NS e.kind
      (some (NL, Hw.decRef (parE.eval σ))) htargetFree
      (Hw.decRef (oldE.eval σ)) (Hw.decRef (newE.eval σ))
    have hL : finOfBv (by decide : 2 ^ 4 = numLineage) (acs.lin.eval σ) = L :=
      (bv4_slot_iff _ L).mp hlinIdx
    simpa [hlinV, hlin, hL, hnl] using hr
  have hsrcParent : Hw.decRef (srcPar.eval σ) = cell.parent := by
    rw [cellParAt_eval σ D acs.lin L hlinIdx]
    change (if σ.regs (Hw.dcellV D L) 1 = 1#1 then
      some (LineageCell.mk (Hw.decRef (σ.regs (Hw.dcellPar D L) 14)))
      else none) = some cell at hcellSample
    by_cases hv : σ.regs (Hw.dcellV D L) 1 = 1#1
    · rw [if_pos hv] at hcellSample
      exact congrArg LineageCell.parent (Option.some.inj hcellSample)
    · rw [if_neg hv] at hcellSample
      contradiction
  have hparDecoded : Hw.decRef (parE.eval σ) =
      if cell.parent = Hw.decRef (oldE.eval σ) then
        Hw.decRef (newE.eval σ) else cell.parent := by
    by_cases hp : srcPar.eval σ = oldE.eval σ
    · have hp' : cell.parent = Hw.decRef (oldE.eval σ) := by
        rw [← hsrcParent, hp]
      simp [parE, Expr.eval, hp, hp', hnew]
    · have hp' : cell.parent ≠ Hw.decRef (oldE.eval σ) := by
        intro heq
        apply hp
        rw [← encRef_decRef (srcPar.eval σ), hsrcParent, heq,
          encRef_decRef]
      simp [parE, Expr.eval, hp, hp', hsrcParent]
  rw [show (transferChosenA D T acs).run σ acc =
      (Hw.sweepRegionsA
        (fun dm sl => .and (.eq dm (Hw.dLit D)) (.eq sl acs.slot))).run σ
        ((Hw.clearSlotA D acs.slot acs.linV acs.lin).run σ
          ((Hw.reparentA oldE newE).run σ
            ((Hw.installA T nsE acs.kindW acs.linV (Hw.freeCellIdx T)
              parE).run σ acc))) from rfl]
  have habs := absDom_transferActions_selected_acc σ acc T nsE acs.kindW
    acs.linV (Hw.freeCellIdx T) parE oldE newE NS e.kind D acs.slot
    acs.linV acs.lin S hns hkind hV hP hregionV hregion (hgenAll D S)
    htargetCellFree hparent hsourceSlot hremoved htargetFree hwf c
  simp only [hlinV, if_pos, hnl] at habs
  have hNL' : finOfBv (by decide : 2 ^ 4 = numLineage)
      (BitVec.ofNat 4 NL.val) = NL :=
    (bv4_slot_iff _ NL).mp rfl
  rw [hNL'] at habs
  rw [hparDecoded, hold', hnew] at habs
  rw [installTransferred_reparent_adjusted (Hw.abs acc) T NS e.kind NL
    cell.parent
    ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩
    ⟨T, NS, ((Hw.abs acc).doms T).slotGen NS⟩
    (fresh_destination_ref_ne_source (Hw.abs acc) D S e hsource T NS
      htargetFree)] at habs
  exact habs

/-- Whole-state accumulator-general derived transfer. -/
theorem abs_transferChosenA_some_acc (σ acc : Loom.Hw.St)
    (D T : DomainId) (acs : Hw.CapSel) (S NS : Slot) (e : CapEntry)
    (L : LineageId) (cell : LineageCell) (NL : LineageId)
    (hsourceSlot : acs.slot.eval σ = BitVec.ofNat 4 S.val)
    (hsource : ((Hw.abs acc).doms D).caps S = some e)
    (hslot : (Hw.abs acc).freeSlot T = some NS)
    (hslotSample : (Hw.abs σ).freeSlot T = some NS)
    (hlin : e.lineage = some L)
    (hcell : ((Hw.abs acc).doms D).lineage L = some cell)
    (hcellSample : ((Hw.abs σ).doms D).lineage L = some cell)
    (hfreeCell : (Hw.abs acc).freeCell T = some NL)
    (hfreeCellSample : (Hw.abs σ).freeCell T = some NL)
    (hlinV : acs.linV.eval σ = 1#1)
    (hlinIdx : acs.lin.eval σ = BitVec.ofNat 4 L.val)
    (hkind : acs.kindW.eval σ = Hw.encKind e.kind)
    (hold : Hw.decRef ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩)
    (hV : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hP : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14)
    (hregionV : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgnV c r) 1 = σ.regs (Hw.drgnV c r) 1)
    (hregion : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgn c r) 42 = σ.regs (Hw.drgn c r) 42)
    (hgenAll : ∀ c : DomainId, ∀ s : Slot,
      acc.regs (Hw.dgen c s) 8 = σ.regs (Hw.dgen c s) 8)
    (hwf : Wf (Hw.abs acc)) :
    Hw.abs ((transferChosenA D T acs).run σ acc) =
      ((((installTransferred (Hw.abs acc) T NS e.kind
        (some (NL, cell.parent))).reparent
          ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩
          ⟨T, NS, ((Hw.abs acc).doms T).slotGen NS⟩).clearSlot D S).sweepRegions) := by
  rw [abs_transferChosenA_frame_acc]
  apply machineState_ext <;> try rfl
  funext c
  exact absDom_transferChosenA_some_acc σ acc D T acs S NS e L cell NL
    hsourceSlot hsource hslot hslotSample hlin hcell hcellSample hfreeCell
    hfreeCellSample hlinV hlinIdx hkind hold hV hP hregionV hregion hgenAll
    hwf c

/-- Dynamic-recipient root transfer over an arbitrary accumulator. -/
theorem abs_transferA_none_acc (σ acc : Loom.Hw.St)
    (D T : DomainId) (toE : Expr 2) (acs : Hw.CapSel)
    (S NS : Slot) (e : CapEntry)
    (hto : finOfBv (by decide : 2 ^ 2 = numDomains) (toE.eval σ) = T)
    (hsourceSlot : acs.slot.eval σ = BitVec.ofNat 4 S.val)
    (hsource : ((Hw.abs acc).doms D).caps S = some e)
    (hslot : (Hw.abs acc).freeSlot T = some NS)
    (hslotSample : (Hw.abs σ).freeSlot T = some NS)
    (hlin : e.lineage = none)
    (hlinV : acs.linV.eval σ = 0#1)
    (hkind : acs.kindW.eval σ = Hw.encKind e.kind)
    (hold : Hw.decRef ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩)
    (hV : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hP : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14)
    (hregionV : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgnV c r) 1 = σ.regs (Hw.drgnV c r) 1)
    (hregion : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgn c r) 42 = σ.regs (Hw.drgn c r) 42)
    (hgenAll : ∀ c : DomainId, ∀ s : Slot,
      acc.regs (Hw.dgen c s) 8 = σ.regs (Hw.dgen c s) 8)
    (hwf : Wf (Hw.abs acc)) :
    Hw.abs ((Hw.transferA D toE acs).run σ acc) =
      ((((installTransferred (Hw.abs acc) T NS e.kind none).reparent
        ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩
        ⟨T, NS, ((Hw.abs acc).doms T).slotGen NS⟩).clearSlot D S).sweepRegions) := by
  rw [transferA_run_selected, hto]
  exact abs_transferChosenA_none_acc σ acc D T acs S NS e hsourceSlot
    hsource hslot hslotSample hlin hlinV hkind hold hV hP hregionV hregion
    hgenAll hwf

/-- Dynamic-recipient derived transfer over an arbitrary accumulator. -/
theorem abs_transferA_some_acc (σ acc : Loom.Hw.St)
    (D T : DomainId) (toE : Expr 2) (acs : Hw.CapSel)
    (S NS : Slot) (e : CapEntry) (L : LineageId)
    (cell : LineageCell) (NL : LineageId)
    (hto : finOfBv (by decide : 2 ^ 2 = numDomains) (toE.eval σ) = T)
    (hsourceSlot : acs.slot.eval σ = BitVec.ofNat 4 S.val)
    (hsource : ((Hw.abs acc).doms D).caps S = some e)
    (hslot : (Hw.abs acc).freeSlot T = some NS)
    (hslotSample : (Hw.abs σ).freeSlot T = some NS)
    (hlin : e.lineage = some L)
    (hcell : ((Hw.abs acc).doms D).lineage L = some cell)
    (hcellSample : ((Hw.abs σ).doms D).lineage L = some cell)
    (hfreeCell : (Hw.abs acc).freeCell T = some NL)
    (hfreeCellSample : (Hw.abs σ).freeCell T = some NL)
    (hlinV : acs.linV.eval σ = 1#1)
    (hlinIdx : acs.lin.eval σ = BitVec.ofNat 4 L.val)
    (hkind : acs.kindW.eval σ = Hw.encKind e.kind)
    (hold : Hw.decRef ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩)
    (hV : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hP : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14)
    (hregionV : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgnV c r) 1 = σ.regs (Hw.drgnV c r) 1)
    (hregion : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgn c r) 42 = σ.regs (Hw.drgn c r) 42)
    (hgenAll : ∀ c : DomainId, ∀ s : Slot,
      acc.regs (Hw.dgen c s) 8 = σ.regs (Hw.dgen c s) 8)
    (hwf : Wf (Hw.abs acc)) :
    Hw.abs ((Hw.transferA D toE acs).run σ acc) =
      ((((installTransferred (Hw.abs acc) T NS e.kind
        (some (NL, cell.parent))).reparent
          ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩
          ⟨T, NS, ((Hw.abs acc).doms T).slotGen NS⟩).clearSlot D S).sweepRegions) := by
  rw [transferA_run_selected, hto]
  exact abs_transferChosenA_some_acc σ acc D T acs S NS e L cell NL
    hsourceSlot hsource hslot hslotSample hlin hcell hcellSample hfreeCell
    hfreeCellSample hlinV hlinIdx hkind hold hV hP hregionV hregion hgenAll
    hwf

theorem absDom_transferChosenA_some (σ : Loom.Hw.St)
    (D T : DomainId) (acs : Hw.CapSel) (S NS : Slot) (e : CapEntry)
    (L : LineageId) (cell : LineageCell) (NL : LineageId)
    (hsourceSlot : acs.slot.eval σ = BitVec.ofNat 4 S.val)
    (hsource : ((Hw.abs σ).doms D).caps S = some e)
    (hslot : (Hw.abs σ).freeSlot T = some NS)
    (hlin : e.lineage = some L)
    (hcell : ((Hw.abs σ).doms D).lineage L = some cell)
    (hfreeCell : (Hw.abs σ).freeCell T = some NL)
    (hlinV : acs.linV.eval σ = 1#1)
    (hlinIdx : acs.lin.eval σ = BitVec.ofNat 4 L.val)
    (hkind : acs.kindW.eval σ = Hw.encKind e.kind)
    (hold : Hw.decRef ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩)
    (hwf : Wf (Hw.abs σ)) (c : DomainId) :
    Hw.absDom (transferChosenA D T acs |>.run σ σ) c =
      (((((installTransferred (Hw.abs σ) T NS e.kind
        (some (NL, cell.parent))).reparent
          ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩
          ⟨T, NS, ((Hw.abs σ).doms T).slotGen NS⟩).clearSlot D S).sweepRegions).doms c) := by
  let oldE := Hw.encRefE (Hw.dLit D) acs.slot acs.gen
  let nsE := Hw.freeSlotIdx T
  let newE := Hw.encRefE (Hw.dLit T) nsE (Hw.genOfE T nsE)
  let srcPar := Hw.cellParAt D acs.lin
  let parE := Expr.mux (.eq srcPar oldE) newE srcPar
  have hns : nsE.eval σ = BitVec.ofNat 4 NS.val :=
    freeSlotIdx_eval σ T NS hslot
  have hnl : (Hw.freeCellIdx T).eval σ = BitVec.ofNat 4 NL.val :=
    freeCellIdx_eval σ T NL hfreeCell
  have hfin : finOfBv (by decide : 2 ^ 4 = numSlots) (nsE.eval σ) = NS :=
    (bv4_slot_iff _ NS).mp hns
  have hgen : (Hw.genOfE T nsE).eval σ =
      ((Hw.abs σ).doms T).slotGen NS := by
    rw [Hw.genOfE, muxFin_eval (by decide : 2 ^ 4 = numSlots), hfin]
    rfl
  have hnew : Hw.decRef (newE.eval σ) =
      ⟨T, NS, ((Hw.abs σ).doms T).slotGen NS⟩ := by
    exact encRefE_decoded_selected σ T nsE (Hw.genOfE T nsE) NS
      (((Hw.abs σ).doms T).slotGen NS) hns hgen
  have hold' : Hw.decRef (oldE.eval σ) =
      ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩ := hold
  have htargetFree : ((Hw.abs σ).doms T).caps NS = none :=
    freeSlot_caps_none (Hw.abs σ) T hslot
  have hnewne : Hw.decRef (newE.eval σ) ≠ Hw.decRef (oldE.eval σ) := by
    rw [hnew, hold']
    exact fresh_destination_ref_ne_source (Hw.abs σ) D S e hsource T NS
      htargetFree
  have hparent : acs.linV.eval σ = 1#1 →
      Hw.decRef (parE.eval σ) ≠ Hw.decRef (oldE.eval σ) := by
    intro _
    exact decRef_transfer_parent_mux_ne σ srcPar oldE newE hnewne
  have htargetCellFree : acs.linV.eval σ = 1#1 →
      σ.regs (Hw.dcellV T
        (finOfBv (by decide) ((Hw.freeCellIdx T).eval σ))) 1 ≠ 1#1 := by
    intro _ hv
    have hnone := freeCell_none (Hw.abs σ) T hfreeCell
    have hNL : finOfBv (by decide : 2 ^ 4 = numLineage)
        ((Hw.freeCellIdx T).eval σ) = NL := (bv4_slot_iff _ NL).mp hnl
    change (if σ.regs (Hw.dcellV T NL) 1 = 1#1 then
      some (LineageCell.mk (Hw.decRef (σ.regs (Hw.dcellPar T NL) 14)))
      else none) = none at hnone
    have hvNL : σ.regs (Hw.dcellV T NL) 1 = 1#1 := by
      rw [← hNL]
      exact hv
    rw [hvNL, if_pos rfl] at hnone
    contradiction
  have hremoved : removedCell
      ((installTransferred (Hw.abs σ) T NS e.kind
        (if acs.linV.eval σ = 1#1 then
          some (finOfBv (by decide) ((Hw.freeCellIdx T).eval σ),
            Hw.decRef (parE.eval σ)) else none)).reparent
        (Hw.decRef (oldE.eval σ)) (Hw.decRef (newE.eval σ))) D S =
      if acs.linV.eval σ = 1#1 then
        some (finOfBv (by decide) (acs.lin.eval σ)) else none := by
    have hr := removedCell_installTransferred_reparent_source (Hw.abs σ)
      D S e hsource T NS e.kind
      (some (NL, Hw.decRef (parE.eval σ))) htargetFree
      (Hw.decRef (oldE.eval σ)) (Hw.decRef (newE.eval σ))
    have hL : finOfBv (by decide : 2 ^ 4 = numLineage) (acs.lin.eval σ) = L :=
      (bv4_slot_iff _ L).mp hlinIdx
    simpa [hlinV, hlin, hL, hnl] using hr
  have hsrcParent : Hw.decRef (srcPar.eval σ) = cell.parent := by
    rw [cellParAt_eval σ D acs.lin L hlinIdx]
    change (if σ.regs (Hw.dcellV D L) 1 = 1#1 then
      some (LineageCell.mk (Hw.decRef (σ.regs (Hw.dcellPar D L) 14)))
      else none) = some cell at hcell
    by_cases hv : σ.regs (Hw.dcellV D L) 1 = 1#1
    · rw [if_pos hv] at hcell
      exact congrArg LineageCell.parent (Option.some.inj hcell)
    · rw [if_neg hv] at hcell
      contradiction
  have hparDecoded : Hw.decRef (parE.eval σ) =
      if cell.parent = Hw.decRef (oldE.eval σ) then
        Hw.decRef (newE.eval σ) else cell.parent := by
    by_cases hp : srcPar.eval σ = oldE.eval σ
    · have hp' : cell.parent = Hw.decRef (oldE.eval σ) := by
        rw [← hsrcParent, hp]
      simp [parE, Expr.eval, hp, hp', hnew]
    · have hp' : cell.parent ≠ Hw.decRef (oldE.eval σ) := by
        intro heq
        apply hp
        rw [← encRef_decRef (srcPar.eval σ), hsrcParent, heq,
          encRef_decRef]
      simp [parE, Expr.eval, hp, hp', hsrcParent]
  rw [show (transferChosenA D T acs).run σ σ =
      (Hw.sweepRegionsA
        (fun dm sl => .and (.eq dm (Hw.dLit D)) (.eq sl acs.slot))).run σ
        ((Hw.clearSlotA D acs.slot acs.linV acs.lin).run σ
          ((Hw.reparentA oldE newE).run σ
            ((Hw.installA T nsE acs.kindW acs.linV (Hw.freeCellIdx T)
              parE).run σ σ))) from rfl]
  have habs := absDom_transferActions_selected σ T nsE acs.kindW acs.linV
    (Hw.freeCellIdx T) parE oldE newE NS e.kind D acs.slot acs.linV acs.lin S
    hns hkind htargetCellFree hparent hsourceSlot hremoved htargetFree hwf c
  simp only [hlinV, if_pos, hnl] at habs
  have hNL' : finOfBv (by decide : 2 ^ 4 = numLineage)
      (BitVec.ofNat 4 NL.val) = NL :=
    (bv4_slot_iff _ NL).mp rfl
  rw [hNL'] at habs
  rw [hparDecoded, hold', hnew] at habs
  rw [installTransferred_reparent_adjusted (Hw.abs σ) T NS e.kind NL
    cell.parent
    ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩
    ⟨T, NS, ((Hw.abs σ).doms T).slotGen NS⟩
    (fresh_destination_ref_ne_source (Hw.abs σ) D S e hsource T NS
      htargetFree)] at habs
  exact habs

/-! ## Dynamic-recipient `transferA` corollaries -/
/-! ## Whole-state transfer abstraction -/

/-- Whole-state root branch of the selected-recipient transfer. -/
theorem abs_transferChosenA_none (σ : Loom.Hw.St)
    (D T : DomainId) (acs : Hw.CapSel) (S NS : Slot) (e : CapEntry)
    (hsourceSlot : acs.slot.eval σ = BitVec.ofNat 4 S.val)
    (hsource : ((Hw.abs σ).doms D).caps S = some e)
    (hslot : (Hw.abs σ).freeSlot T = some NS)
    (hlin : e.lineage = none)
    (hlinV : acs.linV.eval σ = 0#1)
    (hkind : acs.kindW.eval σ = Hw.encKind e.kind)
    (hold : Hw.decRef ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩)
    (hwf : Wf (Hw.abs σ)) :
    Hw.abs ((transferChosenA D T acs).run σ σ) =
      ((((installTransferred (Hw.abs σ) T NS e.kind none).reparent
        ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩
        ⟨T, NS, ((Hw.abs σ).doms T).slotGen NS⟩).clearSlot D S).sweepRegions) := by
  rw [abs_transferChosenA_frame]
  apply machineState_ext <;> try rfl
  funext c
  exact absDom_transferChosenA_none σ D T acs S NS e hsourceSlot hsource
    hslot hlin hlinV hkind hold hwf c

/-- Whole-state derived branch of the selected-recipient transfer. -/
theorem abs_transferChosenA_some (σ : Loom.Hw.St)
    (D T : DomainId) (acs : Hw.CapSel) (S NS : Slot) (e : CapEntry)
    (L : LineageId) (cell : LineageCell) (NL : LineageId)
    (hsourceSlot : acs.slot.eval σ = BitVec.ofNat 4 S.val)
    (hsource : ((Hw.abs σ).doms D).caps S = some e)
    (hslot : (Hw.abs σ).freeSlot T = some NS)
    (hlin : e.lineage = some L)
    (hcell : ((Hw.abs σ).doms D).lineage L = some cell)
    (hfreeCell : (Hw.abs σ).freeCell T = some NL)
    (hlinV : acs.linV.eval σ = 1#1)
    (hlinIdx : acs.lin.eval σ = BitVec.ofNat 4 L.val)
    (hkind : acs.kindW.eval σ = Hw.encKind e.kind)
    (hold : Hw.decRef ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩)
    (hwf : Wf (Hw.abs σ)) :
    Hw.abs ((transferChosenA D T acs).run σ σ) =
      ((((installTransferred (Hw.abs σ) T NS e.kind
        (some (NL, cell.parent))).reparent
          ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩
          ⟨T, NS, ((Hw.abs σ).doms T).slotGen NS⟩).clearSlot D S).sweepRegions) := by
  rw [abs_transferChosenA_frame]
  apply machineState_ext <;> try rfl
  funext c
  exact absDom_transferChosenA_some σ D T acs S NS e L cell NL hsourceSlot
    hsource hslot hlin hcell hfreeCell hlinV hlinIdx hkind hold hwf c

/-- Root branch of the public `transferA`, after decoding its dynamic
recipient expression. -/
theorem absDom_transferA_none (σ : Loom.Hw.St)
    (D T : DomainId) (toE : Expr 2) (acs : Hw.CapSel)
    (S NS : Slot) (e : CapEntry)
    (hto : finOfBv (by decide : 2 ^ 2 = numDomains) (toE.eval σ) = T)
    (hsourceSlot : acs.slot.eval σ = BitVec.ofNat 4 S.val)
    (hsource : ((Hw.abs σ).doms D).caps S = some e)
    (hslot : (Hw.abs σ).freeSlot T = some NS)
    (hlin : e.lineage = none)
    (hlinV : acs.linV.eval σ = 0#1)
    (hkind : acs.kindW.eval σ = Hw.encKind e.kind)
    (hold : Hw.decRef ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩)
    (hwf : Wf (Hw.abs σ)) (c : DomainId) :
    Hw.absDom ((Hw.transferA D toE acs).run σ σ) c =
      (((((installTransferred (Hw.abs σ) T NS e.kind none).reparent
        ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩
        ⟨T, NS, ((Hw.abs σ).doms T).slotGen NS⟩).clearSlot D S).sweepRegions).doms c) := by
  rw [transferA_run_selected, hto]
  exact absDom_transferChosenA_none σ D T acs S NS e hsourceSlot hsource
    hslot hlin hlinV hkind hold hwf c

/-- Derived branch of the public `transferA`, after decoding its dynamic
recipient expression. -/
theorem absDom_transferA_some (σ : Loom.Hw.St)
    (D T : DomainId) (toE : Expr 2) (acs : Hw.CapSel)
    (S NS : Slot) (e : CapEntry) (L : LineageId)
    (cell : LineageCell) (NL : LineageId)
    (hto : finOfBv (by decide : 2 ^ 2 = numDomains) (toE.eval σ) = T)
    (hsourceSlot : acs.slot.eval σ = BitVec.ofNat 4 S.val)
    (hsource : ((Hw.abs σ).doms D).caps S = some e)
    (hslot : (Hw.abs σ).freeSlot T = some NS)
    (hlin : e.lineage = some L)
    (hcell : ((Hw.abs σ).doms D).lineage L = some cell)
    (hfreeCell : (Hw.abs σ).freeCell T = some NL)
    (hlinV : acs.linV.eval σ = 1#1)
    (hlinIdx : acs.lin.eval σ = BitVec.ofNat 4 L.val)
    (hkind : acs.kindW.eval σ = Hw.encKind e.kind)
    (hold : Hw.decRef ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩)
    (hwf : Wf (Hw.abs σ)) (c : DomainId) :
    Hw.absDom ((Hw.transferA D toE acs).run σ σ) c =
      (((((installTransferred (Hw.abs σ) T NS e.kind
        (some (NL, cell.parent))).reparent
          ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩
          ⟨T, NS, ((Hw.abs σ).doms T).slotGen NS⟩).clearSlot D S).sweepRegions).doms c) := by
  rw [transferA_run_selected, hto]
  exact absDom_transferChosenA_some σ D T acs S NS e L cell NL hsourceSlot
    hsource hslot hlin hcell hfreeCell hlinV hlinIdx hkind hold hwf c

/-! ## Whole-state dynamic-recipient corollaries -/

/-- Whole-state root branch of the public `Hw.transferA`. -/
theorem abs_transferA_none (σ : Loom.Hw.St)
    (D T : DomainId) (toE : Expr 2) (acs : Hw.CapSel)
    (S NS : Slot) (e : CapEntry)
    (hto : finOfBv (by decide : 2 ^ 2 = numDomains) (toE.eval σ) = T)
    (hsourceSlot : acs.slot.eval σ = BitVec.ofNat 4 S.val)
    (hsource : ((Hw.abs σ).doms D).caps S = some e)
    (hslot : (Hw.abs σ).freeSlot T = some NS)
    (hlin : e.lineage = none)
    (hlinV : acs.linV.eval σ = 0#1)
    (hkind : acs.kindW.eval σ = Hw.encKind e.kind)
    (hold : Hw.decRef ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩)
    (hwf : Wf (Hw.abs σ)) :
    Hw.abs ((Hw.transferA D toE acs).run σ σ) =
      ((((installTransferred (Hw.abs σ) T NS e.kind none).reparent
        ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩
        ⟨T, NS, ((Hw.abs σ).doms T).slotGen NS⟩).clearSlot D S).sweepRegions) := by
  rw [transferA_run_selected, hto]
  exact abs_transferChosenA_none σ D T acs S NS e hsourceSlot hsource hslot
    hlin hlinV hkind hold hwf

/-- Whole-state derived branch of the public `Hw.transferA`. -/
theorem abs_transferA_some (σ : Loom.Hw.St)
    (D T : DomainId) (toE : Expr 2) (acs : Hw.CapSel)
    (S NS : Slot) (e : CapEntry) (L : LineageId)
    (cell : LineageCell) (NL : LineageId)
    (hto : finOfBv (by decide : 2 ^ 2 = numDomains) (toE.eval σ) = T)
    (hsourceSlot : acs.slot.eval σ = BitVec.ofNat 4 S.val)
    (hsource : ((Hw.abs σ).doms D).caps S = some e)
    (hslot : (Hw.abs σ).freeSlot T = some NS)
    (hlin : e.lineage = some L)
    (hcell : ((Hw.abs σ).doms D).lineage L = some cell)
    (hfreeCell : (Hw.abs σ).freeCell T = some NL)
    (hlinV : acs.linV.eval σ = 1#1)
    (hlinIdx : acs.lin.eval σ = BitVec.ofNat 4 L.val)
    (hkind : acs.kindW.eval σ = Hw.encKind e.kind)
    (hold : Hw.decRef ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩)
    (hwf : Wf (Hw.abs σ)) :
    Hw.abs ((Hw.transferA D toE acs).run σ σ) =
      ((((installTransferred (Hw.abs σ) T NS e.kind
        (some (NL, cell.parent))).reparent
          ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩
          ⟨T, NS, ((Hw.abs σ).doms T).slotGen NS⟩).clearSlot D S).sweepRegions) := by
  rw [transferA_run_selected, hto]
  exact abs_transferChosenA_some σ D T acs S NS e L cell NL hsourceSlot
    hsource hslot hlin hcell hfreeCell hlinV hlinIdx hkind hold hwf

/-! ## Shared transfer-placement check -/

/-- Without lineage, the shared transfer check is blocked exactly when the
recipient has no free capability slot. -/
theorem transferBlocked_eval_no_lineage (σ : Loom.Hw.St)
    (D T : DomainId) (toE : Expr 2) (acs : Hw.CapSel)
    (hto : finOfBv (by decide : 2 ^ 2 = numDomains) (toE.eval σ) = T)
    (hlinV : acs.linV.eval σ = 0#1) :
    (Hw.transferBlocked D toE acs).eval σ = 1#1 ↔
      ¬((Hw.abs σ).freeSlot T).isSome := by
  have hslot := freeSlotV_eval σ T
  simp only [Hw.transferBlocked, Expr.eval]
  rw [muxFin_eval (by decide : 2 ^ 2 = numDomains), hto, hlinV]
  by_cases hv : (Hw.freeSlotV T).eval σ = 1#1
  · rw [hv]
    simp [hslot.mp hv]
  · have hz : (Hw.freeSlotV T).eval σ = 0#1 := bv1_ne_one.mp hv
    have hs : ¬((Hw.abs σ).freeSlot T).isSome := by
      intro his
      exact hv (hslot.mpr his)
    simp [hz, hs]

/-- With a live lineage cell, the shared transfer check is blocked exactly
when the recipient lacks either a free capability slot or a free lineage
cell. -/
theorem transferBlocked_eval_with_lineage (σ : Loom.Hw.St)
    (D T : DomainId) (toE : Expr 2) (acs : Hw.CapSel)
    (hto : finOfBv (by decide : 2 ^ 2 = numDomains) (toE.eval σ) = T)
    (hlinV : acs.linV.eval σ = 1#1)
    (hcellV : (Hw.cellVAt D acs.lin).eval σ = 1#1) :
    (Hw.transferBlocked D toE acs).eval σ = 1#1 ↔
      (¬((Hw.abs σ).freeSlot T).isSome ∨
       ¬((Hw.abs σ).freeCell T).isSome) := by
  have hslot := freeSlotV_eval σ T
  have hcell := freeCellV_eval σ T
  simp only [Hw.transferBlocked, Expr.eval]
  rw [muxFin_eval (by decide : 2 ^ 2 = numDomains), hto, hlinV, hcellV,
    muxFin_eval (by decide : 2 ^ 2 = numDomains), hto]
  by_cases hsv : (Hw.freeSlotV T).eval σ = 1#1
  · have hs := hslot.mp hsv
    by_cases hcv : (Hw.freeCellV T).eval σ = 1#1
    · have hc := hcell.mp hcv
      simp [hsv, hcv, hs, hc]
    · have hcz : (Hw.freeCellV T).eval σ = 0#1 := bv1_ne_one.mp hcv
      have hc : ¬((Hw.abs σ).freeCell T).isSome := by
        intro his
        exact hcv (hcell.mpr his)
      simp [hsv, hcz, hs, hc]
  · have hsz : (Hw.freeSlotV T).eval σ = 0#1 := bv1_ne_one.mp hsv
    have hs : ¬((Hw.abs σ).freeSlot T).isSome := by
      intro his
      exact hsv (hslot.mpr his)
    by_cases hcv : (Hw.freeCellV T).eval σ = 1#1
    · have hc := hcell.mp hcv
      simp [hsz, hcv, hs, hc]
    · have hcz : (Hw.freeCellV T).eval σ = 0#1 := bv1_ne_one.mp hcv
      have hc : ¬((Hw.abs σ).freeCell T).isSome := by
        intro his
        exact hcv (hcell.mpr his)
      simp [hsz, hcz, hs, hc]

/-- A root transfer with an available target slot passes placement. -/
theorem transferBlocked_pass_no_lineage (σ : Loom.Hw.St)
    (D T : DomainId) (toE : Expr 2) (acs : Hw.CapSel)
    (hto : finOfBv (by decide : 2 ^ 2 = numDomains) (toE.eval σ) = T)
    (hlinV : acs.linV.eval σ = 0#1)
    (hslot : ((Hw.abs σ).freeSlot T).isSome) :
    (Hw.transferBlocked D toE acs).eval σ ≠ 1#1 := by
  intro h
  exact (transferBlocked_eval_no_lineage σ D T toE acs hto hlinV).mp h hslot

/-- A derived transfer with available target slot and lineage cell passes
placement. -/
theorem transferBlocked_pass_with_lineage (σ : Loom.Hw.St)
    (D T : DomainId) (toE : Expr 2) (acs : Hw.CapSel)
    (hto : finOfBv (by decide : 2 ^ 2 = numDomains) (toE.eval σ) = T)
    (hlinV : acs.linV.eval σ = 1#1)
    (hcellV : (Hw.cellVAt D acs.lin).eval σ = 1#1)
    (hslot : ((Hw.abs σ).freeSlot T).isSome)
    (hcell : ((Hw.abs σ).freeCell T).isSome) :
    (Hw.transferBlocked D toE acs).eval σ ≠ 1#1 := by
  intro h
  rcases (transferBlocked_eval_with_lineage σ D T toE acs hto hlinV
    hcellV).mp h with hs | hc
  · exact hs hslot
  · exact hc hcell

end Machines.Lnp64u.Theorems.RMC
