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

end Machines.Lnp64u.Theorems.RMC
