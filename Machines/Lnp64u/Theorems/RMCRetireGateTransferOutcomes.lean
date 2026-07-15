-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateTransfer

/-!
# Exact gate transfer-by-handle error outcomes

Small monadic reductions shared by the final `gate_call` checks and the
corresponding `gate_return` transfer path.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

/-- A non-null handle whose decoded generation is not live returns stale
without changing the specification state. -/
theorem transferByHandle_stale (τ : MachineState) (D T : DomainId)
    (hw : Loom.Word32) (hnz : hw ≠ 0)
    (hnone : (τ.doms D).liveCap (Handle.decode hw).slot
      (Handle.decode hw).gen = none) :
    Machines.Lnp64u.Isa.transferByHandle D T hw τ =
      .err .staleHandle τ := by
  unfold Machines.Lnp64u.Isa.transferByHandle
  rw [if_neg hnz]
  unfold Machines.Lnp64u.Isa.capLive
  simp [SpecM.get, specM_bind, hnone, SpecM.raise]

/-- A non-null live handle with a mismatched class bit returns `badCap`. -/
theorem transferByHandle_badClass (τ : MachineState) (D T : DomainId)
    (hw : Loom.Word32) (S : Slot) (G : Gen) (e : CapEntry)
    (hnz : hw ≠ 0)
    (hdecode : Handle.decode hw = ⟨S, G, (Handle.decode hw).cls⟩)
    (hsome : (τ.doms D).liveCap S G = some e)
    (hcls : (Handle.decode hw).cls ≠ e.kind.cls) :
    Machines.Lnp64u.Isa.transferByHandle D T hw τ = .err .badCap τ := by
  unfold Machines.Lnp64u.Isa.transferByHandle
  rw [if_neg hnz]
  unfold Machines.Lnp64u.Isa.capLive
  simp only [specM_bind, SpecM.get]
  rw [hdecode, hsome]
  simp [SpecM.require, hcls, SpecM.raise]

/-- Once lookup succeeds, failure to allocate the structural transfer target
returns `slotOccupied` without changing the state. -/
theorem transferByHandle_slotOccupied (τ : MachineState) (D T : DomainId)
    (hw : Loom.Word32) (S : Slot) (G : Gen) (e : CapEntry)
    (hnz : hw ≠ 0)
    (hlive : Machines.Lnp64u.Isa.capLive D hw τ = .ok (S, G, e) τ)
    (htransfer : τ.transferCap D S T = none) :
    Machines.Lnp64u.Isa.transferByHandle D T hw τ =
      .err .slotOccupied τ := by
  unfold Machines.Lnp64u.Isa.transferByHandle
  rw [if_neg hnz]
  rw [specM_bind, hlive]
  simp [SpecM.get, specM_bind, htransfer, SpecM.raise]

/-- The shared hardware placement predicate is a sufficient and exact
reason for the structural specification transfer to return `none`, provided
the proof-side state agrees on the selected source and free-resource views. -/
theorem transferCap_none_of_blocked (σ : Loom.Hw.St) (τ : MachineState)
    (D T : DomainId) (toE : Expr 2) (hwE : Expr 32)
    (S : Slot) (e : CapEntry)
    (hto : finOfBv (by decide : 2 ^ 2 = numDomains) (toE.eval σ) = T)
    (hslotSel : (Hw.capSel D hwE).slot.eval σ = BitVec.ofNat 4 S.val)
    (hcap : ((Hw.abs σ).doms D).caps S = some e)
    (hsource : (τ.doms D).caps S = some e)
    (hlineage : ∀ L : LineageId,
      (τ.doms D).lineage L = ((Hw.abs σ).doms D).lineage L)
    (hfreeSlot : τ.freeSlot T = (Hw.abs σ).freeSlot T)
    (hfreeCell : τ.freeCell T = (Hw.abs σ).freeCell T)
    (hwf : Wf (Hw.abs σ))
    (hblocked : (Hw.transferBlocked D toE (Hw.capSel D hwE)).eval σ = 1#1) :
    τ.transferCap D S T = none := by
  cases hlin : e.lineage with
  | none =>
      have hlinV : (Hw.capSel D hwE).linV.eval σ = 0#1 :=
        capSel_lineage_none_eval σ D hwE S e hslotSel hcap hlin
      have hnslot :=
        (transferBlocked_eval_no_lineage σ D T toE (Hw.capSel D hwE)
          hto hlinV).mp
          hblocked
      have hnoneAbs : (Hw.abs σ).freeSlot T = none := by
        cases hs : (Hw.abs σ).freeSlot T with
        | none => rfl
        | some s => simp [hs] at hnslot
      have hnone : τ.freeSlot T = none := hfreeSlot.trans hnoneAbs
      unfold MachineState.transferCap
      simp [hsource, hnone]
  | some L =>
      have hsel := capSel_lineage_some_eval σ D hwE S e L hslotSel hcap hlin
      have hused := (hwf.doms D).cell_backed S e L hcap hlin
      obtain ⟨cell, hcellAbs⟩ : ∃ cell,
          ((Hw.abs σ).doms D).lineage L = some cell := by
        cases hc : ((Hw.abs σ).doms D).lineage L with
        | none => simp [hc] at hused
        | some cell => exact ⟨cell, rfl⟩
      have hcellV : (Hw.cellVAt D (Hw.capSel D hwE).lin).eval σ = 1#1 := by
        rw [cellVAt_eval σ D (Hw.capSel D hwE).lin L hsel.2]
        change σ.regs (Hw.dcellV D L) 1 = 1#1
        change (if σ.regs (Hw.dcellV D L) 1 = 1#1 then
            some ⟨Hw.decRef (σ.regs (Hw.dcellPar D L) 14)⟩
          else none) = some cell at hcellAbs
        by_cases hv : σ.regs (Hw.dcellV D L) 1 = 1#1
        · exact hv
        · rw [if_neg hv] at hcellAbs
          contradiction
      rcases (transferBlocked_eval_with_lineage σ D T toE
        (Hw.capSel D hwE) hto hsel.1 hcellV).mp hblocked with
        hnslot | hncell
      · have hnoneAbs : (Hw.abs σ).freeSlot T = none := by
          cases hs : (Hw.abs σ).freeSlot T with
          | none => rfl
          | some s => simp [hs] at hnslot
        have hnone : τ.freeSlot T = none := hfreeSlot.trans hnoneAbs
        unfold MachineState.transferCap
        simp [hsource, hnone]
      · have hnoneCellAbs : (Hw.abs σ).freeCell T = none := by
          cases hc : (Hw.abs σ).freeCell T with
          | none => rfl
          | some l => simp [hc] at hncell
        have hnoneCell : τ.freeCell T = none :=
          hfreeCell.trans hnoneCellAbs
        have hcell : (τ.doms D).lineage L = some cell := by
          rw [hlineage]
          exact hcellAbs
        unfold MachineState.transferCap
        simp only [Option.bind_eq_bind]
        rw [hsource]
        simp only [Option.bind_some]
        cases hs : τ.freeSlot T with
        | none => simp
        | some NS =>
            rw [hlin]
            simp [hcell, hnoneCell]

end Machines.Lnp64u.Theorems.RMC
