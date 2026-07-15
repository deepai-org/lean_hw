-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateTransfer

/-!
# Exact gate transfer-by-handle error outcomes

Small monadic reductions shared by the final `gate_call` checks and the
corresponding `gate_return` transfer path.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom

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

end Machines.Lnp64u.Theorems.RMC
