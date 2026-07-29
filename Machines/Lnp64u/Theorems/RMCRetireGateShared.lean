-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateTransfer
import Machines.Lnp64u.Theorems.RMCRetireDrop
import Machines.Lnp64u.Theorems.RMCRefill
import Machines.Lnp64u.Theorems.RMCFrames

/-!
# R-MC retirement: the shared retirement-base transfer glue

The post-refill, cleared-inflight retirement accumulator and the
structural-transfer lemmas over it are used by both the successful
`gate_call` arms and the successful `gate_return` arms. They were born in
`RMCRetireGateCallSuccess`, which serialized the whole gate-return proof
chain behind the 880-second call chain for lemmas that mention nothing
call-specific. This module holds them below both chains.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

private theorem refillClear_pres (m : Manifest) (σ : Loom.Hw.St)
    (rn : String) (w : Nat) (hne : rn ≠ "if_v")
    (hnot : (rn, w) ∉
      ([ ("d0_budget", 32), ("d0_rctr", 32),
         ("d1_budget", 32), ("d1_rctr", 32),
         ("d2_budget", 32), ("d2_rctr", 32),
         ("d3_budget", 32), ("d3_rctr", 32) ] :
        List (String × Nat))) :
    ((Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)).regs rn w = σ.regs rn w := by
  simp only [Act.run, RegEnv.set]
  rw [if_neg hne]
  exact refill_pres m σ hnot

/-- Clearing the retiring in-flight valid bit after refill has exactly the
expected abstract effect.  This is the accumulator used by every successful
retirement payload. -/
theorem abs_refill_clearInflight (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP) :
    Hw.abs ((Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)) =
      { refillPhase m (Hw.abs σ) with inflight := none } := by
  have hrefill := abs_refill m hwf hfit σ hsync
  apply machineState_ext'
  · change (((Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)).regs "cycle" 32) = _
    simp [Act.run, RegEnv.set]
    exact congrArg MachineState.cycle hrefill
  · change (fun a : Addr => ((Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)).mems "mem" a.toNat 32) = _
    simpa [Act.run] using congrArg MachineState.mem hrefill
  · change (fun d => Hw.absDom ((Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)) d) = _
    have hdom : ∀ d, Hw.absDom ((Act.write 1 "if_v" (.lit 0)).run σ
        ((Hw.refillAct m).run σ σ)) d =
        Hw.absDom ((Hw.refillAct m).run σ σ) d := by
      intro d
      apply absDom_congr
      intro q hq
      simp only [Act.run, RegEnv.set]
      have hne : q.1 ≠ "if_v" := by
        exact (show ∀ q ∈ domReadNames d, q.1 ≠ "if_v" from by
          fin_cases d <;> decide +kernel) q hq
      simp [hne]
    funext d
    rw [hdom]
    exact congrFun (congrArg MachineState.doms hrefill) d
  · change (fun g => Hw.absGate ((Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)) g) = _
    have hgate : ∀ g, Hw.absGate ((Act.write 1 "if_v" (.lit 0)).run σ
        ((Hw.refillAct m).run σ σ)) g =
        Hw.absGate ((Hw.refillAct m).run σ σ) g := by
      intro g
      apply absGate_congr
      intro q hq
      simp only [Act.run, RegEnv.set]
      have hne : q.1 ≠ "if_v" := by
        exact (show ∀ q ∈ gateReadNames g, q.1 ≠ "if_v" from by
          fin_cases g <;> decide +kernel) q hq
      simp [hne]
    funext g
    rw [hgate]
    exact congrFun (congrArg MachineState.gates hrefill) g
  · change Hw.absMover ((Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)) = _
    have hm : Hw.absMover ((Act.write 1 "if_v" (.lit 0)).run σ
        ((Hw.refillAct m).run σ σ)) =
        Hw.absMover ((Hw.refillAct m).run σ σ) := by
      unfold Hw.absMover
      simp [Act.run, RegEnv.set]
    rw [hm]
    exact congrArg MachineState.mover hrefill
  · rfl

/-- The post-refill, cleared-inflight retirement base has exactly the same
capability liveness as the sampled abstract state. -/
theorem retireBase_liveRef (m : Manifest) (σ : Loom.Hw.St) (r : CapRef) :
    ({ refillPhase m (Hw.abs σ) with inflight := none } : MachineState).liveRef r =
      (Hw.abs σ).liveRef r := by
  unfold MachineState.liveRef DomainState.liveCap
  rw [refillPhase_caps, refillPhase_slotGen]

/-- Refill and in-flight clearing frame region tables. -/
theorem retireBase_regions (m : Manifest) (σ : Loom.Hw.St)
    (d : DomainId) :
    (({ refillPhase m (Hw.abs σ) with inflight := none } : MachineState).doms
      d).regions = ((Hw.abs σ).doms d).regions := by
  exact refillPhase_regions m (Hw.abs σ) d

/-- Refill and in-flight clearing frame the active Mover job. -/
theorem retireBase_mover (m : Manifest) (σ : Loom.Hw.St) :
    ({ refillPhase m (Hw.abs σ) with inflight := none } : MachineState).mover =
      Hw.absMover σ := by
  exact refillPhase_mover m (Hw.abs σ)

/-- Refill and in-flight clearing frame physical memory. -/
theorem retireBase_mem (m : Manifest) (σ : Loom.Hw.St) (b : Addr) :
    ({ refillPhase m (Hw.abs σ) with inflight := none } : MachineState).mem b =
      σ.mems "mem" b.toNat 32 := by
  rfl

/-- Exact liveness of an old live reference after a structural transfer from
the retirement base.  The region sweep does not alter capability liveness. -/
theorem transferStructural_retire_liveRef (m : Manifest)
    (σ : Loom.Hw.St) (T : DomainId) (NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef)) (oldRef newRef : CapRef)
    (D : DomainId) (S : Slot) (r : CapRef)
    (hfree : ((Hw.abs σ).doms T).caps NS = none)
    (hlive : (Hw.abs σ).liveRef r = true) :
    (transferStructural
      { refillPhase m (Hw.abs σ) with inflight := none }
      T NS kind moved oldRef newRef D S).liveRef r =
        if r.dom = D ∧ r.slot = S then false else true := by
  unfold transferStructural
  rw [sweepRegions_liveRef]
  apply transferStructural_liveRef_of_live
  · simpa [refillPhase_caps] using hfree
  · rw [retireBase_liveRef]
    exact hlive

/-- Capability kind of an old live non-source reference is preserved by a
structural transfer from the retirement base. -/
theorem transferStructural_retire_liveKind (m : Manifest)
    (σ : Loom.Hw.St) (T : DomainId) (NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef)) (oldRef newRef : CapRef)
    (D : DomainId) (S : Slot) (r : CapRef)
    (hfree : ((Hw.abs σ).doms T).caps NS = none)
    (hlive : (Hw.abs σ).liveRef r = true)
    (hout : ¬(r.dom = D ∧ r.slot = S)) :
    Option.map CapEntry.kind
        (((transferStructural
          { refillPhase m (Hw.abs σ) with inflight := none }
          T NS kind moved oldRef newRef D S).doms r.dom).liveCap r.slot r.gen) =
      Option.map CapEntry.kind
        (((Hw.abs σ).doms r.dom).liveCap r.slot r.gen) := by
  unfold transferStructural
  have h := transferStructural_liveKind_of_live
    ({ refillPhase m (Hw.abs σ) with inflight := none } : MachineState)
    T NS kind moved oldRef newRef D S r
    (by simpa [refillPhase_caps] using hfree)
    (by rw [retireBase_liveRef]; exact hlive) hout
  calc
    _ = Option.map CapEntry.kind
        (((refillPhase m (Hw.abs σ)).doms r.dom).liveCap r.slot r.gen) := h
    _ = Option.map CapEntry.kind
        (((Hw.abs σ).doms r.dom).liveCap r.slot r.gen) := by
      unfold DomainState.liveCap
      rw [refillPhase_caps, refillPhase_slotGen]

/-- Mover field after sweeping a retirement-base structural transfer. -/
theorem transferStructural_retire_sweepMover_mover (m : Manifest)
    (σ : Loom.Hw.St) (T : DomainId) (NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef)) (oldRef newRef : CapRef)
    (D : DomainId) (S : Slot)
    (hfree : ((Hw.abs σ).doms T).caps NS = none)
    (hwf : Wf (Hw.abs σ)) :
    (transferStructural
      { refillPhase m (Hw.abs σ) with inflight := none }
      T NS kind moved oldRef newRef D S).sweepMover.mover =
        match Hw.absMover σ with
        | none => none
        | some job =>
            if (job.src.dom = D ∧ job.src.slot = S) ∨
                (job.dst.dom = D ∧ job.dst.slot = S)
            then none else some job := by
  let τr := transferStructural
    ({ refillPhase m (Hw.abs σ) with inflight := none } : MachineState)
    T NS kind moved oldRef newRef D S
  apply sweepMover_transfer_mover (Hw.abs σ) τr D S
  · simp [τr, transferStructural, installTransferred,
      MachineState.reparent, MachineState.clearSlot,
      MachineState.sweepRegions, MachineState.setDom, retireBase_mover]
  · intro job hjob
    have hsrc := (moverEndpoints_live hwf job hjob).1
    simpa [τr, hsrc] using
      transferStructural_retire_liveRef m σ T NS kind moved oldRef
        newRef D S job.src hfree hsrc
  · intro job hjob
    have hdst := (moverEndpoints_live hwf job hjob).2
    simpa [τr, hdst] using
      transferStructural_retire_liveRef m σ T NS kind moved oldRef
        newRef D S job.dst hfree hdst
  · exact moverEndpoints_live hwf

/-- Memory face of `transferStructural_retire_sweepMover_mover`. -/
theorem transferStructural_retire_sweepMover_mem (m : Manifest)
    (σ : Loom.Hw.St) (T : DomainId) (NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef)) (oldRef newRef : CapRef)
    (D : DomainId) (S : Slot)
    (hfree : ((Hw.abs σ).doms T).caps NS = none)
    (hwf : Wf (Hw.abs σ)) (b : Addr) :
    (transferStructural
      { refillPhase m (Hw.abs σ) with inflight := none }
      T NS kind moved oldRef newRef D S).sweepMover.mem b =
        match Hw.absMover σ with
        | none => σ.mems "mem" b.toNat 32
        | some job =>
            if (job.src.dom = D ∧ job.src.slot = S) ∨
                (job.dst.dom = D ∧ job.dst.slot = S) then
              if (transferStructural
                    { refillPhase m (Hw.abs σ) with inflight := none }
                    T NS kind moved oldRef newRef D S).domCovers
                    job.owner job.statusAddr
                    { r := false, w := true, x := false } then
                if b = job.statusAddr then Errno.staleHandle.toWord
                else σ.mems "mem" b.toNat 32
              else σ.mems "mem" b.toNat 32
            else σ.mems "mem" b.toNat 32 := by
  let τr := transferStructural
    ({ refillPhase m (Hw.abs σ) with inflight := none } : MachineState)
    T NS kind moved oldRef newRef D S
  rw [sweepMover_transfer_mem (Hw.abs σ) τr D S]
  · simp only
    have hmem : ∀ a, τr.mem a = σ.mems "mem" a.toNat 32 := by
      intro a
      simpa [τr, transferStructural, installTransferred,
        MachineState.reparent, MachineState.clearSlot,
        MachineState.sweepRegions, MachineState.setDom] using
          retireBase_mem m σ a
    simp only [hmem]
    have habsm : (Hw.abs σ).mover = Hw.absMover σ := rfl
    cases hm : Hw.absMover σ <;> rw [habsm, hm] <;> rfl
  · simp [τr, transferStructural, installTransferred,
      MachineState.reparent, MachineState.clearSlot,
      MachineState.sweepRegions, MachineState.setDom, retireBase_mover]
  · intro job hjob
    have hsrc := (moverEndpoints_live hwf job hjob).1
    simpa [τr, hsrc] using
      transferStructural_retire_liveRef m σ T NS kind moved oldRef
        newRef D S job.src hfree hsrc
  · intro job hjob
    have hdst := (moverEndpoints_live hwf job hjob).2
    simpa [τr, hdst] using
      transferStructural_retire_liveRef m σ T NS kind moved oldRef
        newRef D S job.dst hfree hdst
  · exact moverEndpoints_live hwf

/-- Root transfer specialized to the post-refill, cleared-inflight
retirement accumulator. -/
theorem abs_transferA_none_retireAcc (m : Manifest) (hwfm : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
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
    let acc := (Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)
    Hw.abs ((Hw.transferA D toE acs).run σ acc) =
      ((((installTransferred
        { refillPhase m (Hw.abs σ) with inflight := none }
        T NS e.kind none).reparent
          ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩
          ⟨T, NS, ((Hw.abs σ).doms T).slotGen NS⟩).clearSlot D S).sweepRegions) := by
  dsimp only
  let acc := (Act.write 1 "if_v" (.lit 0)).run σ
    ((Hw.refillAct m).run σ σ)
  let base : MachineState :=
    { refillPhase m (Hw.abs σ) with inflight := none }
  have habs : Hw.abs acc = base :=
    abs_refill_clearInflight m hwfm hfit σ hsync
  have hsourceAcc : ((Hw.abs acc).doms D).caps S = some e := by
    rw [habs]
    simpa [base] using hsource
  have hslotAcc : (Hw.abs acc).freeSlot T = some NS := by
    rw [habs]
    unfold MachineState.freeSlot
    simp only [base, refillPhase_caps, refillPhase_slotGen]
    exact hslot
  have holdAcc : Hw.decRef
      ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩ := by
    rw [habs]
    simpa [base] using hold
  have hV : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1 := by
    intro c l
    exact refillClear_pres m σ _ _
      (by fin_cases c <;> fin_cases l <;> decide +kernel)
      (by fin_cases c <;> fin_cases l <;> decide +kernel)
  have hP : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14 := by
    intro c l
    exact refillClear_pres m σ _ _
      (by fin_cases c <;> fin_cases l <;> decide +kernel)
      (by fin_cases c <;> fin_cases l <;> decide +kernel)
  have hregionV : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgnV c r) 1 = σ.regs (Hw.drgnV c r) 1 := by
    intro c r
    exact refillClear_pres m σ _ _
      (by fin_cases c <;> fin_cases r <;> decide +kernel)
      (by fin_cases c <;> fin_cases r <;> decide +kernel)
  have hregion : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgn c r) 42 = σ.regs (Hw.drgn c r) 42 := by
    intro c r
    exact refillClear_pres m σ _ _
      (by fin_cases c <;> fin_cases r <;> decide +kernel)
      (by fin_cases c <;> fin_cases r <;> decide +kernel)
  have hgenAll : ∀ c : DomainId, ∀ s : Slot,
      acc.regs (Hw.dgen c s) 8 = σ.regs (Hw.dgen c s) 8 := by
    intro c s
    exact refillClear_pres m σ _ _
      (by fin_cases c <;> fin_cases s <;> decide +kernel)
      (by fin_cases c <;> fin_cases s <;> decide +kernel)
  have hwfAcc : Wf (Hw.abs acc) := by
    rw [habs]
    have hρ := refillPhase_preserves_wf m (Hw.abs σ) hwf
    refine { hρ with inflight_running := ?_ }
    intro fl hfl
    simp [base] at hfl
  have h := abs_transferA_none_acc σ acc D T toE acs S NS e hto
    hsourceSlot hsourceAcc hslotAcc hslot hlin hlinV hkind holdAcc hV hP
    hregionV hregion hgenAll hwfAcc
  rw [habs] at h
  simpa [base] using h

/-- Derived transfer specialized to the post-refill, cleared-inflight
retirement accumulator. -/
theorem abs_transferA_some_retireAcc (m : Manifest) (hwfm : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
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
    let acc := (Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)
    Hw.abs ((Hw.transferA D toE acs).run σ acc) =
      ((((installTransferred
        { refillPhase m (Hw.abs σ) with inflight := none }
        T NS e.kind (some (NL, cell.parent))).reparent
          ⟨D, S, ((Hw.abs σ).doms D).slotGen S⟩
          ⟨T, NS, ((Hw.abs σ).doms T).slotGen NS⟩).clearSlot D S).sweepRegions) := by
  dsimp only
  let acc := (Act.write 1 "if_v" (.lit 0)).run σ
    ((Hw.refillAct m).run σ σ)
  let base : MachineState :=
    { refillPhase m (Hw.abs σ) with inflight := none }
  have habs : Hw.abs acc = base :=
    abs_refill_clearInflight m hwfm hfit σ hsync
  have hsourceAcc : ((Hw.abs acc).doms D).caps S = some e := by
    rw [habs]
    simpa [base] using hsource
  have hslotAcc : (Hw.abs acc).freeSlot T = some NS := by
    rw [habs]
    unfold MachineState.freeSlot
    simp only [base, refillPhase_caps, refillPhase_slotGen]
    exact hslot
  have hcellAcc : ((Hw.abs acc).doms D).lineage L = some cell := by
    rw [habs]
    simpa [base] using hcell
  have hfreeCellAcc : (Hw.abs acc).freeCell T = some NL := by
    rw [habs]
    unfold MachineState.freeCell
    simp only [base, refillPhase_lineage]
    exact hfreeCell
  have holdAcc : Hw.decRef
      ((Hw.encRefE (Hw.dLit D) acs.slot acs.gen).eval σ) =
      ⟨D, S, ((Hw.abs acc).doms D).slotGen S⟩ := by
    rw [habs]
    simpa [base] using hold
  have hV : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1 := by
    intro c l
    exact refillClear_pres m σ _ _
      (by fin_cases c <;> fin_cases l <;> decide +kernel)
      (by fin_cases c <;> fin_cases l <;> decide +kernel)
  have hP : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14 := by
    intro c l
    exact refillClear_pres m σ _ _
      (by fin_cases c <;> fin_cases l <;> decide +kernel)
      (by fin_cases c <;> fin_cases l <;> decide +kernel)
  have hregionV : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgnV c r) 1 = σ.regs (Hw.drgnV c r) 1 := by
    intro c r
    exact refillClear_pres m σ _ _
      (by fin_cases c <;> fin_cases r <;> decide +kernel)
      (by fin_cases c <;> fin_cases r <;> decide +kernel)
  have hregion : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgn c r) 42 = σ.regs (Hw.drgn c r) 42 := by
    intro c r
    exact refillClear_pres m σ _ _
      (by fin_cases c <;> fin_cases r <;> decide +kernel)
      (by fin_cases c <;> fin_cases r <;> decide +kernel)
  have hgenAll : ∀ c : DomainId, ∀ s : Slot,
      acc.regs (Hw.dgen c s) 8 = σ.regs (Hw.dgen c s) 8 := by
    intro c s
    exact refillClear_pres m σ _ _
      (by fin_cases c <;> fin_cases s <;> decide +kernel)
      (by fin_cases c <;> fin_cases s <;> decide +kernel)
  have hwfAcc : Wf (Hw.abs acc) := by
    rw [habs]
    have hρ := refillPhase_preserves_wf m (Hw.abs σ) hwf
    refine { hρ with inflight_running := ?_ }
    intro fl hfl
    simp [base] at hfl
  have h := abs_transferA_some_acc σ acc D T toE acs S NS e L cell NL hto
    hsourceSlot hsourceAcc hslotAcc hslot hlin hcellAcc hcell hfreeCellAcc
    hfreeCell hlinV hlinIdx hkind holdAcc hV hP hregionV hregion hgenAll
    hwfAcc
  rw [habs] at h
  simpa [base] using h

end Machines.Lnp64u.Theorems.RMC
