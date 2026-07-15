-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateCallArm
import Machines.Lnp64u.Theorems.RMCRetireGateSquare

/-!
# R-MC retirement: successful gate_call arms

Successful `gate_call` retirement, split at the optional argument transfer.
The null branch establishes the complete activation/callee/caller cycle with
an empty structural kill footprint; the non-null branch reuses the shared
`transferA` abstraction.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

private theorem ifv_notin_callSuccess (d : DomainId) :
    ("if_v", 1) ∉ (callSuccessA d).regWrites := by
  fin_cases d <;> decide +kernel

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

/-- A null argument selects the identity arm of the optional hardware
transfer, independently of the accumulator supplied by retirement. -/
theorem callTransferA_run_zero (σ acc : Loom.Hw.St) (d : DomainId)
    (hz : (Hw.argW d).eval σ = 0#32) :
    (callTransferA d).run σ acc = acc := by
  have hnz : (Hw.argNZ d).eval σ ≠ 1#1 := by
    intro h
    exact (argNZ_eval_iff σ d).mp h hz
  simp [callTransferA, Act.run, bv1_ne_one.mp hnz]

/-- A non-null argument selects the shared structural transfer action. -/
theorem callTransferA_run_nonzero (σ acc : Loom.Hw.St) (d : DomainId)
    (hnz : (Hw.argW d).eval σ ≠ 0#32) :
    (callTransferA d).run σ acc =
      (Hw.transferA d (Hw.callCal d) (Hw.argSel d)).run σ acc := by
  have hnzE : (Hw.argNZ d).eval σ = 1#1 :=
    (argNZ_eval_iff σ d).mpr hnz
  simp [callTransferA, Act.run, hnzE]

/-- A successful call with a null argument cannot invalidate a Mover
endpoint, so its auxiliary status-memory port is disabled. -/
theorem callCirc_memEn_zero_arg (σ : Loom.Hw.St) (d : DomainId)
    (hz : (Hw.argW d).eval σ = 0#32) :
    (Hw.callCirc d).memEn.eval σ = 0#1 := by
  have hnz : (Hw.argNZ d).eval σ = 0#1 := by
    apply bv1_ne_one.mp
    intro h
    exact (argNZ_eval_iff σ d).mp h hz
  have hk : (Hw.movKilledE (Hw.callKilled d)).eval σ = 0#1 := by
    unfold Hw.movKilledE Hw.callKilled Hw.andAll
    simp only [Expr.eval]
    rw [hnz]
    exact (by decide : ∀ a b c : BitVec 1,
      a &&& ((0#1 &&& b) ||| (0#1 &&& c)) = 0#1) _ _ _
  unfold Hw.callCirc Hw.sweepMem Hw.andAll
  change (Hw.callOkE d).eval σ &&&
    ((Hw.movKilledE (Hw.callKilled d)).eval σ &&&
      (Hw.statusAuthE (Hw.callKilled d)).eval σ) = 0#1
  rw [hk]
  exact (by decide : ∀ a b : BitVec 1, a &&& (0#1 &&& b) = 0#1) _ _

/-- Consequently, the core phase of a null-argument call preserves memory,
including when all call checks pass. -/
theorem coreAct_mem_gateCall_zero_arg (m : Manifest) (σ : Loom.Hw.St)
    (E : DomainId)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hz : (Hw.argW E).eval σ = 0#32) (b : Addr) :
    ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
      b.toNat 32 = σ.mems "mem" b.toNat 32 := by
  have hport := retireMem_gateCall_sel σ E hifsel hifexcl hopc
  have hmen : (Hw.callCirc E).memEn.eval σ = 0#1 :=
    callCirc_memEn_zero_arg σ E hz
  rw [coreAct_run_retire_eq m σ _ hifv hcl,
    retireAct_run_mems σ _ b.toNat 32]
  show (if (((List.finRange numDomains).foldr
      (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
        let (en_d, ad_d, da_d) := Hw.retireMemFor d
        let g := Expr.and (Hw.ifDomIs d) en_d
        (.or g acc'.1, .mux g ad_d acc'.2.1,
          .mux g da_d acc'.2.2))
      ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
        (.lit 0 : Expr 32))).1).eval σ = 1#1 then _
    else ((Hw.refillAct m).run σ σ)).mems "mem" b.toNat 32 = _
  rw [if_neg (by rw [hport.1, hmen]; decide)]
  exact refill_pres_mem m σ "mem" b.toNat 32

/-- Although the call itself succeeds, a null argument gives it an empty
structural kill footprint, so the ordinary inert Mover assembly applies. -/
theorem Inert.of_successful_call_zero (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1)
    (hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1)
    (hcall : (Hw.isMn "gate_call").eval σ = 1#1)
    (hreturn : (Hw.isMn "gate_return").eval σ ≠ 1#1)
    (hok : ∀ d : DomainId, d = E → (Hw.callOkE d).eval σ = 1#1)
    (hz : (Hw.argNZ E).eval σ = 0#1)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1) : Inert σ where
  killed := by
    intro dm sl
    rw [killedByCoreE_call_eval σ E hret hif hdrop hrev hcall hreturn
      hok dm sl]
    exact callKilled_zero_eval σ E hz dm sl
  newJob := hnew

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

/-- The specification enters the call body after advancing the caller PC,
whereas the hardware successful payload performs that advance itself.  Refill
does not change any value captured by the activation record, so the two pure
successful-call transformers coincide. -/
theorem callAbstractSuccess_refill_pc (m : Manifest) (σ : Loom.Hw.St)
    (d cal : DomainId) (g : GateId) (rd : RegId)
    (argHandle : Loom.Word32) (depth : Nat) (hne : d ≠ cal) :
    let base : MachineState :=
      { refillPhase m (Hw.abs σ) with inflight := none }
    let prefixed := base.setDom d (fun ds => { ds with pc := ds.pc + 1 })
    callAbstractSuccessAt prefixed prefixed d cal g rd argHandle depth
        (prefixed.doms d).pc =
      callAbstractSuccess (Hw.abs σ) base d cal g rd argHandle depth := by
  dsimp only
  unfold callAbstractSuccess callAbstractSuccessAt
  apply machineState_ext' <;> try rfl
  · funext x
    by_cases hxd : x = d
    · subst x
      simp [MachineState.setDom, Loom.Fun.update]
    · by_cases hxc : x = cal
      · subst x
        have hcald : cal ≠ d := hxd
        simp [MachineState.setDom, Loom.Fun.update, hcald,
          refillPhase_serving]
      · simp [MachineState.setDom, Loom.Fun.update, hxd, hxc]
  · funext h
    by_cases hh : h = g
    · subst h
      have hcald : cal ≠ d := Ne.symm hne
      simp [MachineState.setDom, Loom.Fun.update, hcald,
        refillPhase_gates,
        refillPhase_serving, refillPhase_dmaxdon]
    · simp [MachineState.setDom, hh, refillPhase_gates]

/-- The call control-state tail frames all capability structure and regions
already produced by the optional transfer. -/
theorem callAbstractSuccess_structural_frames (source base : MachineState)
    (d cal : DomainId) (g : GateId) (rd : RegId)
    (argHandle : Loom.Word32) (depth : Nat) :
    (∀ x, ((callAbstractSuccess source base d cal g rd argHandle depth).doms
        x).caps = (base.doms x).caps) ∧
    (∀ x, ((callAbstractSuccess source base d cal g rd argHandle depth).doms
        x).slotGen = (base.doms x).slotGen) ∧
    (∀ x, ((callAbstractSuccess source base d cal g rd argHandle depth).doms
        x).regions = (base.doms x).regions) ∧
    (callAbstractSuccess source base d cal g rd argHandle depth).mover =
      base.mover ∧
    (callAbstractSuccess source base d cal g rd argHandle depth).mem =
      base.mem := by
  constructor
  · intro x
    by_cases hxd : x = d <;> by_cases hxc : x = cal <;>
      simp_all [callAbstractSuccess, callAbstractSuccessAt]
  constructor
  · intro x
    by_cases hxd : x = d <;> by_cases hxc : x = cal <;>
      simp_all [callAbstractSuccess, callAbstractSuccessAt]
  constructor
  · intro x
    by_cases hxd : x = d <;> by_cases hxc : x = cal <;>
      simp_all [callAbstractSuccess, callAbstractSuccessAt]
  · exact ⟨rfl, rfl⟩

/-- Once the common gate-call checks have selected a ready callee, a null
argument reduces the specification body directly to the successful pure
transformer. -/
theorem gateCallExec_success_zero_of_ready (σ : Loom.Hw.St)
    (τ : MachineState) (d : DomainId) (c : Ctx)
    (hready : CallReady σ τ d c)
    (harg : (τ.doms c.d).reg c.op.rs2 = 0) :
    ∃ g : GateId, ∃ cal : DomainId,
      cal ≠ c.d ∧
      finOfBv (by decide : 2 ^ 2 = numGates)
          ((Hw.callGid d).eval σ) = g ∧
      finOfBv (by decide : 2 ^ 2 = numDomains)
          ((Hw.callCal d).eval σ) = cal ∧
      Machines.Lnp64u.Isa.Wip.gateCallExec c τ =
        .ok () (callAbstractSuccessAt τ τ c.d cal g c.op.rd 0
          (Machines.Lnp64u.Isa.Wip.gateDepth c τ) (τ.doms c.d).pc) := by
  obtain ⟨S, G, e, g, cal, hlive, hkind, hact, hcal, hne, hrun,
      hserv, hdepth, hgid, hcalSel⟩ := hready
  have htransfer : Machines.Lnp64u.Isa.transferByHandle c.d cal
      ((τ.doms c.d).reg c.op.rs2) τ = .ok 0 τ := by
    rw [harg]
    exact transferByHandle_eq_zero τ c.d cal
  refine ⟨g, cal, hne, hgid, hcalSel, ?_⟩
  exact gateCallExec_eq_selected c τ τ S G e g cal 0 hlive hkind hact
    hcal hne hrun hserv hdepth htransfer rfl rfl rfl rfl rfl

/-- Complete successful null-argument arm.  This is the first successful
leaf of the gate-call check tree and the full-cycle template for the
structural-transfer branches. -/
theorem square_retire_gateCall_success_zero (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrc : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2)
    (hz : R0Zero σ) (hkc : KindCanon σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hlive : (Hw.callSel
      (finOfBv (by decide) (σ.regs "if_dom" 2))).live.eval σ = 1#1)
    (hprimary : (Expr.not (Expr.and
      (Hw.callSel (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk
      (Expr.not (Hw.kIsMem
        (Hw.callSel (finOfBv (by decide)
          (σ.regs "if_dom" 2))).kindW)))).eval σ ≠ 1#1)
    (hidle : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
      (Hw.callGid (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hnotSelf : (Expr.eq
      (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Hw.dLit (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hrunning : (Hw.neqE
      (Hw.muxFin (fun d => .reg 2 (Hw.drun d))
        (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2))))
      (.lit 0)).eval σ ≠ 1#1)
    (hnotServing : (Hw.muxFin (fun d => .reg 1 (Hw.dsrvV d))
      (Hw.callCal (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hdepthPass : (Expr.ult (.lit (BitVec.ofNat 3 maxChainDepth))
      (Hw.callDepth (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hargZero : (Hw.argW
      (finOfBv (by decide) (σ.regs "if_dom" 2))).eval σ = 0#32) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  let base : MachineState :=
    { refillPhase m (Hw.abs σ) with inflight := none }
  let c : Ctx :=
    { d := E, pc := (base.doms E).pc, op := operandsOf W }
  let τ0 : MachineState :=
    base.setDom E (fun ds => { ds with pc := ds.pc + 1 })
  have hop : Machines.Lnp64u.sig.opcodeOf W = (22#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) =
      retire base E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hR2 : (Hw.readReg E Hw.rs2E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl
  have hreg1 : (τ0.doms E).reg (operandsOf W).rs1 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    specReg_bridge m σ E _
  have hreg2 : (τ0.doms E).reg (operandsOf W).rs2 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    specReg_bridge m σ E _
  have hword1 : (τ0.doms c.d).reg c.op.rs1 =
      (Hw.readReg E Hw.rs1E).eval σ := by
    simp only [c]
    rw [hreg1, hR1]
  have hword2 : (τ0.doms c.d).reg c.op.rs2 =
      (Hw.argW E).eval σ := by
    simp only [c, Hw.argW]
    rw [hreg2, hR2]
  have hbridge : ∀ (S : Slot) (G : Gen),
      (τ0.doms E).liveCap S G = ((Hw.abs σ).doms E).liveCap S G := by
    intro S G
    exact specLiveCap_bridge m σ E S G
  have hp := callPrimary_of_pass σ τ0 E c rfl hword1 hbridge hkc
    (by simpa [E] using hlive) (by simpa [E] using hprimary)
  have hgates : τ0.gates = (Hw.abs σ).gates := by
    change (refillPhase m (Hw.abs σ)).gates = (Hw.abs σ).gates
    exact refillPhase_gates m (Hw.abs σ)
  have hcallee := callCallee_of_pass σ τ0 E c rfl hgates hp
    (by simpa [E] using hidle) (by simpa [E] using hnotSelf)
  have hrunBridge : ∀ x : DomainId,
      (τ0.doms x).run = ((Hw.abs σ).doms x).run := by
    intro x
    by_cases hx : x = E
    · subst x
      simp [τ0, base, MachineState.setDom, Loom.Fun.update]
    · simp [τ0, base, MachineState.setDom, Loom.Fun.update, hx]
  have hservBridge : ∀ x : DomainId,
      (τ0.doms x).serving = ((Hw.abs σ).doms x).serving := by
    intro x
    by_cases hx : x = E
    · subst x
      simp [τ0, base, MachineState.setDom, Loom.Fun.update]
    · simp [τ0, base, MachineState.setDom, Loom.Fun.update, hx]
  have hwfAbs : Wf (Hw.abs σ) :=
    (Machines.Lnp64u.wfa_invariant m hwf (Hw.abs σ) hsr).1
  have hready := callReady_of_pass σ τ0 E c rfl hwfAbs hrc hrunBridge
    hservBridge hgates hcallee (by simpa [E] using hrunning)
      (by simpa [E] using hnotServing) (by simpa [E] using hdepthPass)
  obtain ⟨S, G, e, g, cal, hcapLive, hkind, hact, hcal, hne,
      hrun, hserv, hdepth, hgid, hcalSel⟩ := hready
  have hselPass :
      (Expr.not (Hw.callSel E).live).eval σ ≠ 1#1 ∧
      (Expr.not (Expr.and (Hw.callSel E).clsOk
        (Expr.not (Hw.kIsMem (Hw.callSel E).kindW)))).eval σ ≠ 1#1 := by
    constructor
    · show ¬(~~~((Hw.callSel E).live.eval σ) = 1#1)
      rw [show (Hw.callSel E).live.eval σ = 1#1 from by
        simpa [E] using hlive]
      decide
    · simpa [E] using hprimary
  have hstatePass := callStateChecks_pass σ c g cal hwfAbs (hrc cal)
    hgid hcalSel (by simpa [hgates] using hact) (by simpa [c] using hne)
    (by simpa [hrunBridge] using hrun)
    (by simpa [hservBridge] using hserv)
    (by
      have heq : Machines.Lnp64u.Isa.Wip.gateDepth c τ0 =
          Machines.Lnp64u.Isa.Wip.gateDepth c (Hw.abs σ) := by
        unfold Machines.Lnp64u.Isa.Wip.gateDepth
        rw [hservBridge c.d, hgates]
      simpa [heq] using hdepth)
  have hargPass := callArgumentChecks_zero σ E (by simpa [E] using hargZero)
  have hok : (Hw.callOkE E).eval σ = 1#1 :=
    callOkE_of_passes σ E hselPass hstatePass hargPass.1
      hargPass.2.1 hargPass.2.2
  have hargSpec : (τ0.doms c.d).reg c.op.rs2 = 0 := by
    rw [hword2]
    simpa [E] using hargZero
  have htransfer : Machines.Lnp64u.Isa.transferByHandle c.d cal
      ((τ0.doms c.d).reg c.op.rs2) τ0 = .ok 0 τ0 := by
    rw [hargSpec]
    exact transferByHandle_eq_zero τ0 c.d cal
  have hexec : Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 =
      .ok () (callAbstractSuccessAt τ0 τ0 c.d cal g c.op.rd 0
        (Machines.Lnp64u.Isa.Wip.gateDepth c τ0) (τ0.doms c.d).pc) :=
    gateCallExec_eq_selected c τ0 τ0 S G e g cal 0 hcapLive hkind hact
      hcal hne hrun hserv hdepth htransfer rfl rfl rfl rfl rfl
  have hdepthEq : ((Hw.callDepth E).eval σ).toNat =
      Machines.Lnp64u.Isa.Wip.gateDepth c τ0 := by
    rw [show ((Hw.callDepth E).eval σ).toNat =
      Machines.Lnp64u.Isa.Wip.gateDepth c (Hw.abs σ) from by
        simpa [c] using callDepth_eval σ c hwfAbs]
    unfold Machines.Lnp64u.Isa.Wip.gateDepth
    rw [hservBridge c.d, hgates]
  let τ2 := callAbstractSuccess (Hw.abs σ) base E cal g
    (operandsOf W).rd 0 ((Hw.callDepth E).eval σ).toNat
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2 := by
    rw [hcore0, retire_gateCall_exec _ E W hdec]
    change (match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
      | .ok _ τ' => τ'
      | .err er τ' => τ'.setDom E
          (fun ds => ds.setReg (operandsOf W).rd er.toWord)
      | .fault f => haltWith base E f) = τ2
    rw [hexec]
    rw [← hdepthEq]
    simpa [c, τ0, base, τ2] using
      (callAbstractSuccess_refill_pc m σ E cal g (operandsOf W).rd 0
        ((Hw.callDepth E).eval σ).toNat (by simpa [c] using hne.symm))
  let acc0 := (Act.write 1 "if_v" (.lit 0)).run σ
    ((Hw.refillAct m).run σ σ)
  have habsBase : Hw.abs acc0 = base := by
    exact abs_refill_clearInflight m hwf hfit σ hsync
  have habsCall : Hw.abs ((callSuccessA E).run σ acc0) = τ2 := by
    rw [abs_callSuccessA σ acc0 E cal g (by simpa [c] using hne.symm)
      hcalSel hgid]
    rw [callTransferA_run_zero σ acc0 E (by simpa [E] using hargZero),
      habsBase, callArgHandle_eval_zero σ E (by simpa [E] using hargZero)]
    rfl
  have hret := retiringE_one σ hifv hcl
  have hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1 := by
    intro d
    by_cases hd : d = E
    · subst d; simpa using hifsel
    · rw [if_neg hd, bv1_ne_one.mp (hifexcl d hd)]
  have hmn : (Hw.isMn "gate_call").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "gate_call" = 22#6).symm
  have hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "cap_drop" 22#6 hopc (by decide +kernel)
  have hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "cap_revoke" 22#6 hopc (by decide +kernel)
  have hreturn : (Hw.isMn "gate_return").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "gate_return" 22#6 hopc (by decide +kernel)
  have hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1 := by
    intro d
    apply andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
    exact isMn_ne_of_opc σ "move" 22#6 hopc (by decide +kernel)
  have hin : Inert σ := Inert.of_successful_call_zero σ E hret hif hdrop
    hrev hmn hreturn (fun d hd => by simpa [hd] using hok)
      (by
        apply bv1_ne_one.mp
        intro hnz
        exact (argNZ_eval_iff σ E).mp hnz (by simpa [E] using hargZero))
      hnew
  have hmapz : ∀ (x : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs x, Hw.isMn "map", Hw.mapOkE x,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun x r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "map" 22#6 hopc (by decide +kernel))
  have hunmapz : ∀ (x : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs x, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun x r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "unmap" 22#6 hopc (by decide +kernel))
  have hswz : ∀ (d : DomainId) (sc : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
        Hw.domCoversE d
          (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          ⟨false, true, false⟩,
        .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          sc]).eval σ = 0#1 := fun d sc =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "sw" 22#6 hopc (by decide +kernel))
  let X := callSuccessA E
  have hcoreR : ∀ (rn : String) (w : Nat),
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).regs rn w =
        ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
          ((Hw.refillAct m).run σ σ)).regs rn w := by
    intro rn w
    rw [coreAct_run_retire_eq m σ _ hifv hcl,
      retireAct_run_regs σ _ E rfl rn w,
      retireFor_gateCall_success σ _ E hopc hok]
    rfl
  have hframes := callAbstractSuccess_structural_frames (Hw.abs σ) base E
    cal g (operandsOf W).rd 0 ((Hw.callDepth E).eval σ).toNat
  have hcaps : ∀ x, (τ2.doms x).caps = ((Hw.abs σ).doms x).caps := by
    intro x
    rw [show (τ2.doms x).caps = (base.doms x).caps from hframes.1 x]
    exact refillPhase_caps m (Hw.abs σ) x
  have hgens : ∀ x, (τ2.doms x).slotGen =
      ((Hw.abs σ).doms x).slotGen := by
    intro x
    rw [show (τ2.doms x).slotGen = (base.doms x).slotGen from
      hframes.2.1 x]
    exact refillPhase_slotGen m (Hw.abs σ) x
  have hregions : ∀ x, (τ2.doms x).regions =
      ((Hw.abs σ).doms x).regions := by
    intro x
    rw [show (τ2.doms x).regions = (base.doms x).regions from
      hframes.2.2.1 x]
    exact refillPhase_regions m (Hw.abs σ) x
  have hjob : τ2.mover = Hw.absMover σ := by
    rw [show τ2.mover = base.mover from hframes.2.2.2.1]
    exact refillPhase_mover m (Hw.abs σ)
  have hauth : ∀ (ow : Expr 2) (sa : Expr 12),
      ((Hw.orAll ((List.finRange numDomains).flatMap fun x =>
        (List.finRange numRegions).map fun r =>
          Hw.andAll [Expr.eq ow (Hw.dLit x), Hw.rgnVPostE x r,
            Hw.rgnCoversVal (Hw.rgnValPostE x r) sa
              ⟨false, true, false⟩])).eval σ = 1#1) ↔
        τ2.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
          ⟨false, true, false⟩ = true := by
    intro ow sa
    rw [sAuth_quiescent_eval σ hin.killed hmapz hunmapz ow sa]
    simp only [MachineState.domCovers, hregions]
  have hmem : ∀ b : Addr,
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
        b.toNat 32 = τ2.mem b := by
    intro b
    rw [coreAct_mem_gateCall_zero_arg m σ E hifv hcl hifsel hifexcl
      hopc (by simpa [E] using hargZero) b]
    change (Hw.abs σ).mem b = τ2.mem b
    rw [show τ2.mem = base.mem from hframes.2.2.2.2]
    rfl
  have hsw : ∀ sc : Expr 12, Expr.eval σ
      (((List.finRange numDomains).foldr
        (fun d acc' =>
          Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
              Hw.domCoversE d
                (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                ⟨false, true, false⟩,
              .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX)
                0 12) sc]) (Hw.readReg d Hw.rs2E) acc')
        (.memRead 32 "mem" sc))) = τ2.mem (sc.eval σ) := by
    intro sc
    rw [srcWord_quiescent σ hswz sc]
    change (Hw.abs σ).mem (sc.eval σ) = τ2.mem (sc.eval σ)
    rw [show τ2.mem = base.mem from hframes.2.2.2.2]
    rfl
  refine square_retire_install m hwf hfit σ hsync hifv hcl hin X τ2
    hcoreR ?_ hspec ?_ ?_ hjob ?_ ?_ ?_ ?_ hauth hmem hsw ?_ ?_
  · unfold X
    exact ifv_notin_callSuccess E
  · intro x
    change Hw.absDom ((callSuccessA E).run σ acc0) x = τ2.doms x
    exact congrFun (congrArg MachineState.doms habsCall) x
  · intro gate
    change Hw.absGate ((callSuccessA E).run σ acc0) gate = τ2.gates gate
    exact congrFun (congrArg MachineState.gates habsCall) gate
  · intro _
    exact congrFun (hcaps _) _
  · intro _
    exact congrFun (hgens _) _
  · intro _
    exact congrFun (hcaps _) _
  · intro _
    exact congrFun (hgens _) _
  · rfl
  · rfl

end Machines.Lnp64u.Theorems.RMC
