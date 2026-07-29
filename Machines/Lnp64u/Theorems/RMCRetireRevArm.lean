-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireRevState
import Machines.Lnp64u.Theorems.RMCRetireGateShared
import Machines.Lnp64u.Theorems.RMCRetireGateSquare

/-!
# R-MC retirement: full cap_revoke arm

This module assembles the converged revoke engine, structural destruction,
region sweep, and Mover bridges into the retiring instruction square.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

private theorem ifv_notin_revSuccessA (E : DomainId) :
    (("if_v" : String), (1 : Nat)) ∉ (revSuccessArmA E).regWrites := by
  fin_cases E <;> decide +kernel

/-- A selected but failed revoke has no structural kill footprint because
`revOkE` gates its contribution to the global core kill tree. -/
theorem killedByCoreE_rev_failed (sigma : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval sigma = 1#1)
    (hif : ∀ d : DomainId, (Hw.ifDomIs d).eval sigma =
      if d = E then 1#1 else 0#1)
    (hdrop : (Hw.isMn "cap_drop").eval sigma ≠ 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval sigma = 1#1)
    (hcall : (Hw.isMn "gate_call").eval sigma ≠ 1#1)
    (hreturn : (Hw.isMn "gate_return").eval sigma ≠ 1#1)
    (hbad : ∀ d : DomainId, d = E → (Hw.revOkE d).eval sigma = 0#1)
    (dm : Expr 2) (sl : Expr 4) :
    (Hw.killedByCoreE dm sl).eval sigma = 0#1 := by
  have hdrop0 : (Hw.isMn "cap_drop").eval sigma = 0#1 :=
    bv1_ne_one.mp hdrop
  have hcall0 : (Hw.isMn "gate_call").eval sigma = 0#1 :=
    bv1_ne_one.mp hcall
  have hreturn0 : (Hw.isMn "gate_return").eval sigma = 0#1 :=
    bv1_ne_one.mp hreturn
  have honeAnd : ∀ x : BitVec 1, 1#1 &&& x = x := by decide
  have hzeroAnd : ∀ x : BitVec 1, 0#1 &&& x = 0#1 := by decide
  have hzeroOr : ∀ x : BitVec 1, 0#1 ||| x = x := by decide
  have horZero : ∀ x : BitVec 1, x ||| 0#1 = x := by decide
  unfold Hw.killedByCoreE
  fin_cases E <;>
    simp [Hw.orAll, List.finRange, Expr.eval, Fin.ext_iff, hret, hif,
      hdrop0, hrev, hbad, hcall0, hreturn0, honeAnd, hzeroAnd,
      hzeroOr, horZero]

/-- Failed revokes are Mover-inert once the unrelated job-install gate is
known off. -/
theorem Inert.of_failed_rev (sigma : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval sigma = 1#1)
    (hif : ∀ d : DomainId, (Hw.ifDomIs d).eval sigma =
      if d = E then 1#1 else 0#1)
    (hdrop : (Hw.isMn "cap_drop").eval sigma ≠ 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval sigma = 1#1)
    (hcall : (Hw.isMn "gate_call").eval sigma ≠ 1#1)
    (hreturn : (Hw.isMn "gate_return").eval sigma ≠ 1#1)
    (hbad : ∀ d : DomainId, d = E → (Hw.revOkE d).eval sigma = 0#1)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval sigma = 0#1) :
    Inert sigma where
  killed := killedByCoreE_rev_failed sigma E hret hif hdrop hrev hcall
    hreturn hbad
  newJob := hnew

/-- With map and unmap off, post-core region validity is the old valid bit
masked by the converged revoke kill predicate. -/
theorem rgnVPostE_rev_eval (sigma : Loom.Hw.St)
    (hkills : ∀ dm sl, (Hw.killedByCoreE dm sl).eval sigma =
      (Hw.revKilled dm sl).eval sigma)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval sigma = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval sigma = 0#1)
    (c : DomainId) (r : RegionId) :
    (Hw.rgnVPostE c r).eval sigma =
      sigma.regs (Hw.drgnV c r) 1 &&&
        ~~~((Hw.revKilled
          (Hw.field (.reg 42 (Hw.drgn c r)) 40 2)
          (Hw.field (.reg 42 (Hw.drgn c r)) 36 4)).eval sigma) := by
  show (if (Hw.andAll (Hw.retiringE :: _)).eval sigma = 1#1 then _
    else if (Hw.andAll (Hw.retiringE :: _)).eval sigma = 1#1 then _
    else (Expr.and (.reg 1 (Hw.drgnV c r))
      (.not (Hw.killedByCoreE _ _))).eval sigma) = _
  rw [hmapz c r, hunmapz c r]
  rw [if_neg (by decide), if_neg (by decide)]
  show sigma.regs (Hw.drgnV c r) 1 &&&
      ~~~((Hw.killedByCoreE _ _).eval sigma) = _
  rw [hkills]

/-- The successful circuit payload, run after refill and latch clear,
decodes to the complete named abstract revoke state on every domain. -/
theorem absDom_revSuccessA_refill (m : Manifest) (hwfm : m.WF)
    (hfit : Fits m) (sigma : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (sigma.regs (Hw.drctr d) 32).toNat =
      (sigma.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrv : RvSync sigma)
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hopc : (sigma.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2)
    (hwf : Wf (Hw.abs sigma)) (E : DomainId) (RD : RegId)
    (hrd : (Hw.rdE.eval sigma).toNat = RD.val) (c : DomainId) :
    Hw.absDom
        ((Act.seq (.write 1 "if_v" (.lit 0)) (revSuccessArmA E)).run
          sigma ((Hw.refillAct m).run sigma sigma)) c =
      (revAbstractSuccess m (Hw.abs sigma) E RD (rvRoot sigma)).doms c := by
  let acc := (Act.write 1 "if_v" (.lit 0)).run sigma
    ((Hw.refillAct m).run sigma sigma)
  have habsAcc : Hw.abs acc =
      { refillPhase m (Hw.abs sigma) with inflight := none } :=
    abs_refill_clearInflight m hwfm hfit sigma hsync
  have hacc {rn : String} {w : Nat}
      (hif : (rn, w) ≠ ("if_v", 1))
      (hrefill : (rn, w) ∉
        ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
          ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
          ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) :
      acc.regs rn w = sigma.regs rn w := by
    rw [show acc.regs rn w =
        ((Hw.refillAct m).run sigma sigma).regs rn w from
      frame (by simpa [Act.regWrites] using hif) sigma
        ((Hw.refillAct m).run sigma sigma)]
    exact refill_pres m sigma hrefill
  have haccV : ∀ d s, acc.regs (Hw.dcapV d s) 1 =
      sigma.regs (Hw.dcapV d s) 1 := by
    intro d s
    exact hacc (by fin_cases d <;> fin_cases s <;> decide)
      (by fin_cases d <;> fin_cases s <;> decide)
  have haccG : ∀ d s, acc.regs (Hw.dgen d s) 8 =
      sigma.regs (Hw.dgen d s) 8 := by
    intro d s
    exact hacc (by fin_cases d <;> fin_cases s <;> decide)
      (by fin_cases d <;> fin_cases s <;> decide)
  have hcaps : ∀ d, ((Hw.abs acc).doms d).caps =
      ((Hw.abs sigma).doms d).caps := by
    intro d
    rw [habsAcc]
    exact refillPhase_caps m (Hw.abs sigma) d
  have hrgnV : ∀ d r, acc.regs (Hw.drgnV d r) 1 =
      sigma.regs (Hw.drgnV d r) 1 := by
    intro d r
    exact hacc (by fin_cases d <;> fin_cases r <;> decide)
      (by fin_cases d <;> fin_cases r <;> decide)
  have hrgn : ∀ d r, acc.regs (Hw.drgn d r) 42 =
      sigma.regs (Hw.drgn d r) 42 := by
    intro d r
    exact hacc (by fin_cases d <;> fin_cases r <;> decide)
      (by fin_cases d <;> fin_cases r <;> decide)
  have hpc : ∀ d, acc.regs (Hw.dpc d) 12 =
      sigma.regs (Hw.dpc d) 12 := by
    intro d
    exact hacc (by fin_cases d <;> decide) (by fin_cases d <;> decide)
  have hwfAcc : Wf (Hw.abs acc) := by
    rw [habsAcc]
    apply wf_of_skeleton_sameGates (refillPhase m (Hw.abs sigma))
      { refillPhase m (Hw.abs sigma) with inflight := none }
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) rfl rfl (by simp)
    exact refillPhase_preserves_wf m (Hw.abs sigma) hwf
  have hdom := absDom_revSuccessA sigma acc hrv hifv hopc hcl
    haccV haccG hcaps hrgnV hrgn hpc hwfAcc E RD hrd c
  change Hw.absDom ((revSuccessArmA E).run sigma acc) c = _
  unfold revSuccessArmA
  rw [hdom]
  rw [habsAcc]
  unfold revAbstractSuccess revRetireBase
  rw [destroyMarked_setPc, sweepRegions_setPc, sweepMover_setPc]
  by_cases hc : c = E
  · subst c
    simp [MachineState.setDom]
  · simp [MachineState.setDom, hc]

/-- The revoke payload does not alter gate records; after refill its gate
abstraction is the gate face of the named successful abstract state. -/
theorem absGate_revSuccessA_refill (m : Manifest) (hwfm : m.WF)
    (hfit : Fits m) (sigma : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (sigma.regs (Hw.drctr d) 32).toNat =
      (sigma.regs "cycle" 32).toNat % (m.doms d).periodP)
    (E : DomainId) (RD : RegId) (g : GateId) :
    Hw.absGate
        ((Act.seq (.write 1 "if_v" (.lit 0)) (revSuccessArmA E)).run
          sigma ((Hw.refillAct m).run sigma sigma)) g =
      (revAbstractSuccess m (Hw.abs sigma) E RD (rvRoot sigma)).gates g := by
  have hquiet : ∀ q ∈ gateReadNames g,
      q ∉ (Act.seq (.write 1 "if_v" (.lit 0))
        (revSuccessArmA E)).regWrites := by
    clear * - g E
    fin_cases g <;> fin_cases E <;> decide +kernel
  have hg := absGate_congr g (fun q hq => frame (hquiet q hq) sigma
    ((Hw.refillAct m).run sigma sigma))
  rw [hg]
  have hrefill := abs_refill m hwfm hfit sigma hsync
  have hgate : Hw.absGate ((Hw.refillAct m).run sigma sigma) g =
      ((refillPhase m (Hw.abs sigma)).gates g) := by
    change (Hw.abs ((Hw.refillAct m).run sigma sigma)).gates g = _
    rw [hrefill]
  rw [hgate]
  unfold revAbstractSuccess revRetireBase
  simp [MachineState.setDom]

/-- Every region in the named successful state is exactly the hardware
post-core region selector and unchanged packed payload. -/
theorem revAbstractSuccess_regionEq (m : Manifest) (hwfm : m.WF)
    (hfit : Fits m) (sigma : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (sigma.regs (Hw.drctr d) 32).toNat =
      (sigma.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrv : RvSync sigma)
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hopc : (sigma.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2)
    (hwf : Wf (Hw.abs sigma)) (E : DomainId) (RD : RegId)
    (hrd : (Hw.rdE.eval sigma).toNat = RD.val)
    (hkills : ∀ dm sl, (Hw.killedByCoreE dm sl).eval sigma =
      (Hw.revKilled dm sl).eval sigma)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval sigma = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval sigma = 0#1)
    (c : DomainId) (r : RegionId) :
    ((revAbstractSuccess m (Hw.abs sigma) E RD
        (rvRoot sigma)).doms c).regions r =
      if (Hw.rgnVPostE c r).eval sigma = 1#1 then
        some (Hw.decRegion (sigma.regs (Hw.drgn c r) 42)) else none := by
  let acc := (Act.write 1 "if_v" (.lit 0)).run sigma
    ((Hw.refillAct m).run sigma sigma)
  let out := (revSuccessArmA E).run sigma acc
  have hdom := absDom_revSuccessA_refill m hwfm hfit sigma hsync hrv
    hifv hopc hcl hwf E RD hrd c
  have hacc {rn : String} {w : Nat}
      (hif : (rn, w) ≠ ("if_v", 1))
      (hrefill : (rn, w) ∉
        ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
          ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
          ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) :
      acc.regs rn w = sigma.regs rn w := by
    rw [show acc.regs rn w =
        ((Hw.refillAct m).run sigma sigma).regs rn w from
      frame (by simpa [Act.regWrites] using hif) sigma
        ((Hw.refillAct m).run sigma sigma)]
    exact refill_pres m sigma hrefill
  have hv : out.regs (Hw.drgnV c r) 1 =
      (Hw.rgnVPostE c r).eval sigma := by
    unfold out revSuccessArmA
    rw [revSuccessA_run_rgnV, rgnVPostE_rev_eval sigma hkills hmapz
      hunmapz]
    rw [hacc (by fin_cases c <;> fin_cases r <;> decide)
      (by fin_cases c <;> fin_cases r <;> decide)]
    change (if (sigma.regs (Hw.drgnV c r) 1 &&&
      (Hw.revKilled
        (Hw.field (.reg 42 (Hw.drgn c r)) 40 2)
        (Hw.field (.reg 42 (Hw.drgn c r)) 36 4)).eval sigma) = 1#1
      then 0#1 else sigma.regs (Hw.drgnV c r) 1) =
        sigma.regs (Hw.drgnV c r) 1 &&&
          ~~~((Hw.revKilled
            (Hw.field (.reg 42 (Hw.drgn c r)) 40 2)
            (Hw.field (.reg 42 (Hw.drgn c r)) 36 4)).eval sigma)
    generalize sigma.regs (Hw.drgnV c r) 1 = v
    generalize (Hw.revKilled
      (Hw.field (.reg 42 (Hw.drgn c r)) 40 2)
      (Hw.field (.reg 42 (Hw.drgn c r)) 36 4)).eval sigma = k
    revert v k
    decide
  have hval : out.regs (Hw.drgn c r) 42 =
      sigma.regs (Hw.drgn c r) 42 := by
    unfold out revSuccessArmA
    rw [revSuccessA_run_rgn]
    exact hacc (by fin_cases c <;> fin_cases r <;> decide)
      (by fin_cases c <;> fin_cases r <;> decide)
  rw [← hdom]
  change (if out.regs (Hw.drgnV c r) 1 = 1#1 then
    some (Hw.decRegion (out.regs (Hw.drgn c r) 42)) else none) = _
  rw [hv, hval]

/-- The Mover status-authority tree decodes against the complete successful
revoke state. -/
theorem sAuth_rev_eval (m : Manifest) (hwfm : m.WF) (hfit : Fits m)
    (sigma : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (sigma.regs (Hw.drctr d) 32).toNat =
      (sigma.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrv : RvSync sigma)
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hopc : (sigma.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2)
    (hwf : Wf (Hw.abs sigma)) (E : DomainId) (RD : RegId)
    (hrd : (Hw.rdE.eval sigma).toNat = RD.val)
    (hkills : ∀ dm sl, (Hw.killedByCoreE dm sl).eval sigma =
      (Hw.revKilled dm sl).eval sigma)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval sigma = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval sigma = 0#1)
    (ow : Expr 2) (sa : Expr 12) :
    ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
        (List.finRange numRegions).map fun r =>
          Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
            Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
              { r := false, w := true, x := false }])).eval sigma = 1#1) ↔
      (revAbstractSuccess m (Hw.abs sigma) E RD
        (rvRoot sigma)).domCovers
          (finOfBv (by decide) (ow.eval sigma)) (sa.eval sigma)
            { r := false, w := true, x := false } = true := by
  apply sAuth_region_eq_eval sigma
    (revAbstractSuccess m (Hw.abs sigma) E RD (rvRoot sigma)) hmapz
  intro c r
  exact revAbstractSuccess_regionEq m hwfm hfit sigma hsync hrv hifv
    hopc hcl hwf E RD hrd hkills hmapz hunmapz c r

/-- The retiring core's revoke status write is exactly the memory face of
the ISA-level `sweepMover` contained in `revAbstractSuccess`. -/
theorem coreAct_mem_revAbstractSuccess (m : Manifest) (hwfm : m.WF)
    (hfit : Fits m) (sigma : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (sigma.regs (Hw.drctr d) 32).toNat =
      (sigma.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrv : RvSync sigma)
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hopc : (sigma.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2)
    (hwf : Wf (Hw.abs sigma)) (E : DomainId) (RD : RegId)
    (hrd : (Hw.rdE.eval sigma).toNat = RD.val)
    (hifsel : (Hw.ifDomIs E).eval sigma = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E →
      (Hw.ifDomIs d).eval sigma ≠ 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval sigma = 1#1)
    (hok : (Hw.revOkE E).eval sigma = 1#1)
    (hkills : ∀ dm sl, (Hw.killedByCoreE dm sl).eval sigma =
      (Hw.revKilled dm sl).eval sigma)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval sigma = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval sigma = 0#1)
    (b : Addr) :
    ((Hw.coreAct m).run sigma ((Hw.refillAct m).run sigma sigma)).mems
        "mem" b.toNat 32 =
      (revAbstractSuccess m (Hw.abs sigma) E RD (rvRoot sigma)).mem b := by
  let base := (((revRetireBase m (Hw.abs sigma) E).destroyMarked
    ((Hw.abs sigma).marks (rvRoot sigma))).sweepRegions)
  let target := revAbstractSuccess m (Hw.abs sigma) E RD (rvRoot sigma)
  let killJob : MoverJob → Prop := fun job =>
    (base.liveRef job.src && base.liveRef job.dst) = false
  have hliveBase : ∀ r, base.liveRef r = target.liveRef r := by
    intro r
    unfold target revAbstractSuccess
    change base.liveRef r =
      (base.sweepMover.setDom E (fun ds => ds.setReg RD 0)).liveRef r
    unfold MachineState.liveRef DomainState.liveCap
    by_cases hd : r.dom = E
    · rw [hd]
      simp [MachineState.setDom]
    · simp [MachineState.setDom, hd]
  have hnd : ((Hw.opCircs E).map Prod.fst).Nodup := by
    rw [opCircs_fst_all E]
    exact allMns_nodup
  have hq : ∀ p ∈ Hw.opCircs E, p.1 ≠ "cap_revoke" →
      (Hw.isMn p.1).eval sigma = 0#1 ∨ isLit0 p.2.memEn = true := by
    intro p hp hne
    left
    exact bv1_ne_one.mp (isMn_ne_of_opc sigma p.1 18#6 hopc
      ((by decide +kernel : ∀ mn' ∈ allMns, mn' ≠ "cap_revoke" →
        (18#6 : BitVec 6) ≠ Hw.opcodeOf mn') p.1
        (by rw [← opCircs_fst_all E]; exact List.mem_map_of_mem hp) hne))
  have hmemrev : ("cap_revoke", Hw.revCirc E) ∈ Hw.opCircs E :=
    List.mem_append_right _
      (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hport := retireMem_op_sel sigma E "cap_revoke" (Hw.revCirc E)
    hifsel hifexcl hrev hmemrev hnd hq
  apply coreAct_mem_sweep_success_pred m sigma (Hw.revOkE E)
    Hw.revKilled (Hw.revCirc E) killJob base target hifv hcl hport
  · rfl
  · rfl
  · rfl
  · exact hok
  · cases habs : Hw.absMover sigma with
    | none =>
        simpa [habs] using movKilledE_rev_iff sigma hrv hifv hopc hcl
    | some job =>
        simp only
        unfold killJob
        rw [← movKilledE_core_rev_endpoint_iff sigma base hrv hifv hopc
          hcl hkills hwf (fun r => (hliveBase r).trans
            (revAbstractSuccess_liveRef m (Hw.abs sigma) E RD
              (rvRoot sigma) r)) job habs]
        unfold Hw.movKilledE
        simp only [Expr.eval]
        rw [← hkills Hw.movSrcDom Hw.movSrcSlot,
          ← hkills Hw.movDstDom Hw.movDstSlot]
  · intro job habs
    rw [statusAuthE_post_eval sigma Hw.revKilled hkills hmapz hunmapz]
    rw [sAuth_rev_eval m hwfm hfit sigma hsync hrv hifv hopc hcl hwf E
      RD hrd hkills hmapz hunmapz (.reg 2 "mov_owner")
      (.reg 12 "mov_status")]
    have hv : sigma.regs "mov_v" 1 = 1#1 := by
      by_contra hn
      rw [absMover_none sigma hn] at habs
      contradiction
    have hcanon := Option.some.inj ((absMover_some sigma hv).symm.trans habs)
    have howner : finOfBv (by decide)
        (sigma.regs "mov_owner" 2) = job.owner :=
      congrArg MoverJob.owner hcanon
    have hstatus : sigma.regs "mov_status" 12 = job.statusAddr :=
      congrArg MoverJob.statusAddr hcanon
    simp only [Expr.eval]
    rw [howner, hstatus]
    change (target.domCovers job.owner job.statusAddr
      { r := false, w := true, x := false } = true) ↔ _
    have hregions : ∀ d, (target.doms d).regions =
        (base.doms d).regions := by
      intro d
      unfold target revAbstractSuccess
      change ((base.sweepMover.setDom E
        (fun ds => ds.setReg RD 0)).doms d).regions = _
      by_cases hd : d = E
      · subst d
        simp [MachineState.setDom]
      · simp [MachineState.setDom, hd]
    unfold MachineState.domCovers
    rw [hregions]
  · intro a
    rfl
  · intro a
    unfold target revAbstractSuccess
    change (base.sweepMover.setDom E (fun ds => ds.setReg RD 0)).mem a = _
    have hmover : base.mover = Hw.absMover sigma := by rfl
    rw [show (base.sweepMover.setDom E
      (fun ds => ds.setReg RD 0)).mem a = base.sweepMover.mem a from rfl]
    cases habs : Hw.absMover sigma with
    | none =>
        have hb : base.mover = none := hmover.trans habs
        simp [MachineState.sweepMover, hb]
    | some job =>
        have hb : base.mover = some job := hmover.trans habs
        by_cases hbt : (base.liveRef job.src &&
            base.liveRef job.dst) = true
        ·
          have hkfalse : ¬ killJob job := by
            unfold killJob
            rw [hbt]
            decide
          unfold MachineState.sweepMover
          rw [hb]
          simp only
          rw [if_pos hbt, if_neg hkfalse]
        · have hbf : (base.liveRef job.src && base.liveRef job.dst) = false :=
            Bool.eq_false_of_not_eq_true hbt
          have hktrue : killJob job := by
            unfold killJob
            exact hbf
          unfold MachineState.sweepMover
          rw [hb]
          simp only
          rw [if_neg hbt, if_pos hktrue]
          have hcover : ({ base with mover := none } : MachineState).domCovers
              job.owner job.statusAddr { r := false, w := true, x := false } =
                base.domCovers job.owner job.statusAddr
                  { r := false, w := true, x := false } := rfl
          rw [hcover]
          by_cases hc : base.domCovers job.owner job.statusAddr
              { r := false, w := true, x := false } = true
          · rw [if_pos hc, if_pos hc]
            by_cases ha : a = job.statusAddr
            · subst a
              simp [MachineState.write, Loom.Fun.update_same]
            · simp [MachineState.write, ha]
          · rw [if_neg hc, if_neg hc]

/-- If revoke leaves the current Mover job live, its ISA-level sweep writes
no status word, so the named success state's memory is the pre-cycle memory. -/
theorem revAbstractSuccess_mem_of_surviving_job (m : Manifest)
    (sigma : Loom.Hw.St) (E : DomainId) (RD : RegId) (job : MoverJob)
    (habs : Hw.absMover sigma = some job)
    (hlive : ((revAbstractSuccess m (Hw.abs sigma) E RD
      (rvRoot sigma)).liveRef job.src &&
      (revAbstractSuccess m (Hw.abs sigma) E RD
        (rvRoot sigma)).liveRef job.dst) = true)
    (b : Addr) :
    (revAbstractSuccess m (Hw.abs sigma) E RD (rvRoot sigma)).mem b =
      sigma.mems "mem" b.toNat 32 := by
  let base := (((revRetireBase m (Hw.abs sigma) E).destroyMarked
    ((Hw.abs sigma).marks (rvRoot sigma))).sweepRegions)
  let target := revAbstractSuccess m (Hw.abs sigma) E RD (rvRoot sigma)
  have hmover : base.mover = some job := by
    change (Hw.abs sigma).mover = some job
    exact habs
  have hliveBase : (base.liveRef job.src && base.liveRef job.dst) = true := by
    have hsrc : base.liveRef job.src = target.liveRef job.src := by
      unfold target revAbstractSuccess
      change base.liveRef job.src =
        (base.sweepMover.setDom E (fun ds => ds.setReg RD 0)).liveRef job.src
      unfold MachineState.liveRef DomainState.liveCap
      by_cases hd : job.src.dom = E
      · rw [hd]
        simp [MachineState.setDom]
      · simp [MachineState.setDom, hd]
    have hdst : base.liveRef job.dst = target.liveRef job.dst := by
      unfold target revAbstractSuccess
      change base.liveRef job.dst =
        (base.sweepMover.setDom E (fun ds => ds.setReg RD 0)).liveRef job.dst
      unfold MachineState.liveRef DomainState.liveCap
      by_cases hd : job.dst.dom = E
      · rw [hd]
        simp [MachineState.setDom]
      · simp [MachineState.setDom, hd]
    rw [hsrc, hdst]
    exact hlive
  change target.mem b = _
  unfold target revAbstractSuccess
  change base.sweepMover.mem b = _
  unfold MachineState.sweepMover
  rw [hmover]
  simp only
  rw [if_pos hliveBase]
  rfl

/-- Full retiring `cap_revoke` square, assuming the bounded mark engine is
synchronized with the abstract descendant closure. -/
theorem square_retire_rev (m : Manifest) (hwfm : m.WF) (hfit : Fits m)
    (sigma : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (sigma.regs (Hw.drctr d) 32).toNat =
      (sigma.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero sigma) (hkc : KindCanon sigma)
    (hrv : RvSync sigma)
    (hsr : (machine m).Reachable (Hw.abs sigma))
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2)
    (hopc : (sigma.regs "if_word" 32).extractLsb' 0 6 = 18#6) :
    Hw.abs ((Hw.core m).cycle sigma) = step m (Hw.abs sigma) := by
  set W := sigma.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (sigma.regs "if_dom" 2)
  have hop : Machines.Lnp64u.sig.opcodeOf W = (18#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (18#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel sigma E rfl
  have hif : ∀ d : DomainId, (Hw.ifDomIs d).eval sigma =
      if d = E then 1#1 else 0#1 := by
    intro d
    by_cases hd : d = E
    · subst d
      rw [if_pos rfl]
      exact hifsel
    · rw [if_neg hd, bv1_ne_one.mp (hifexcl d hd)]
  have hrev : (Hw.isMn "cap_revoke").eval sigma = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "cap_revoke" = 18#6).symm
  have hdrop : (Hw.isMn "cap_drop").eval sigma ≠ 1#1 :=
    isMn_ne_of_opc sigma "cap_drop" 18#6 hopc (by decide +kernel)
  have hcall : (Hw.isMn "gate_call").eval sigma ≠ 1#1 :=
    isMn_ne_of_opc sigma "gate_call" 18#6 hopc (by decide +kernel)
  have hreturn : (Hw.isMn "gate_return").eval sigma ≠ 1#1 :=
    isMn_ne_of_opc sigma "gate_return" 18#6 hopc (by decide +kernel)
  have hret := retiringE_one sigma hifv hcl
  have hnew : ∀ d : DomainId, (Hw.newJobSet d).eval sigma = 0#1 := by
    intro d
    apply andAll_zero_of_mem sigma
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
    exact isMn_ne_of_opc sigma "move" 18#6 hopc (by decide +kernel)
  have hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval sigma = 0#1 := fun c r =>
    andAll_zero_of_mem sigma
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc sigma "map" 18#6 hopc (by decide +kernel))
  have hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval sigma = 0#1 := fun c r =>
    andAll_zero_of_mem sigma
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc sigma "unmap" 18#6 hopc (by decide +kernel))
  have hswz : ∀ (d : DomainId) (sc : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
        Hw.domCoversE d
          (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          { r := false, w := true, x := false },
        .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          sc]).eval sigma = 0#1 := fun d sc =>
    andAll_zero_of_mem sigma
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc sigma "sw" 18#6 hopc (by decide +kernel))
  have hsel := retireFor_rev_ladder sigma E hopc
  have hfl : (refillPhase m (Hw.abs sigma)).inflight = some
      { dom := finOfBv (by decide) (sigma.regs "if_dom" 2)
        word := W
        cyclesLeft := (sigma.regs "if_cl" 8).toNat } := by
    show Hw.absInflight sigma = _
    exact absInflight_some sigma hifv
  have hR1 : (Hw.readReg E Hw.rs1E).eval sigma =
      ((Hw.abs sigma).doms E).reg (operandsOf W).rs1 :=
    readReg_eval sigma hz E Hw.rs1E (operandsOf W).rs1 rfl
  set HWv := ((Hw.abs sigma).doms E).reg (operandsOf W).rs1
  have hRD : (((revRetireBase m (Hw.abs sigma) E).doms E).reg
      (operandsOf W).rs1) = HWv := by
    exact specReg_bridge m sigma E _
  have hcore0 : corePhase m (refillPhase m (Hw.abs sigma)) =
      retire { refillPhase m (Hw.abs sigma) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (sigma.regs "if_cl" 8).toNat ≤ 1)]
  have hDO : retire { refillPhase m (Hw.abs sigma) with inflight := none }
      E W =
      (match ((SpecM.reg E (operandsOf W).rs1 >>= fun hw =>
        Machines.Lnp64u.Isa.capLive E hw >>= fun x =>
        let (s, g, e) := x
        SpecM.require (e.kind.cls = .mem) .badCap >>= fun _ =>
        SpecM.get >>= fun rho =>
        let marked := rho.marks ⟨E, s, g⟩
        SpecM.set (((rho.destroyMarked marked).sweepRegions).sweepMover) >>=
          fun _ => SpecM.setReg E (operandsOf W).rd 0)
        (revRetireBase m (Hw.abs sigma) E)) with
      | .ok _ rho => rho
      | .err e rho => rho.setDom E
          (fun ds => ds.setReg (operandsOf W).rd e.toWord)
      | .fault fl => haltWith
          { refillPhase m (Hw.abs sigma) with inflight := none } E fl) := by
    have hfind : isa.find? (fun d => d.opcode == (18#6 : BitVec 6)) =
        some (Machines.Lnp64u.Isa.system.get ⟨2, by decide⟩) := by rfl
    have hexec :
        (Machines.Lnp64u.Isa.system.get ⟨2, by decide⟩).sem.exec =
          (fun c => do
            let hw ← SpecM.reg c.d c.op.rs1
            let (s, g, e) ← Machines.Lnp64u.Isa.capLive c.d hw
            SpecM.require (e.kind.cls = .mem) .badCap
            let rho ← SpecM.get
            let marked := rho.marks ⟨c.d, s, g⟩
            SpecM.set (((rho.destroyMarked marked).sweepRegions).sweepMover)
            SpecM.setReg c.d c.op.rd 0) := by rfl
    rw [retire_of_decode_some _ E W _ (hdec.trans hfind), hexec]
    rfl
  have hSval : (finOfBv (by decide : 2 ^ 4 = numSlots)
      (HWv.extractLsb' 0 4)).val =
      (((Hw.readReg E Hw.rs1E).eval sigma).extractLsb' 0 4).toNat := by
    rw [hR1]
    rfl
  have hlivE := capSel_live_eval sigma E (Hw.readReg E Hw.rs1E) _ hSval
  rw [hR1] at hlivE
  have hnd : ((Hw.opCircs E).map Prod.fst).Nodup := by
    rw [opCircs_fst_all E]
    exact allMns_nodup
  have hq : ∀ p ∈ Hw.opCircs E, p.1 ≠ "cap_revoke" →
      (Hw.isMn p.1).eval sigma = 0#1 ∨ isLit0 p.2.memEn = true := by
    intro p hp hne
    left
    exact bv1_ne_one.mp (isMn_ne_of_opc sigma p.1 18#6 hopc
      ((by decide +kernel : ∀ mn' ∈ allMns, mn' ≠ "cap_revoke" →
        (18#6 : BitVec 6) ≠ Hw.opcodeOf mn') p.1
        (by rw [← opCircs_fst_all E]; exact List.mem_map_of_mem hp) hne))
  have hmemrev : ("cap_revoke", Hw.revCirc E) ∈ Hw.opCircs E :=
    List.mem_append_right _
      (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hport := retireMem_op_sel sigma E "cap_revoke" (Hw.revCirc E)
    hifsel hifexcl hrev hmemrev hnd hq
  have hcoremem_of_revOk_zero (hok0 : (Hw.revOkE E).eval sigma = 0#1) :
      ∀ b : Addr,
        ((Hw.coreAct m).run sigma ((Hw.refillAct m).run sigma sigma)).mems
          "mem" b.toNat 32 = sigma.mems "mem" b.toNat 32 := by
    intro b
    rw [coreAct_run_retire_eq m sigma _ hifv hcl,
      retireAct_run_mems sigma _ b.toNat 32]
    show (if (((List.finRange numDomains).foldr
        (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
          let (en_d, ad_d, da_d) := Hw.retireMemFor d
          let g := Expr.and (Hw.ifDomIs d) en_d
          (.or g acc'.1, .mux g ad_d acc'.2.1,
            .mux g da_d acc'.2.2))
        ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
          (.lit 0 : Expr 32))).1).eval sigma = 1#1 then _
      else ((Hw.refillAct m).run sigma sigma)).mems "mem" b.toNat 32 = _
    rw [if_neg (by
      rw [hport.1]
      show ¬((Hw.revCirc E).memEn.eval sigma = 1#1)
      unfold Hw.revCirc Hw.sweepMem Hw.andAll
      change ¬((Hw.revOkE E).eval sigma &&& _ = 1#1)
      rw [hok0]
      exact (by decide : ∀ q : BitVec 1, ¬(0#1 &&& q = 1#1)) _)]
    rw [refill_pres_mem m sigma "mem" b.toNat 32]
  by_cases hlv : sigma.regs (Hw.dcapV E
        (finOfBv (by decide) (HWv.extractLsb' 0 4))) 1 = 1#1 ∧
      sigma.regs (Hw.dgen E (finOfBv (by decide)
        (HWv.extractLsb' 0 4))) 8 = HWv.extractLsb' 4 8 ∧
      HWv.extractLsb' 4 8 ≠ 0
  case neg =>
    have hlive0 : ¬((Hw.revSel E).live.eval sigma = 1#1) :=
      fun hc => hlv (hlivE.mp hc)
    have hlcN : ((revRetireBase m (Hw.abs sigma) E).doms E).liveCap
        (Handle.decode HWv).slot (Handle.decode HWv).gen = none := by
      change ((({ refillPhase m (Hw.abs sigma) with inflight := none }).setDom
        E (fun ds => { ds with pc := ds.pc + 1 })).doms E).liveCap
          (Handle.decode HWv).slot (Handle.decode HWv).gen = none
      rw [specLiveCap_bridge, abs_liveCap]
      exact if_neg hlv
    have hbad : ∀ d : DomainId, d = E →
        (Hw.revOkE d).eval sigma = 0#1 := by
      intro d hd
      subst d
      unfold Hw.revOkE Hw.okOf Hw.revChecks Hw.andAll
      change ~~~(~~~((Hw.revSel E).live.eval sigma)) &&&
        ~~~(~~~((Expr.and (Hw.revSel E).clsOk
          (Hw.kIsMem (Hw.revSel E).kindW)).eval sigma)) = 0#1
      rw [bv1_ne_one.mp hlive0]
      generalize (Expr.and (Hw.revSel E).clsOk
        (Hw.kIsMem (Hw.revSel E).kindW)).eval sigma = q
      exact (by decide : ∀ q : BitVec 1,
        ~~~(~~~(0#1)) &&& ~~~(~~~q) = 0#1) q
    have hin : Inert sigma := Inert.of_failed_rev sigma E hret hif hdrop
      hrev hcall hreturn hbad hnew
    refine retire_err_common_mem m hwfm hfit sigma hsync hifv hcl hin
      hmapz hunmapz hswz (hcoremem_of_revOk_zero (hbad E rfl)) E rfl
      Errno.staleHandle.toWord ?_ ?_
    · intro acc
      rw [hsel acc, if_pos (show (Expr.not (Hw.revSel E).live).eval
        sigma = 1#1 from by
          show ~~~((Hw.revSel E).live.eval sigma) = 1#1
          rw [bv1_ne_one.mp hlive0]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, Machines.Lnp64u.Isa.capLive, SpecM.setReg, hRD, hlcN]
      rfl
  case pos =>
    have hliv1 : (Hw.revSel E).live.eval sigma = 1#1 := hlivE.mpr hlv
    let S : Slot := finOfBv (by decide) (HWv.extractLsb' 0 4)
    let e : CapEntry :=
      { kind := Hw.decKind (sigma.regs (Hw.dcapKind E S) 32)
        lineage := if sigma.regs (Hw.dcapLinV E S) 1 = 1#1 then
          some (finOfBv (by decide) (sigma.regs (Hw.dcapLin E S) 4))
        else none }
    have hcap : ((Hw.abs sigma).doms E).caps S = some e := by
      change (if sigma.regs (Hw.dcapV E S) 1 = 1#1 then some e else none) =
        some e
      rw [if_pos hlv.1]
    have hlcS : ((revRetireBase m (Hw.abs sigma) E).doms E).liveCap
        (Handle.decode HWv).slot (Handle.decode HWv).gen = some e := by
      change ((({ refillPhase m (Hw.abs sigma) with inflight := none }).setDom
        E (fun ds => { ds with pc := ds.pc + 1 })).doms E).liveCap
          (Handle.decode HWv).slot (Handle.decode HWv).gen = some e
      rw [specLiveCap_bridge, abs_liveCap]
      exact if_pos hlv
    have hcls := capSel_clsOk_iff_some sigma E (Hw.readReg E Hw.rs1E)
      S e hkc hSval hcap
    have hmem := capSel_isMem_iff_some sigma E (Hw.readReg E Hw.rs1E)
      S e hkc hSval hcap
    rw [hR1] at hcls
    by_cases hgood : (Expr.and (Hw.revSel E).clsOk
        (Hw.kIsMem (Hw.revSel E).kindW)).eval sigma = 1#1
    · have hg := (bv1_and_eq_one _ _).mp hgood
      have hclsSpec : (Handle.decode HWv).cls = e.kind.cls := hcls.mp hg.1
      obtain ⟨mb, ml, mp, hkind⟩ := hmem.mp hg.2
      have hkindCls : e.kind.cls = .mem := by rw [hkind]; rfl
      have hwf : Wf (Hw.abs sigma) :=
        (Machines.Lnp64u.wfa_invariant m hwfm (Hw.abs sigma) hsr).1
      have hok : ∀ d : DomainId, d = E →
          (Hw.revOkE d).eval sigma = 1#1 := by
        intro d hd
        subst d
        unfold Hw.revOkE Hw.okOf Hw.revChecks Hw.andAll
        change ~~~(~~~((Hw.revSel E).live.eval sigma)) &&&
          ~~~(~~~((Expr.and (Hw.revSel E).clsOk
            (Hw.kIsMem (Hw.revSel E).kindW)).eval sigma)) = 1#1
        rw [hliv1, hgood]
        decide
      have hkills : ∀ dm sl, (Hw.killedByCoreE dm sl).eval sigma =
          (Hw.revKilled dm sl).eval sigma :=
        killedByCoreE_rev_eval sigma E hret hif hdrop hrev hcall hreturn hok
      let RD : RegId := (operandsOf W).rd
      let tau := revAbstractSuccess m (Hw.abs sigma) E RD (rvRoot sigma)
      have hrd : (Hw.rdE.eval sigma).toNat = RD.val := rfl
      have hspec : corePhase m (refillPhase m (Hw.abs sigma)) = tau := by
        rw [hcore0, hDO]
        simp only [specM_bind, SpecM.get, SpecM.require,
          SpecM.reg,
          Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
          SpecM.modify, specM_pure, hRD, hlcS]
        rw [show decide ((Handle.decode HWv).cls = e.kind.cls) = true from
          decide_eq_true hclsSpec]
        simp only [reduceIte, specM_pure]
        rw [show decide (e.kind.cls = .mem) = true from
          decide_eq_true hkindCls]
        simp only [reduceIte, specM_pure]
        rw [revRetireBase_marks]
        rfl
      have hcoreR : ∀ rn w,
          ((Hw.coreAct m).run sigma ((Hw.refillAct m).run sigma sigma)).regs
              rn w =
            ((Act.seq (.write 1 "if_v" (.lit 0))
              (revSuccessArmA E)).run sigma
                ((Hw.refillAct m).run sigma sigma)).regs rn w := by
        intro rn w
        rw [coreAct_run_retire_eq m sigma _ hifv hcl,
          retireAct_run_regs sigma _ E rfl rn w, hsel]
        rw [if_neg (by
          show ¬(~~~((Hw.revSel E).live.eval sigma) = 1#1)
          rw [hliv1]
          decide), if_neg (by
          show ¬(~~~((Expr.and (Hw.revSel E).clsOk
            (Hw.kIsMem (Hw.revSel E).kindW)).eval sigma) = 1#1)
          rw [hgood]
          decide)]
        rfl
      refine square_retire_kill m hwfm hfit sigma hsync hifv hcl
        (revSuccessArmA E) tau hcoreR (ifv_notin_revSuccessA E) hspec
        ?_ ?_ ?_ ?_ ?_ ?_
      · intro c
        exact absDom_revSuccessA_refill m hwfm hfit sigma hsync hrv hifv
          hopc hcl hwf E RD hrd c
      · intro g
        exact absGate_revSuccessA_refill m hwfm hfit sigma hsync E RD g
      · exact absMover_moverAct_revAbstractSuccess m sigma
          ((Hw.coreAct m).run sigma ((Hw.refillAct m).run sigma sigma)) E RD
          hrv hifv hopc hcl hkills hnew hwf
      · intro a
        apply moverAct_mem_revAbstractSuccess m sigma
          ((Hw.coreAct m).run sigma ((Hw.refillAct m).run sigma sigma)) E RD
          hrv hifv hopc hcl hkills hnew hwf
        · intro ow sa
          exact sAuth_rev_eval m hwfm hfit sigma hsync hrv hifv hopc hcl
            hwf E RD hrd hkills hmapz hunmapz ow sa
        · intro b
          exact coreAct_mem_revAbstractSuccess m hwfm hfit sigma hsync hrv
            hifv hopc hcl hwf E RD hrd hifsel hifexcl hrev (hok E rfl)
            hkills hmapz hunmapz b
        · intro job habs hlive sc
          rw [srcWord_quiescent sigma hswz sc]
          exact (revAbstractSuccess_mem_of_surviving_job m sigma E RD job
            habs hlive (sc.eval sigma)).symm
      · rw [← hspec, corePhase_cycle, refillPhase_cycle]
        rfl
      · rw [← hspec, hcore0, Machines.Lnp64u.Wip.retire_inflight]
    · have hbadE : (Expr.not (Expr.and (Hw.revSel E).clsOk
          (Hw.kIsMem (Hw.revSel E).kindW))).eval sigma = 1#1 := by
        show ~~~((Expr.and (Hw.revSel E).clsOk
          (Hw.kIsMem (Hw.revSel E).kindW)).eval sigma) = 1#1
        rw [bv1_ne_one.mp hgood]
        decide
      have hbad : ∀ d : DomainId, d = E →
          (Hw.revOkE d).eval sigma = 0#1 := by
        intro d hd
        subst d
        unfold Hw.revOkE Hw.okOf Hw.revChecks Hw.andAll
        change ~~~(~~~((Hw.revSel E).live.eval sigma)) &&&
          ~~~(~~~((Expr.and (Hw.revSel E).clsOk
            (Hw.kIsMem (Hw.revSel E).kindW)).eval sigma)) = 0#1
        rw [hliv1]
        rw [bv1_ne_one.mp hgood]
        decide
      have hin : Inert sigma := Inert.of_failed_rev sigma E hret hif hdrop
        hrev hcall hreturn hbad hnew
      refine retire_err_common_mem m hwfm hfit sigma hsync hifv hcl hin
        hmapz hunmapz hswz (hcoremem_of_revOk_zero (hbad E rfl)) E rfl
        Errno.badCap.toWord ?_ ?_
      · intro acc
        rw [hsel acc, if_neg (by
          show ¬(~~~((Hw.revSel E).live.eval sigma) = 1#1)
          rw [hliv1]
          decide), if_pos hbadE]
        rfl
      · rw [hcore0, hDO]
        simp only [specM_bind, SpecM.get, SpecM.require,
          SpecM.reg,
          Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
          SpecM.modify, specM_pure, hRD, hlcS]
        by_cases hc : (Handle.decode HWv).cls = e.kind.cls
        · rw [show decide ((Handle.decode HWv).cls = e.kind.cls) = true from
            decide_eq_true hc]
          simp only [reduceIte, specM_pure]
          have hcls1 : (Hw.revSel E).clsOk.eval sigma = 1#1 := hcls.mpr hc
          have hmem0 : ¬((Hw.kIsMem (Hw.revSel E).kindW).eval sigma =
              1#1) := by
            intro hm
            exact hgood ((bv1_and_eq_one _ _).mpr ⟨hcls1, hm⟩)
          have hnmem : ¬(∃ mb ml mp, e.kind = .mem mb ml mp) := by
            intro hm
            exact hmem0 (hmem.mpr hm)
          cases hk : e.kind with
          | mem mb ml mp => exact absurd ⟨mb, ml, mp, hk⟩ hnmem
          | gate g =>
              have hgm : ¬(CapKind.gate g).cls = CapClass.mem := by
                simp [CapKind.cls]
              rw [show decide ((CapKind.gate g).cls = CapClass.mem) = false
                from decide_eq_false hgm]
              rfl
        · rw [show decide ((Handle.decode HWv).cls = e.kind.cls) = false
            from decide_eq_false hc]
          rfl

end Machines.Lnp64u.Theorems.RMC
