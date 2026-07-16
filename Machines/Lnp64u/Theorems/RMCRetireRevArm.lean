-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireRevState
import Machines.Lnp64u.Theorems.RMCRetireGateCallSuccess

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

end Machines.Lnp64u.Theorems.RMC
