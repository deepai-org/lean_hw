-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireRevMover

/-!
# R-MC retirement: revoke Mover specialization

Instantiation of the arbitrary endpoint-sweep bridge with the converged
`cap_revoke` mark set.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

/-- Revoke specialization of the generic endpoint-sweep Mover-field bridge.
The caller supplies only the post-core liveness/kind faces and the exact
kernel `sweepMover` job face. -/
theorem absMover_moverAct_revoke (sigma acc : Loom.Hw.St)
    (tau : MachineState) (hrv : RvSync sigma)
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hopc : (sigma.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2)
    (hkills : forall dm sl, (Hw.killedByCoreE dm sl).eval sigma =
      (Hw.revKilled dm sl).eval sigma)
    (hnew : forall d : DomainId, (Hw.newJobSet d).eval sigma = 0#1)
    (hwf : Wf (Hw.abs sigma))
    (htauLive : forall r, tau.liveRef r =
      ((Hw.abs sigma).destroyMarked
        ((Hw.abs sigma).marks (rvRoot sigma))).liveRef r)
    (htauKind : forall d s g, Option.map CapEntry.kind
        ((tau.doms d).liveCap s g) =
      Option.map CapEntry.kind
        ((((Hw.abs sigma).destroyMarked
          ((Hw.abs sigma).marks (rvRoot sigma))).doms d).liveCap s g))
    (hjob : tau.mover =
      match Hw.absMover sigma with
      | none => none
      | some job =>
          if tau.liveRef job.src && tau.liveRef job.dst then some job else none) :
    Hw.absMover (Hw.moverAct.run sigma acc) = (moverPhase tau).mover := by
  let marked := (Hw.abs sigma).marks (rvRoot sigma)
  have endpointLive (job : MoverJob) (habs : Hw.absMover sigma = some job) :
      (Hw.abs sigma).liveRef job.src = true /\
      (Hw.abs sigma).liveRef job.dst = true := by
    exact moverEndpoints_live hwf job habs
  have unmarkedSrc (job : MoverJob) (habs : Hw.absMover sigma = some job)
      (hlive : (tau.liveRef job.src && tau.liveRef job.dst) = true) :
      marked job.src.dom job.src.slot = false := by
    have ht := (Bool.and_eq_true_iff.mp hlive).1
    have hi := destroyMarked_liveRef_true_iff_of_live (Hw.abs sigma)
      marked job.src (endpointLive job habs).1
    exact hi.mp ((htauLive job.src).symm.trans ht)
  have unmarkedDst (job : MoverJob) (habs : Hw.absMover sigma = some job)
      (hlive : (tau.liveRef job.src && tau.liveRef job.dst) = true) :
      marked job.dst.dom job.dst.slot = false := by
    have ht := (Bool.and_eq_true_iff.mp hlive).2
    have hi := destroyMarked_liveRef_true_iff_of_live (Hw.abs sigma)
      marked job.dst (endpointLive job habs).2
    exact hi.mp ((htauLive job.dst).symm.trans ht)
  apply absMover_moverAct_endpointSweep sigma acc tau hnew hjob
  · intro job habs
    exact movKilledE_core_rev_endpoint_iff sigma tau hrv hifv hopc hcl
      hkills hwf htauLive job habs
  · intro job habs hlive refE href
    have hv : sigma.regs "mov_v" 1 = 1#1 := by
      by_contra hn
      rw [absMover_none sigma hn] at habs
      contradiction
    have hcanon := Option.some.inj ((absMover_some sigma hv).symm.trans habs)
    have href' : Hw.decRef (refE.eval sigma) = job.src := by
      rw [href]
      exact congrArg MoverJob.src hcanon
    apply killedByCoreE_rev_ref_zero sigma hrv hifv hopc hcl hkills refE
    simpa [marked, href'] using unmarkedSrc job habs hlive
  · intro job habs hlive refE href
    have hv : sigma.regs "mov_v" 1 = 1#1 := by
      by_contra hn
      rw [absMover_none sigma hn] at habs
      contradiction
    have hcanon := Option.some.inj ((absMover_some sigma hv).symm.trans habs)
    have href' : Hw.decRef (refE.eval sigma) = job.dst := by
      rw [href]
      exact congrArg MoverJob.dst hcanon
    apply killedByCoreE_rev_ref_zero sigma hrv hifv hopc hcl hkills refE
    simpa [marked, href'] using unmarkedDst job habs hlive
  · intro job habs hlive
    rw [htauKind, destroyMarked_liveCap_eq_of_unmarked]
    exact unmarkedSrc job habs hlive
  · intro job habs hlive
    rw [htauKind, destroyMarked_liveCap_eq_of_unmarked]
    exact unmarkedDst job habs hlive

/-- Memory counterpart of `absMover_moverAct_revoke`. -/
theorem moverAct_mem_revoke (sigma acc : Loom.Hw.St)
    (tau : MachineState) (hrv : RvSync sigma)
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hopc : (sigma.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2)
    (hkills : forall dm sl, (Hw.killedByCoreE dm sl).eval sigma =
      (Hw.revKilled dm sl).eval sigma)
    (hnew : forall d : DomainId, (Hw.newJobSet d).eval sigma = 0#1)
    (hwf : Wf (Hw.abs sigma))
    (htauLive : forall r, tau.liveRef r =
      ((Hw.abs sigma).destroyMarked
        ((Hw.abs sigma).marks (rvRoot sigma))).liveRef r)
    (htauKind : forall d s g, Option.map CapEntry.kind
        ((tau.doms d).liveCap s g) =
      Option.map CapEntry.kind
        ((((Hw.abs sigma).destroyMarked
          ((Hw.abs sigma).marks (rvRoot sigma))).doms d).liveCap s g))
    (hjob : tau.mover =
      match Hw.absMover sigma with
      | none => none
      | some job =>
          if tau.liveRef job.src && tau.liveRef job.dst then some job else none)
    (hauth : forall (ow : Expr 2) (sa : Expr 12),
      ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
          (List.finRange numRegions).map fun r =>
            Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
              Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
                { r := false, w := true, x := false }])).eval sigma = 1#1) <->
        tau.domCovers (finOfBv (by decide) (ow.eval sigma)) (sa.eval sigma)
          { r := false, w := true, x := false } = true)
    (hmem : forall b : Addr, acc.mems "mem" b.toNat 32 = tau.mem b)
    (hsw : forall job, Hw.absMover sigma = some job ->
      (tau.liveRef job.src && tau.liveRef job.dst) = true ->
      forall sc : Expr 12, Expr.eval sigma
        (((List.finRange numDomains).foldr
          (fun d acc' =>
            Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
                Hw.domCoversE d
                  (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                  { r := false, w := true, x := false },
                .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12) sc])
              (Hw.readReg d Hw.rs2E) acc')
          (.memRead 32 "mem" sc))) = tau.mem (sc.eval sigma))
    (a : Addr) :
    (Hw.moverAct.run sigma acc).mems "mem" a.toNat 32 =
      (moverPhase tau).mem a := by
  let marked := (Hw.abs sigma).marks (rvRoot sigma)
  have endpointLive (job : MoverJob) (habs : Hw.absMover sigma = some job) :
      (Hw.abs sigma).liveRef job.src = true /\
      (Hw.abs sigma).liveRef job.dst = true := by
    exact moverEndpoints_live hwf job habs
  have unmarkedSrc (job : MoverJob) (habs : Hw.absMover sigma = some job)
      (hlive : (tau.liveRef job.src && tau.liveRef job.dst) = true) :
      marked job.src.dom job.src.slot = false := by
    have ht := (Bool.and_eq_true_iff.mp hlive).1
    have hi := destroyMarked_liveRef_true_iff_of_live (Hw.abs sigma)
      marked job.src (endpointLive job habs).1
    exact hi.mp ((htauLive job.src).symm.trans ht)
  have unmarkedDst (job : MoverJob) (habs : Hw.absMover sigma = some job)
      (hlive : (tau.liveRef job.src && tau.liveRef job.dst) = true) :
      marked job.dst.dom job.dst.slot = false := by
    have ht := (Bool.and_eq_true_iff.mp hlive).2
    have hi := destroyMarked_liveRef_true_iff_of_live (Hw.abs sigma)
      marked job.dst (endpointLive job habs).2
    exact hi.mp ((htauLive job.dst).symm.trans ht)
  apply moverAct_mem_endpointSweep sigma acc tau hnew hjob
  · intro job habs
    exact movKilledE_core_rev_endpoint_iff sigma tau hrv hifv hopc hcl
      hkills hwf htauLive job habs
  · intro job habs hlive refE href
    have hv : sigma.regs "mov_v" 1 = 1#1 := by
      by_contra hn
      rw [absMover_none sigma hn] at habs
      contradiction
    have hcanon := Option.some.inj ((absMover_some sigma hv).symm.trans habs)
    have href' : Hw.decRef (refE.eval sigma) = job.src := by
      rw [href]
      exact congrArg MoverJob.src hcanon
    apply killedByCoreE_rev_ref_zero sigma hrv hifv hopc hcl hkills refE
    simpa [marked, href'] using unmarkedSrc job habs hlive
  · intro job habs hlive refE href
    have hv : sigma.regs "mov_v" 1 = 1#1 := by
      by_contra hn
      rw [absMover_none sigma hn] at habs
      contradiction
    have hcanon := Option.some.inj ((absMover_some sigma hv).symm.trans habs)
    have href' : Hw.decRef (refE.eval sigma) = job.dst := by
      rw [href]
      exact congrArg MoverJob.dst hcanon
    apply killedByCoreE_rev_ref_zero sigma hrv hifv hopc hcl hkills refE
    simpa [marked, href'] using unmarkedDst job habs hlive
  · intro job habs hlive
    rw [htauKind, destroyMarked_liveCap_eq_of_unmarked]
    exact unmarkedSrc job habs hlive
  · intro job habs hlive
    rw [htauKind, destroyMarked_liveCap_eq_of_unmarked]
    exact unmarkedDst job habs hlive
  · exact hauth
  · exact hmem
  · exact hsw

end Machines.Lnp64u.Theorems.RMC
