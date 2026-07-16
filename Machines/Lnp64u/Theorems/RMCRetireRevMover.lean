-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireRev

/-!
# R-MC retirement: mark-set Mover bridge

The drop/gate retirement proofs specialize Mover killing to one transferred
slot.  Revoke kills an arbitrary finite mark set, so this file factors the
common proof around the semantic endpoint-survival test instead.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

private theorem revNewJobAny_zero (sigma : Loom.Hw.St)
    (hnew : forall d : DomainId, (Hw.newJobSet d).eval sigma = 0#1) :
    (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet)).eval sigma = 0#1 := by
  apply orAll_zero
  intro e he
  obtain ⟨d, -, rfl⟩ := List.mem_map.mp he
  rw [hnew d]
  decide

/-- Generic Mover-field correspondence for a core operation whose kill set
is characterized by post-core endpoint liveness. -/
theorem absMover_moverAct_endpointSweep (sigma acc : Loom.Hw.St)
    (tau : MachineState)
    (hnew : forall d : DomainId, (Hw.newJobSet d).eval sigma = 0#1)
    (hjob : tau.mover =
      match Hw.absMover sigma with
      | none => none
      | some job =>
          if tau.liveRef job.src && tau.liveRef job.dst then some job else none)
    (hguard : forall job, Hw.absMover sigma = some job ->
      ((Hw.movKilledE (fun dm sl => Hw.killedByCoreE dm sl)).eval sigma =
          1#1 <->
        (tau.liveRef job.src && tau.liveRef job.dst) = false))
    (hkillS : forall job, Hw.absMover sigma = some job ->
      (tau.liveRef job.src && tau.liveRef job.dst) = true ->
      forall e : Expr 14, e.eval sigma = sigma.regs "mov_src" 14 ->
        (Hw.killedByCoreE (Hw.field e 12 2)
          (Hw.field e 8 4)).eval sigma = 0#1)
    (hkillD : forall job, Hw.absMover sigma = some job ->
      (tau.liveRef job.src && tau.liveRef job.dst) = true ->
      forall e : Expr 14, e.eval sigma = sigma.regs "mov_dst" 14 ->
        (Hw.killedByCoreE (Hw.field e 12 2)
          (Hw.field e 8 4)).eval sigma = 0#1)
    (hkindS : forall job, Hw.absMover sigma = some job ->
      (tau.liveRef job.src && tau.liveRef job.dst) = true ->
      Option.map CapEntry.kind
          ((tau.doms job.src.dom).liveCap job.src.slot job.src.gen) =
        Option.map CapEntry.kind
          (((Hw.abs sigma).doms job.src.dom).liveCap
            job.src.slot job.src.gen))
    (hkindD : forall job, Hw.absMover sigma = some job ->
      (tau.liveRef job.src && tau.liveRef job.dst) = true ->
      Option.map CapEntry.kind
          ((tau.doms job.dst.dom).liveCap job.dst.slot job.dst.gen) =
        Option.map CapEntry.kind
          (((Hw.abs sigma).doms job.dst.dom).liveCap
            job.dst.slot job.dst.gen)) :
    Hw.absMover (Hw.moverAct.run sigma acc) = (moverPhase tau).mover := by
  by_cases hv : sigma.regs "mov_v" 1 = 1#1
  · let job : MoverJob :=
      { owner := finOfBv (by decide) (sigma.regs "mov_owner" 2)
        src := Hw.decRef (sigma.regs "mov_src" 14)
        dst := Hw.decRef (sigma.regs "mov_dst" 14)
        srcCur := sigma.regs "mov_srccur" 12
        dstCur := sigma.regs "mov_dstcur" 12
        remaining := (sigma.regs "mov_rem" 13).toNat
        statusAddr := sigma.regs "mov_status" 12 }
    have habs : Hw.absMover sigma = some job := absMover_some sigma hv
    by_cases hlive : (tau.liveRef job.src && tau.liveRef job.dst) = true
    · have hguard0 :
          (Hw.movKilledE (fun dm sl => Hw.killedByCoreE dm sl)).eval sigma =
            0#1 := bv1_ne_one.mp (by
          intro hk
          have hdead := (hguard job habs).mp hk
          rw [hlive] at hdead
          contradiction)
      have hnewAny := revNewJobAny_zero sigma hnew
      have htau : tau.mover = some job := by
        rw [hjob, habs]
        simp [hlive]
      have hjobV : (Expr.or
          (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet))
          (.and (.reg 1 "mov_v")
            (.not (.and (.reg 1 "mov_v")
              (.or (Hw.killedByCoreE Hw.movSrcDom Hw.movSrcSlot)
                   (Hw.killedByCoreE Hw.movDstDom Hw.movDstSlot)))))).eval sigma =
          1#1 := by
        show (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet)).eval sigma |||
          (sigma.regs "mov_v" 1 &&& ~~~((Hw.movKilledE
            (fun dm sl => Hw.killedByCoreE dm sl)).eval sigma)) = 1#1
        rw [hnewAny, hv, hguard0]
        decide
      exact absMover_moverAct_run sigma acc tau
        (sigma.regs "mov_src" 14) (sigma.regs "mov_dst" 14)
        (sigma.regs "mov_owner" 2) (sigma.regs "mov_srccur" 12)
        (sigma.regs "mov_dstcur" 12) (sigma.regs "mov_status" 12)
        (sigma.regs "mov_rem" 13)
        (hkillS job habs hlive) (hkillD job habs hlive)
        (by simpa [job] using hkindS job habs hlive)
        (by simpa [job] using hkindD job habs hlive)
        hjobV
        (postJ_noNew sigma hnew _ _) (postJ_noNew sigma hnew _ _)
        (postJ_noNew sigma hnew _ _) (postJ_noNew sigma hnew _ _)
        (postJ_noNew sigma hnew _ _) (postJ_noNew sigma hnew _ _)
        (postJ_noNew sigma hnew _ _)
        (by simpa [job] using htau)
    · have hlive0 : (tau.liveRef job.src && tau.liveRef job.dst) = false :=
        Bool.eq_false_of_not_eq_true hlive
      have hkilled := (hguard job habs).mpr hlive0
      have htau : tau.mover = none := by
        rw [hjob, habs]
        simp [hlive0]
      rw [absMover_moverAct_killed sigma acc hnew hkilled]
      simp [Machines.Lnp64u.moverPhase, htau, hlive0]
  · have hv0 : sigma.regs "mov_v" 1 = 0#1 := bv1_ne_one.mp hv
    have habs : Hw.absMover sigma = none := absMover_none sigma hv
    have htau : tau.mover = none := by rw [hjob, habs]
    rw [absMover_moverAct_nojob sigma acc hnew hv0]
    simp [Machines.Lnp64u.moverPhase, htau]

/-- Memory counterpart of `absMover_moverAct_endpointSweep`. -/
theorem moverAct_mem_endpointSweep (sigma acc : Loom.Hw.St)
    (tau : MachineState)
    (hnew : forall d : DomainId, (Hw.newJobSet d).eval sigma = 0#1)
    (hjob : tau.mover =
      match Hw.absMover sigma with
      | none => none
      | some job =>
          if tau.liveRef job.src && tau.liveRef job.dst then some job else none)
    (hguard : forall job, Hw.absMover sigma = some job ->
      ((Hw.movKilledE (fun dm sl => Hw.killedByCoreE dm sl)).eval sigma =
          1#1 <->
        (tau.liveRef job.src && tau.liveRef job.dst) = false))
    (hkillS : forall job, Hw.absMover sigma = some job ->
      (tau.liveRef job.src && tau.liveRef job.dst) = true ->
      forall e : Expr 14, e.eval sigma = sigma.regs "mov_src" 14 ->
        (Hw.killedByCoreE (Hw.field e 12 2)
          (Hw.field e 8 4)).eval sigma = 0#1)
    (hkillD : forall job, Hw.absMover sigma = some job ->
      (tau.liveRef job.src && tau.liveRef job.dst) = true ->
      forall e : Expr 14, e.eval sigma = sigma.regs "mov_dst" 14 ->
        (Hw.killedByCoreE (Hw.field e 12 2)
          (Hw.field e 8 4)).eval sigma = 0#1)
    (hkindS : forall job, Hw.absMover sigma = some job ->
      (tau.liveRef job.src && tau.liveRef job.dst) = true ->
      Option.map CapEntry.kind
          ((tau.doms job.src.dom).liveCap job.src.slot job.src.gen) =
        Option.map CapEntry.kind
          (((Hw.abs sigma).doms job.src.dom).liveCap
            job.src.slot job.src.gen))
    (hkindD : forall job, Hw.absMover sigma = some job ->
      (tau.liveRef job.src && tau.liveRef job.dst) = true ->
      Option.map CapEntry.kind
          ((tau.doms job.dst.dom).liveCap job.dst.slot job.dst.gen) =
        Option.map CapEntry.kind
          (((Hw.abs sigma).doms job.dst.dom).liveCap
            job.dst.slot job.dst.gen))
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
  by_cases hv : sigma.regs "mov_v" 1 = 1#1
  · let job : MoverJob :=
      { owner := finOfBv (by decide) (sigma.regs "mov_owner" 2)
        src := Hw.decRef (sigma.regs "mov_src" 14)
        dst := Hw.decRef (sigma.regs "mov_dst" 14)
        srcCur := sigma.regs "mov_srccur" 12
        dstCur := sigma.regs "mov_dstcur" 12
        remaining := (sigma.regs "mov_rem" 13).toNat
        statusAddr := sigma.regs "mov_status" 12 }
    have habs : Hw.absMover sigma = some job := absMover_some sigma hv
    by_cases hlive : (tau.liveRef job.src && tau.liveRef job.dst) = true
    · have hguard0 :
          (Hw.movKilledE (fun dm sl => Hw.killedByCoreE dm sl)).eval sigma =
            0#1 := bv1_ne_one.mp (by
          intro hk
          have hdead := (hguard job habs).mp hk
          rw [hlive] at hdead
          contradiction)
      have hnewAny := revNewJobAny_zero sigma hnew
      have htau : tau.mover = some job := by
        rw [hjob, habs]
        simp [hlive]
      have hjobV : (Expr.or
          (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet))
          (.and (.reg 1 "mov_v")
            (.not (.and (.reg 1 "mov_v")
              (.or (Hw.killedByCoreE Hw.movSrcDom Hw.movSrcSlot)
                   (Hw.killedByCoreE Hw.movDstDom Hw.movDstSlot)))))).eval sigma =
          1#1 := by
        show (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet)).eval sigma |||
          (sigma.regs "mov_v" 1 &&& ~~~((Hw.movKilledE
            (fun dm sl => Hw.killedByCoreE dm sl)).eval sigma)) = 1#1
        rw [hnewAny, hv, hguard0]
        decide
      exact moverAct_mem_run sigma acc tau
        (sigma.regs "mov_src" 14) (sigma.regs "mov_dst" 14)
        (sigma.regs "mov_owner" 2) (sigma.regs "mov_srccur" 12)
        (sigma.regs "mov_dstcur" 12) (sigma.regs "mov_status" 12)
        (sigma.regs "mov_rem" 13)
        (hkillS job habs hlive) (hkillD job habs hlive)
        (by simpa [job] using hkindS job habs hlive)
        (by simpa [job] using hkindD job habs hlive)
        hjobV
        (postJ_noNew sigma hnew _ _) (postJ_noNew sigma hnew _ _)
        (postJ_noNew sigma hnew _ _) (postJ_noNew sigma hnew _ _)
        (postJ_noNew sigma hnew _ _) (postJ_noNew sigma hnew _ _)
        (postJ_noNew sigma hnew _ _)
        (by simpa [job] using htau) hauth hmem
        (hsw job habs hlive) a
    · have hlive0 : (tau.liveRef job.src && tau.liveRef job.dst) = false :=
        Bool.eq_false_of_not_eq_true hlive
      have hkilled := (hguard job habs).mpr hlive0
      have htau : tau.mover = none := by
        rw [hjob, habs]
        simp [hlive0]
      rw [moverAct_mem_killed sigma acc hnew hkilled a, hmem a]
      simp [Machines.Lnp64u.moverPhase, htau, hlive0]
  · have hv0 : sigma.regs "mov_v" 1 = 0#1 := bv1_ne_one.mp hv
    have habs : Hw.absMover sigma = none := absMover_none sigma hv
    have htau : tau.mover = none := by rw [hjob, habs]
    rw [moverAct_mem_nojob sigma acc hnew hv0 a, hmem a]
    simp [Machines.Lnp64u.moverPhase, htau]

end Machines.Lnp64u.Theorems.RMC
