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

/-- Predicate-general form of the successful sweeping-operation memory
commit.  Unlike the older one-slot specialization, this accommodates
`cap_revoke`'s arbitrary finite mark set. -/
theorem coreAct_mem_sweep_success_pred (m : Manifest) (sigma : Loom.Hw.St)
    (okE : Expr 1) (killed : Expr 2 → Expr 4 → Expr 1)
    (circ : Hw.OpCirc) (killJob : MoverJob → Prop)
    [DecidablePred killJob]
    (base target : MachineState)
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2)
    (hport :
      ((((List.finRange numDomains).foldr
        (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
          let (en_d, ad_d, da_d) := Hw.retireMemFor d
          let g := Expr.and (Hw.ifDomIs d) en_d
          (.or g acc'.1, .mux g ad_d acc'.2.1,
            .mux g da_d acc'.2.2))
        ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
          (.lit 0 : Expr 32))).1).eval sigma = circ.memEn.eval sigma) ∧
        (circ.memEn.eval sigma = 1#1 →
          ((((List.finRange numDomains).foldr
            (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
              let (en_d, ad_d, da_d) := Hw.retireMemFor d
              let g := Expr.and (Hw.ifDomIs d) en_d
              (.or g acc'.1, .mux g ad_d acc'.2.1,
                .mux g da_d acc'.2.2))
            ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
              (.lit 0 : Expr 32))).2.1).eval sigma =
              circ.memAddr.eval sigma) ∧
           ((((List.finRange numDomains).foldr
            (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
              let (en_d, ad_d, da_d) := Hw.retireMemFor d
              let g := Expr.and (Hw.ifDomIs d) en_d
              (.or g acc'.1, .mux g ad_d acc'.2.1,
                .mux g da_d acc'.2.2))
            ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
              (.lit 0 : Expr 32))).2.2).eval sigma =
              circ.memData.eval sigma)))
    (henShape : circ.memEn = Hw.andAll
      [okE, Hw.movKilledE killed, Hw.statusAuthE killed])
    (haddrShape : circ.memAddr = .reg 12 "mov_status")
    (hdataShape : circ.memData = .lit Errno.staleHandle.toWord)
    (hok : okE.eval sigma = 1#1)
    (hkilled : ((Hw.movKilledE killed).eval sigma = 1#1) ↔
      match Hw.absMover sigma with
      | none => False
      | some job => killJob job)
    (hauth : ∀ job, Hw.absMover sigma = some job →
      (((Hw.statusAuthE killed).eval sigma = 1#1) ↔
        base.domCovers job.owner job.statusAddr
          { r := false, w := true, x := false } = true))
    (hbase : ∀ b : Addr, base.mem b = sigma.mems "mem" b.toNat 32)
    (htarget : ∀ b : Addr, target.mem b =
      match Hw.absMover sigma with
      | none => base.mem b
      | some job =>
          if killJob job then
            if base.domCovers job.owner job.statusAddr
                { r := false, w := true, x := false } then
              if b = job.statusAddr then Errno.staleHandle.toWord
              else base.mem b
            else base.mem b
          else base.mem b)
    (b : Addr) :
    ((Hw.coreAct m).run sigma ((Hw.refillAct m).run sigma sigma)).mems
        "mem" b.toNat 32 = target.mem b := by
  rw [coreAct_run_retire_eq m sigma _ hifv hcl,
    retireAct_run_mems sigma _ b.toNat 32]
  simp only [Act.run]
  rw [hport.1]
  change _ = target.mem b
  rw [htarget b]
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
    rw [habs]
    simp only
    have hauth' : ((Hw.statusAuthE killed).eval sigma = 1#1) ↔
        base.domCovers job.owner job.statusAddr
          { r := false, w := true, x := false } = true := hauth job habs
    have hen : (circ.memEn.eval sigma = 1#1) ↔
        (killJob job ∧ base.domCovers job.owner job.statusAddr
          { r := false, w := true, x := false } = true) := by
      rw [henShape, andAll_eval]
      simp only [List.forall_mem_cons, List.not_mem_nil]
      rw [hok, hkilled, habs, hauth']
      simp
    by_cases hk : killJob job
    · rw [if_pos hk]
      by_cases ha : base.domCovers job.owner job.statusAddr
          { r := false, w := true, x := false } = true
      · have he : circ.memEn.eval sigma = 1#1 := hen.mpr ⟨hk, ha⟩
        rw [if_pos ha, if_pos he]
        obtain ⟨had, hda⟩ := hport.2 he
        rw [had, hda, haddrShape, hdataShape]
        by_cases hb : b = job.statusAddr
        · subst b
          simp only [MemEnv.set]
          simp [Expr.eval, job]
        · have hbn : b.toNat ≠ job.statusAddr.toNat :=
            fun h => hb (BitVec.eq_of_toNat_eq h)
          simp only [MemEnv.set]
          rw [if_neg (fun h => hbn h.2),
            refill_pres_mem m sigma "mem" b.toNat 32]
          rw [if_neg hb, hbase]
      · have he : ¬(circ.memEn.eval sigma = 1#1) :=
          fun h => ha (hen.mp h).2
        rw [if_neg ha, if_neg he,
          refill_pres_mem m sigma "mem" b.toNat 32]
        exact (hbase b).symm
    · have he : ¬(circ.memEn.eval sigma = 1#1) :=
        fun h => hk (hen.mp h).1
      rw [if_neg hk, if_neg he,
        refill_pres_mem m sigma "mem" b.toNat 32]
      exact (hbase b).symm
  · have habs : Hw.absMover sigma = none := absMover_none sigma hv
    rw [habs]
    simp only
    have he : ¬(circ.memEn.eval sigma = 1#1) := by
      intro h
      have hm : (Hw.movKilledE killed).eval sigma = 1#1 := by
        rw [henShape] at h
        exact (andAll_eval sigma _).mp h _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      simpa [habs] using hkilled.mp hm
    rw [if_neg he, refill_pres_mem m sigma "mem" b.toNat 32]
    exact (hbase b).symm

private theorem revNewJobAny_zero (sigma : Loom.Hw.St)
    (hnew : forall d : DomainId, (Hw.newJobSet d).eval sigma = 0#1) :
    (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet)).eval sigma = 0#1 := by
  apply orAll_zero
  intro e he
  obtain ⟨d, -, rfl⟩ := List.mem_map.mp he
  rw [hnew d]
  decide

/-- `revKilled` applied to the domain/slot fields of a packed reference is
exactly the converged abstract mark bit for that decoded reference. -/
theorem revKilled_ref_eval (sigma : Loom.Hw.St) (hrv : RvSync sigma)
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hopc : (sigma.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2) (refE : Expr 14) :
    ((Hw.revKilled (Hw.field refE 12 2) (Hw.field refE 8 4)).eval sigma =
        1#1) <->
      (Hw.abs sigma).marks (rvRoot sigma)
        (Hw.decRef (refE.eval sigma)).dom
        (Hw.decRef (refE.eval sigma)).slot = true := by
  rw [revKilled_eval sigma hrv hifv hopc hcl]
  congr 2 <;> rfl

/-- The revoke-specific Mover kill guard fires exactly when a live encoded
job has a marked source or destination slot. -/
theorem movKilledE_rev_iff (sigma : Loom.Hw.St) (hrv : RvSync sigma)
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hopc : (sigma.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2) :
    ((Hw.movKilledE Hw.revKilled).eval sigma = 1#1) <->
      match Hw.absMover sigma with
      | none => False
      | some job =>
          (Hw.abs sigma).marks (rvRoot sigma) job.src.dom job.src.slot = true \/
          (Hw.abs sigma).marks (rvRoot sigma) job.dst.dom job.dst.slot = true := by
  unfold Hw.movKilledE
  change (sigma.regs "mov_v" 1 &&&
    ((Hw.revKilled Hw.movSrcDom Hw.movSrcSlot).eval sigma |||
      (Hw.revKilled Hw.movDstDom Hw.movDstSlot).eval sigma) = 1#1) <-> _
  by_cases hv : sigma.regs "mov_v" 1 = 1#1
  · rw [absMover_some sigma hv, bv1_and_eq_one, bv1_or_eq_one]
    simp only [Hw.movSrcDom, Hw.movSrcSlot, Hw.movDstDom, Hw.movDstSlot]
    rw [
      revKilled_ref_eval sigma hrv hifv hopc hcl (.reg 14 "mov_src"),
      revKilled_ref_eval sigma hrv hifv hopc hcl (.reg 14 "mov_dst")]
    simp [hv]
    rfl
  · have hv0 : sigma.regs "mov_v" 1 = 0#1 := bv1_ne_one.mp hv
    simp [absMover_none sigma hv, hv0]

/-- On a successful retiring `cap_revoke`, the global core kill tree is
exactly the revoke mark lookup. -/
theorem killedByCoreE_rev_eval (sigma : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval sigma = 1#1)
    (hif : forall d : DomainId, (Hw.ifDomIs d).eval sigma =
      if d = E then 1#1 else 0#1)
    (hdrop : (Hw.isMn "cap_drop").eval sigma ≠ 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval sigma = 1#1)
    (hcall : (Hw.isMn "gate_call").eval sigma ≠ 1#1)
    (hreturn : (Hw.isMn "gate_return").eval sigma ≠ 1#1)
    (hok : forall d : DomainId, d = E -> (Hw.revOkE d).eval sigma = 1#1)
    (dm : Expr 2) (sl : Expr 4) :
    (Hw.killedByCoreE dm sl).eval sigma = (Hw.revKilled dm sl).eval sigma := by
  have hdrop0 : (Hw.isMn "cap_drop").eval sigma = 0#1 := bv1_ne_one.mp hdrop
  have hcall0 : (Hw.isMn "gate_call").eval sigma = 0#1 := bv1_ne_one.mp hcall
  have hreturn0 : (Hw.isMn "gate_return").eval sigma = 0#1 :=
    bv1_ne_one.mp hreturn
  have honeAnd : forall x : BitVec 1, 1#1 &&& x = x := by decide
  have hzeroAnd : forall x : BitVec 1, 0#1 &&& x = 0#1 := by decide
  have hzeroOr : forall x : BitVec 1, 0#1 ||| x = x := by decide
  have horZero : forall x : BitVec 1, x ||| 0#1 = x := by decide
  unfold Hw.killedByCoreE
  fin_cases E <;>
    simp [Hw.orAll, List.finRange, Expr.eval, Fin.ext_iff, hret, hif,
      hdrop0, hrev, hok, hcall0, hreturn0, honeAnd, hzeroAnd, hzeroOr,
      horZero] <;>
    congr 2

/-- The global Mover kill guard reduces to marked endpoints once the
successful revoke branch is selected in `killedByCoreE`. -/
theorem movKilledE_core_rev_iff (sigma : Loom.Hw.St) (hrv : RvSync sigma)
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hopc : (sigma.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2)
    (hkills : forall dm sl, (Hw.killedByCoreE dm sl).eval sigma =
      (Hw.revKilled dm sl).eval sigma) :
    ((Hw.movKilledE (fun dm sl => Hw.killedByCoreE dm sl)).eval sigma =
        1#1) <->
      match Hw.absMover sigma with
      | none => False
      | some job =>
          (Hw.abs sigma).marks (rvRoot sigma) job.src.dom job.src.slot = true \/
          (Hw.abs sigma).marks (rvRoot sigma) job.dst.dom job.dst.slot = true := by
  unfold Hw.movKilledE
  change (sigma.regs "mov_v" 1 &&&
    ((Hw.killedByCoreE Hw.movSrcDom Hw.movSrcSlot).eval sigma |||
      (Hw.killedByCoreE Hw.movDstDom Hw.movDstSlot).eval sigma) = 1#1) <-> _
  rw [hkills Hw.movSrcDom Hw.movSrcSlot,
    hkills Hw.movDstDom Hw.movDstSlot]
  exact movKilledE_rev_iff sigma hrv hifv hopc hcl

/-- A packed unmarked reference is silent in the selected global revoke
kill tree. -/
theorem killedByCoreE_rev_ref_zero (sigma : Loom.Hw.St) (hrv : RvSync sigma)
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hopc : (sigma.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2)
    (hkills : forall dm sl, (Hw.killedByCoreE dm sl).eval sigma =
      (Hw.revKilled dm sl).eval sigma)
    (refE : Expr 14)
    (hunmarked : (Hw.abs sigma).marks (rvRoot sigma)
      (Hw.decRef (refE.eval sigma)).dom
      (Hw.decRef (refE.eval sigma)).slot = false) :
    (Hw.killedByCoreE (Hw.field refE 12 2)
      (Hw.field refE 8 4)).eval sigma = 0#1 := by
  rw [hkills]
  apply bv1_ne_one.mp
  intro hkill
  have hm := (revKilled_ref_eval sigma hrv hifv hopc hcl refE).mp hkill
  rw [hunmarked] at hm
  contradiction

/-- `destroyMarked` preserves the complete live-capability lookup at an
unmarked slot, for any queried generation. -/
theorem destroyMarked_liveCap_eq_of_unmarked (rho : MachineState)
    (marked : DomainId -> Slot -> Bool) (d : DomainId) (s : Slot) (g : Gen)
    (hm : marked d s = false) :
    (((rho.destroyMarked marked).doms d).liveCap s g) =
      ((rho.doms d).liveCap s g) := by
  unfold DomainState.liveCap
  rw [destroyMarked_caps, destroyMarked_slotGen]
  simp [hm]

/-- For a reference live before destruction, post-destruction liveness is
equivalent to its slot being unmarked. -/
theorem destroyMarked_liveRef_true_iff_of_live (rho : MachineState)
    (marked : DomainId -> Slot -> Bool) (r : CapRef)
    (hlive : rho.liveRef r = true) :
    (rho.destroyMarked marked).liveRef r = true <->
      marked r.dom r.slot = false := by
  by_cases hm : marked r.dom r.slot = true
  · have hmfalse : (rho.destroyMarked marked).liveRef r = false :=
      (destroyMarked_liveRef_false_iff_of_live rho marked r hlive).mpr hm
    simp [hm, hmfalse]
  · have hm0 := Bool.eq_false_of_not_eq_true hm
    unfold MachineState.liveRef at hlive ⊢
    rw [destroyMarked_liveCap_eq_of_unmarked rho marked r.dom r.slot r.gen hm0]
    simp [hlive, hm0]

/-- Under well-formedness, the selected global revoke guard is equivalent
to at least one Mover endpoint being dead in the post-destruction state. -/
theorem movKilledE_core_rev_endpoint_iff (sigma : Loom.Hw.St)
    (tau : MachineState) (hrv : RvSync sigma)
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hopc : (sigma.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2)
    (hkills : forall dm sl, (Hw.killedByCoreE dm sl).eval sigma =
      (Hw.revKilled dm sl).eval sigma)
    (hwf : Wf (Hw.abs sigma))
    (htauLive : forall r, tau.liveRef r =
      ((Hw.abs sigma).destroyMarked
        ((Hw.abs sigma).marks (rvRoot sigma))).liveRef r)
    (job : MoverJob) (habs : Hw.absMover sigma = some job) :
    ((Hw.movKilledE (fun dm sl => Hw.killedByCoreE dm sl)).eval sigma =
        1#1) <->
      (tau.liveRef job.src && tau.liveRef job.dst) = false := by
  have hmove : (Hw.abs sigma).mover = some job := habs
  have hlive := moverEndpoints_live hwf job hmove
  have hsrc : tau.liveRef job.src = false <->
      (Hw.abs sigma).marks (rvRoot sigma) job.src.dom job.src.slot = true := by
    rw [htauLive]
    exact destroyMarked_liveRef_false_iff_of_live (Hw.abs sigma)
      ((Hw.abs sigma).marks (rvRoot sigma)) job.src hlive.1
  have hdst : tau.liveRef job.dst = false <->
      (Hw.abs sigma).marks (rvRoot sigma) job.dst.dom job.dst.slot = true := by
    rw [htauLive]
    exact destroyMarked_liveRef_false_iff_of_live (Hw.abs sigma)
      ((Hw.abs sigma).marks (rvRoot sigma)) job.dst hlive.2
  rw [movKilledE_core_rev_iff sigma hrv hifv hopc hcl hkills, habs,
    Bool.and_eq_false_iff, hsrc, hdst]

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
