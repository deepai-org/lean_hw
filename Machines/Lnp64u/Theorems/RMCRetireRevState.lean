-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireRevMoverSpec

/-!
# R-MC retirement: abstract revoke success state

This module names the successful `cap_revoke` state and records the exact
table, liveness, capability-kind, and Mover faces needed by the retirement
square.  Keeping these facts independent of circuit dispatch makes the final
arm proof substantially smaller.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

/-- The state at which a retiring instruction's ISA body starts: refill has
run, the in-flight instruction has been consumed, and its PC has advanced. -/
def revRetireBase (m : Manifest) (sigma : MachineState) (E : DomainId) :
    MachineState :=
  ({ refillPhase m sigma with inflight := none }).setDom E
    (fun ds => { ds with pc := ds.pc + 1 })

/-- The complete successful abstract `cap_revoke` result, before the outer
machine cycle applies its ordinary Mover phase and cycle tick. -/
def revAbstractSuccess (m : Manifest) (sigma : MachineState)
    (E : DomainId) (RD : RegId) (root : CapRef) : MachineState :=
  ((((revRetireBase m sigma E).destroyMarked
      (sigma.marks root)).sweepRegions).sweepMover).setDom E
        (fun ds => ds.setReg RD 0)

/-- Refill, retirement bookkeeping, and PC advance do not change the
capability tables used by `marks`. -/
theorem revRetireBase_tables (m : Manifest) (sigma : MachineState)
    (E : DomainId) : TablesEq sigma (revRetireBase m sigma E) := by
  refine TablesEq.trans (σ₂ := { refillPhase m sigma with inflight := none }) ?_ ?_
  · intro d
    exact ⟨refillPhase_caps m sigma d, refillPhase_lineage m sigma d,
      refillPhase_slotGen m sigma d⟩
  · exact (quiet_setDom _ E _ ⟨rfl, rfl, rfl⟩).1

/-- The mark set sampled by the ISA body is the same mark set computed from
the pre-cycle abstract state. -/
theorem revRetireBase_marks (m : Manifest) (sigma : MachineState)
    (E : DomainId) (root : CapRef) :
    (revRetireBase m sigma E).marks root = sigma.marks root := by
  exact marks_congr sigma (revRetireBase m sigma E)
    (revRetireBase_tables m sigma E) root

/-- Successful revoke's final liveness is exactly pre-state liveness after
destroying the sampled mark set. -/
theorem revAbstractSuccess_liveRef (m : Manifest) (sigma : MachineState)
    (E : DomainId) (RD : RegId) (root r : CapRef) :
    (revAbstractSuccess m sigma E RD root).liveRef r =
      (sigma.destroyMarked (sigma.marks root)).liveRef r := by
  have ht := revRetireBase_tables m sigma E r.dom
  unfold revAbstractSuccess
  unfold MachineState.liveRef DomainState.liveCap
  by_cases hd : r.dom = E
  · rw [hd]
    simp only [setDom_doms_same, setReg_caps, setReg_slotGen,
      sweepMover_doms, sweepRegions_caps, sweepRegions_slotGen,
      destroyMarked_caps, destroyMarked_slotGen]
    rw [(revRetireBase_tables m sigma E E).1,
      (revRetireBase_tables m sigma E E).2.2]
  · simp only [setDom_doms_ne _ _ _ _ hd, sweepMover_doms,
      sweepRegions_caps, sweepRegions_slotGen, destroyMarked_caps,
      destroyMarked_slotGen]
    rw [ht.1, ht.2.2]

/-- Successful revoke preserves the exact kind lookup of every surviving
capability relative to `destroyMarked` on the pre-state. -/
theorem revAbstractSuccess_liveKind (m : Manifest) (sigma : MachineState)
    (E : DomainId) (RD : RegId) (root : CapRef) (d : DomainId)
    (s : Slot) (g : Gen) :
    Option.map CapEntry.kind
        (((revAbstractSuccess m sigma E RD root).doms d).liveCap s g) =
      Option.map CapEntry.kind
        (((sigma.destroyMarked (sigma.marks root)).doms d).liveCap s g) := by
  have ht := revRetireBase_tables m sigma E d
  unfold revAbstractSuccess DomainState.liveCap
  by_cases hd : d = E
  · rw [hd]
    simp only [setDom_doms_same, setReg_caps, setReg_slotGen,
      sweepMover_doms, sweepRegions_caps, sweepRegions_slotGen,
      destroyMarked_caps, destroyMarked_slotGen]
    rw [(revRetireBase_tables m sigma E E).1,
      (revRetireBase_tables m sigma E E).2.2]
  · simp only [setDom_doms_ne _ _ _ _ hd, sweepMover_doms,
      sweepRegions_caps, sweepRegions_slotGen, destroyMarked_caps,
      destroyMarked_slotGen]
    rw [ht.1, ht.2.2]

/-- The named successful state exposes the kernel `sweepMover` job face
expected by the revoke-specific circuit bridge. -/
theorem revAbstractSuccess_mover (m : Manifest) (sigma : MachineState)
    (E : DomainId) (RD : RegId) (root : CapRef) :
    (revAbstractSuccess m sigma E RD root).mover =
      match sigma.mover with
      | none => none
      | some job =>
          if (revAbstractSuccess m sigma E RD root).liveRef job.src &&
              (revAbstractSuccess m sigma E RD root).liveRef job.dst
          then some job else none := by
  let tau := (((revRetireBase m sigma E).destroyMarked
    (sigma.marks root)).sweepRegions)
  have hm : tau.mover = sigma.mover := by
    unfold tau revRetireBase
    change sigma.mover = sigma.mover
    rfl
  have hlive : ∀ r, tau.liveRef r =
      (revAbstractSuccess m sigma E RD root).liveRef r := by
    intro r
    unfold revAbstractSuccess
    change tau.liveRef r = (tau.sweepMover.setDom E
      (fun ds => ds.setReg RD 0)).liveRef r
    unfold MachineState.liveRef DomainState.liveCap
    by_cases hd : r.dom = E
    · rw [hd]
      simp [MachineState.setDom]
    · simp [MachineState.setDom, hd]
  rw [← hm]
  simp_rw [← hlive]
  unfold revAbstractSuccess
  change tau.sweepMover.mover =
    match tau.mover with
    | none => none
    | some job =>
        if tau.liveRef job.src && tau.liveRef job.dst then some job else none
  unfold MachineState.sweepMover
  cases hmov : tau.mover with
  | none => simp [hmov]
  | some job =>
      simp only
      by_cases h : tau.liveRef job.src && tau.liveRef job.dst
      · simp [h, hmov]
      · simp only [h, Bool.false_eq_true, if_false]
        split <;> rfl

/-- The revoke-specific hardware Mover bridge instantiated with the complete
named abstract success state. -/
theorem absMover_moverAct_revAbstractSuccess (m : Manifest)
    (sigma acc : Loom.Hw.St) (E : DomainId) (RD : RegId)
    (hrv : RvSync sigma)
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hopc : (sigma.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2)
    (hkills : ∀ dm sl, (Hw.killedByCoreE dm sl).eval sigma =
      (Hw.revKilled dm sl).eval sigma)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval sigma = 0#1)
    (hwf : Wf (Hw.abs sigma)) :
    Hw.absMover (Hw.moverAct.run sigma acc) =
      (moverPhase (revAbstractSuccess m (Hw.abs sigma) E RD
        (rvRoot sigma))).mover := by
  apply absMover_moverAct_revoke sigma acc
    (revAbstractSuccess m (Hw.abs sigma) E RD (rvRoot sigma))
    hrv hifv hopc hcl hkills hnew hwf
  · intro r
    exact revAbstractSuccess_liveRef m (Hw.abs sigma) E RD
      (rvRoot sigma) r
  · intro d s g
    exact revAbstractSuccess_liveKind m (Hw.abs sigma) E RD
      (rvRoot sigma) d s g
  · simpa [show (Hw.abs sigma).mover = Hw.absMover sigma from rfl] using
      revAbstractSuccess_mover m (Hw.abs sigma) E RD (rvRoot sigma)

/-- Memory counterpart of `absMover_moverAct_revAbstractSuccess`.  Only the
three genuinely circuit-facing facts remain as inputs: post-region
authority, post-core memory, and the quiescent store/memory read face. -/
theorem moverAct_mem_revAbstractSuccess (m : Manifest)
    (sigma acc : Loom.Hw.St) (E : DomainId) (RD : RegId)
    (hrv : RvSync sigma)
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hopc : (sigma.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2)
    (hkills : ∀ dm sl, (Hw.killedByCoreE dm sl).eval sigma =
      (Hw.revKilled dm sl).eval sigma)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval sigma = 0#1)
    (hwf : Wf (Hw.abs sigma))
    (hauth : ∀ (ow : Expr 2) (sa : Expr 12),
      ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
          (List.finRange numRegions).map fun r =>
            Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
              Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
                { r := false, w := true, x := false }])).eval sigma = 1#1) ↔
        (revAbstractSuccess m (Hw.abs sigma) E RD (rvRoot sigma)).domCovers
          (finOfBv (by decide) (ow.eval sigma)) (sa.eval sigma)
            { r := false, w := true, x := false } = true)
    (hmem : ∀ b : Addr, acc.mems "mem" b.toNat 32 =
      (revAbstractSuccess m (Hw.abs sigma) E RD (rvRoot sigma)).mem b)
    (hsw : ∀ job, Hw.absMover sigma = some job →
      ((revAbstractSuccess m (Hw.abs sigma) E RD
          (rvRoot sigma)).liveRef job.src &&
        (revAbstractSuccess m (Hw.abs sigma) E RD
          (rvRoot sigma)).liveRef job.dst) = true →
      ∀ sc : Expr 12, Expr.eval sigma
        (((List.finRange numDomains).foldr
          (fun d acc' =>
            Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
                Hw.domCoversE d
                  (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                  { r := false, w := true, x := false },
                .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12) sc])
              (Hw.readReg d Hw.rs2E) acc')
          (.memRead 32 "mem" sc))) =
        (revAbstractSuccess m (Hw.abs sigma) E RD (rvRoot sigma)).mem
          (sc.eval sigma))
    (a : Addr) :
    (Hw.moverAct.run sigma acc).mems "mem" a.toNat 32 =
      (moverPhase (revAbstractSuccess m (Hw.abs sigma) E RD
        (rvRoot sigma))).mem a := by
  apply moverAct_mem_revoke sigma acc
    (revAbstractSuccess m (Hw.abs sigma) E RD (rvRoot sigma))
    hrv hifv hopc hcl hkills hnew hwf
  · intro r
    exact revAbstractSuccess_liveRef m (Hw.abs sigma) E RD
      (rvRoot sigma) r
  · intro d s g
    exact revAbstractSuccess_liveKind m (Hw.abs sigma) E RD
      (rvRoot sigma) d s g
  · simpa [show (Hw.abs sigma).mover = Hw.absMover sigma from rfl] using
      revAbstractSuccess_mover m (Hw.abs sigma) E RD (rvRoot sigma)
  · exact hauth
  · exact hmem
  · exact hsw

end Machines.Lnp64u.Theorems.RMC
