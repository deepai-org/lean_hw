-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64mini.RunHaltInvariant

/-!
# LNP64mini lifecycle invariant

This module extends the run/halt theorem to the reset sweep.  The open core
needs two state-dependent command obligations: start-only must not revive a
still-halted core, and a soft reset must not collide with an actively running
FSM cycle.  Under those explicit obligations, `running`, `halted`, and
`zeroing` remain in a valid lifecycle state.

The inferred property cone contains exactly the real `zeroing`, `cmd`, and
`fsm` rules from the original design.
-/

namespace Machines.Lnp64mini.LifecycleInvariant

open Loom.Hw
open Machines.Lnp64mini
open Machines.Lnp64mini.RunHaltInvariant

set_option maxRecDepth 100000

/-- A halted core is never simultaneously performing the reset sweep. -/
def haltZeroExclusive : ExprProperty :=
  .or
    (.atom haltedReg.rd (fun value => value = 0#1))
    (.atom zeroingReg.rd (fun value => value = 0#1))

/-- The three-bit lifecycle property exposed by this module. -/
def lifecycleSafe : ExprProperty :=
  .and runHaltExclusive haltZeroExclusive

theorem footprint_regs : lifecycleSafe.footprint.regs =
    [(runningReg.name, 1), (haltedReg.name, 1),
      (haltedReg.name, 1), (zeroingReg.name, 1)] := by
  decide

theorem footprint_ok : design.propertyFootprintOkB lifecycleSafe.footprint = true := by
  decide

theorem support_rules : design.propertyExprSupportRules lifecycleSafe =
    [zeroingRule, cmdRule, fsmRule] := by
  rfl

def haltZeroOk (σ : St) : Prop :=
  σ.regs haltedReg.name 1 = 0#1 ∨ σ.regs zeroingReg.name 1 = 0#1

theorem haltZeroExclusive_eval_iff (σ : St) :
    haltZeroExclusive.eval σ ↔ haltZeroOk σ := by
  rfl

def haltZeroCoords : List (String × Nat) :=
  haltZeroExclusive.footprint.regs

/-- The reset engine can only clear `zeroing`; all datapath writes disappear. -/
def haltZeroZeroingAction : Act :=
  .ite zeroing
    (.ite (.eq zctr (.lit (BitVec.ofNat 10 (32 * NT - 1))))
      (zeroingReg.set (L1 0)) .skip)
    .skip

theorem zeroing_projection_eq :
    zeroingRule.body.projectRegs haltZeroCoords = haltZeroZeroingAction := by
  rfl

/-- The command surface can only clear `halted` and start `zeroing`, in that
order, when command 13 requests a reset. -/
def haltZeroCmdAction : Act :=
  .ite cmdValid
    (.ite (.eq cmdIdx (L7 13))
      (.ite (.eq (.slice cmdData 0 1) (L1 1))
        (.seq (haltedReg.set (L1 0)) (zeroingReg.set (L1 1))) .skip)
      .skip)
    .skip

theorem cmd_projection_eq :
    cmdRule.body.projectRegs haltZeroCoords = haltZeroCmdAction := by
  rfl

theorem haltZeroOk_projectRegs_iff (action : Act) (σ acc : St) :
    haltZeroOk ((action.projectRegs haltZeroCoords).run σ acc) ↔
      haltZeroOk (action.run σ acc) := by
  unfold haltZeroOk
  rw [action.projectRegs_run haltZeroCoords haltedReg.name 1
      (by decide) σ acc,
    action.projectRegs_run haltZeroCoords zeroingReg.name 1
      (by decide) σ acc]

theorem projectedZeroing_preserves (σ : St) : haltZeroOk σ →
    haltZeroOk ((zeroingRule.body.projectRegs haltZeroCoords).run σ σ) := by
  intro safe
  rw [zeroing_projection_eq]
  unfold haltZeroZeroingAction
  have evalZero : (L1 0).eval σ = 0#1 := rfl
  by_cases active : zeroing.eval σ = 1#1
  · by_cases done :
        (Expr.eq zctr (.lit (BitVec.ofNat 10 (32 * NT - 1)))).eval σ = 1#1
    · simp [Expr.eval] at done
      simp [Act.run, active, done, haltZeroOk, haltedReg, zeroingReg, Reg.set,
        RegEnv.set, Expr.eval, evalZero]
    · simpa [Act.run, active, done, haltZeroOk] using safe
  · simpa [Act.run, active, haltZeroOk] using safe

theorem projectedCmd_preserves (σ acc : St) : haltZeroOk acc →
    haltZeroOk ((cmdRule.body.projectRegs haltZeroCoords).run σ acc) := by
  intro safe
  rw [cmd_projection_eq]
  unfold haltZeroCmdAction
  have evalZero : (L1 0).eval σ = 0#1 := rfl
  have evalOne : (L1 1).eval σ = 1#1 := rfl
  by_cases valid : cmdValid.eval σ = 1#1
  · by_cases index : (Expr.eq cmdIdx (L7 13)).eval σ = 1#1
    · by_cases reset :
        (Expr.eq (.slice cmdData 0 1) (L1 1)).eval σ = 1#1
      · simp [Expr.eval] at index reset
        simp [Act.run, valid, index, reset, haltZeroOk, haltedReg, zeroingReg,
          Reg.set, RegEnv.set, Expr.eval, evalZero, evalOne]
      · simpa [Act.run, valid, index, reset, haltZeroOk] using safe
    · simpa [Act.run, valid, index, haltZeroOk] using safe
  · simpa [Act.run, valid, haltZeroOk] using safe

/-- A reset request is accepted only while the pre-cycle core is stopped.
This prevents the old FSM instruction and the new reset sweep from both
committing lifecycle state in the same D9 cycle. -/
def resetWhileStopped (σ : St) : Prop :=
  cmdValid.eval σ = 1#1 →
  (Expr.eq cmdIdx (L7 13)).eval σ = 1#1 →
  (Expr.eq (.slice cmdData 0 1) (L1 1)).eval σ = 1#1 →
  σ.regs runningReg.name 1 = 0#1

/-- Both host obligations, evaluated after the open-cycle inputs are
installed. All non-command inputs remain unrestricted. -/
def lifecycleAssumption : InputAssumption := fun σ ι =>
  cmdProtocolAssumption σ ι ∧
    resetWhileStopped (σ.setInputs design.inputs ι)

def haltZeroPrefix (σ : St) : St :=
  (cmdRule.body.projectRegs haltZeroCoords).run σ
    ((zeroingRule.body.projectRegs haltZeroCoords).run σ σ)

theorem prefix_preserves (σ : St) : haltZeroOk σ → haltZeroOk (haltZeroPrefix σ) := by
  intro safe
  exact projectedCmd_preserves σ _ (projectedZeroing_preserves σ safe)

theorem fsm_disabled_of_prefix_zeroing (σ : St) :
    resetWhileStopped σ →
    (haltZeroPrefix σ).regs zeroingReg.name 1 = 1#1 →
    fsmEn.eval σ ≠ 1#1 := by
  intro resetSafe postZeroing
  unfold haltZeroPrefix at postZeroing
  rw [cmd_projection_eq, zeroing_projection_eq] at postZeroing
  unfold haltZeroCmdAction haltZeroZeroingAction at postZeroing
  by_cases active : zeroing.eval σ = 1#1
  · simp [fsmEn, active, Expr.eval]
  · have active' : σ.regs "zeroing" 1 ≠ 1#1 := by
      simpa [zeroing, zeroingReg, Reg.rd, Expr.eval] using active
    by_cases valid : cmdValid.eval σ = 1#1
    · by_cases index : (Expr.eq cmdIdx (L7 13)).eval σ = 1#1
      · by_cases reset :
          (Expr.eq (.slice cmdData 0 1) (L1 1)).eval σ = 1#1
        · have stopped := resetSafe valid index reset
          simp [fsmEn, running, Reg.rd, stopped, Expr.eval]
        · simp [Expr.eval] at index reset
          simp [Act.run, active', valid, index, reset, zeroing, zeroingReg,
            Reg.rd, Expr.eval] at postZeroing
      · simp [Expr.eval] at index
        simp [Act.run, active', valid, index, zeroing, zeroingReg,
          Reg.rd, Expr.eval] at postZeroing
    · simp [Act.run, active', valid, zeroing, zeroingReg, Reg.rd, Expr.eval]
        at postZeroing

theorem projectedFsm_preserves (σ : St) : resetWhileStopped σ →
    haltZeroOk (haltZeroPrefix σ) →
    haltZeroOk ((fsmRule.body.projectRegs haltZeroCoords).run σ
      (haltZeroPrefix σ)) := by
  intro resetSafe safe
  by_cases clear : (haltZeroPrefix σ).regs zeroingReg.name 1 = 0#1
  · right
    rw [fsmRule.body.projectRegs_run haltZeroCoords zeroingReg.name 1
      (by decide) σ (haltZeroPrefix σ)]
    exact fsmRule.body.run_regs_notin zeroingReg.name 1 (by decide) σ
      (haltZeroPrefix σ) |>.trans clear
  · have set : (haltZeroPrefix σ).regs zeroingReg.name 1 = 1#1 := by
      rcases bv1_cases ((haltZeroPrefix σ).regs zeroingReg.name 1) with h | h
      · exact (clear h).elim
      · exact h
    have disabled := fsm_disabled_of_prefix_zeroing σ resetSafe set
    rw [show fsmRule.body.projectRegs haltZeroCoords =
        .ite fsmEn ((actPriTree
          [s_f0, s_pause, s_fw, s_rd, s_rd2, s_ex, s_l0, s_l1, s_dl, s_dst,
           s_dsw, s_cs0, s_cs1, s_cr0, s_cr1, s_clone2, s_clone3, s_ftx1,
           s_wait, s_mul, s_div, s_gpl, s_gps, s_ic, s_gret, s_gc0, s_gc1, s_dc,
           s_default] .skip).projectRegs haltZeroCoords) .skip from rfl]
    simpa [Act.run, disabled, haltZeroOk] using safe

def haltZeroFullPrefix (σ : St) : St :=
  cmdRule.body.run σ (zeroingRule.body.run σ σ)

theorem prefix_regs_eq (σ : St) (name : String) (width : Nat)
    (selected : (name, width) ∈ haltZeroCoords) :
    (haltZeroPrefix σ).regs name width =
      (haltZeroFullPrefix σ).regs name width := by
  unfold haltZeroPrefix haltZeroFullPrefix
  have zeroEq := zeroingRule.body.projectRegs_run haltZeroCoords name width
    selected σ σ
  have cmdProjected := cmdRule.body.projectRegs_run haltZeroCoords name width
    selected σ ((zeroingRule.body.projectRegs haltZeroCoords).run σ σ)
  have cmdAcc := cmdRule.body.run_regs_congr_acc σ
    ((zeroingRule.body.projectRegs haltZeroCoords).run σ σ)
    (zeroingRule.body.run σ σ) name width zeroEq
  exact cmdProjected.trans cmdAcc

theorem fullPrefix_preserves (σ : St) : haltZeroOk σ →
    haltZeroOk (haltZeroFullPrefix σ) := by
  intro safe
  have afterZeroProjected := projectedZeroing_preserves σ safe
  have afterZeroFull : haltZeroOk (zeroingRule.body.run σ σ) :=
    (haltZeroOk_projectRegs_iff zeroingRule.body σ σ).1 afterZeroProjected
  have afterCmdProjected := projectedCmd_preserves σ
    (zeroingRule.body.run σ σ) afterZeroFull
  exact (haltZeroOk_projectRegs_iff cmdRule.body σ
    (zeroingRule.body.run σ σ)).1 afterCmdProjected

theorem fullFsm_preserves (σ : St) : resetWhileStopped σ →
    haltZeroOk (haltZeroFullPrefix σ) →
    haltZeroOk (fsmRule.body.run σ (haltZeroFullPrefix σ)) := by
  intro resetSafe safe
  by_cases clear : (haltZeroFullPrefix σ).regs zeroingReg.name 1 = 0#1
  · right
    exact (fsmRule.body.run_regs_notin zeroingReg.name 1 (by decide) σ
      (haltZeroFullPrefix σ)).trans clear
  · have set : (haltZeroFullPrefix σ).regs zeroingReg.name 1 = 1#1 := by
      rcases bv1_cases ((haltZeroFullPrefix σ).regs zeroingReg.name 1) with h | h
      · exact (clear h).elim
      · exact h
    have projectedSet : (haltZeroPrefix σ).regs zeroingReg.name 1 = 1#1 :=
      (prefix_regs_eq σ zeroingReg.name 1 (by decide)).trans set
    have disabled := fsm_disabled_of_prefix_zeroing σ resetSafe projectedSet
    simpa [fsmRule, Act.run, disabled, haltZeroOk] using safe

theorem haltZeroPropertyStep (σ : St) :
    haltZeroOk σ → resetWhileStopped σ →
      haltZeroOk (design.propertyExprCycle haltZeroExclusive σ) := by
  intro safe resetSafe
  have prefixSafe := fullPrefix_preserves σ safe
  have finalSafe := fullFsm_preserves σ resetSafe prefixSafe
  simpa [Design.propertyExprCycle, Design.propertyCycle] using finalSafe

theorem haltZeroExclusive_reset : haltZeroExclusive.eval design.reset := by
  simp only [haltZeroExclusive, ExprProperty.eval, Reg.rd, Expr.eval]
  decide

theorem setInputs_haltZeroOk_iff (σ : St) (ι : InEnv) :
    haltZeroOk (σ.setInputs design.inputs ι) ↔ haltZeroOk σ := by
  unfold haltZeroOk
  rw [σ.setInputs_regs_notin design.inputs ι haltedReg.name 1 (by decide),
    σ.setInputs_regs_notin design.inputs ι zeroingReg.name 1 (by decide)]

theorem haltZeroOpenPropertyStep (σ : St) (ι : InEnv) :
    haltZeroExclusive.eval σ → lifecycleAssumption σ ι →
      haltZeroExclusive.eval
        (design.propertyExprCycleOpen haltZeroExclusive ι σ) := by
  intro safe accepted
  apply (haltZeroExclusive_eval_iff _).2
  apply haltZeroPropertyStep (σ.setInputs design.inputs ι)
  · exact (setInputs_haltZeroOk_iff σ ι).2
      ((haltZeroExclusive_eval_iff σ).1 safe)
  · exact accepted.2

theorem lifecycleSafe_reset : lifecycleSafe.eval design.reset :=
  ⟨runHaltExclusive_reset, haltZeroExclusive_reset⟩

theorem lifecycleOpenPropertyStep (σ : St) (ι : InEnv) :
    lifecycleSafe.eval σ → lifecycleAssumption σ ι →
      lifecycleSafe.eval (design.propertyExprCycleOpen lifecycleSafe ι σ) := by
  intro safe accepted
  have runReduced := runHaltOpenPropertyStep σ ι safe.1 accepted.1
  have runFull : runHaltExclusive.eval (design.cycleOpen ι σ) :=
    (runHaltExclusive.supports _ _
      (design.cycleOpen_agreeOn_propertyCycleOpen
        runHaltExclusive.footprint ι σ)).2 runReduced
  have haltReduced := haltZeroOpenPropertyStep σ ι safe.2 accepted
  have haltFull : haltZeroExclusive.eval (design.cycleOpen ι σ) :=
    (haltZeroExclusive.supports _ _
      (design.cycleOpen_agreeOn_propertyCycleOpen
        haltZeroExclusive.footprint ι σ)).2 haltReduced
  have lifecycleFull : lifecycleSafe.eval (design.cycleOpen ι σ) :=
    ⟨runFull, haltFull⟩
  exact (lifecycleSafe.supports _ _
    (design.cycleOpen_agreeOn_propertyCycleOpen lifecycleSafe.footprint ι σ)).1
      lifecycleFull

/-- Headline lifecycle theorem for the original open 21-rule core. -/
theorem lifecycleSafe_under_hostProtocol :
    (design.toAssumedOpenTSys lifecycleAssumption).Invariant lifecycleSafe.eval :=
  design.invariant_of_assumedPropertyExprCycleOpen lifecycleAssumption lifecycleSafe
    lifecycleSafe_reset lifecycleOpenPropertyStep

end Machines.Lnp64mini.LifecycleInvariant
