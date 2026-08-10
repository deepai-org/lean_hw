-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.PairSafety
import Machines.Lnp64mini.Core

/-!
# LNP64mini run/halt protocol invariant

The board diagnostic samples `running ∧ halted`. It is not an unconditional
core invariant: command 13 can request start without reset after a halt. This
module retains that counterexample and proves the complementary result under
the exact state-dependent host command contract.

The proof is about the original open 21-rule design. Property support first
selects the `cmd` and `fsm` rules, register projection removes their unrelated
writes, and `PairSafety` checks the remaining balanced FSM action. Every input
other than the stated command condition remains arbitrary.
-/

namespace Machines.Lnp64mini.RunHaltInvariant

open Loom.Hw
open Machines.Lnp64mini

set_option maxRecDepth 100000

/-- Property used by the theorem: at least one status bit is clear. -/
def runHaltExclusive : ExprProperty :=
  .or
    (.atom runningReg.rd (fun value => value = 0#1))
    (.atom haltedReg.rd (fun value => value = 0#1))

/-- The board diagnostic's one-bit EDSL expression. -/
def violation : Expr 1 := .and runningReg.rd haltedReg.rd

def runHaltCoords : List (String × Nat) :=
  [(runningReg.name, 1), (haltedReg.name, 1)]

theorem footprint_regs : runHaltExclusive.footprint.regs = runHaltCoords := by
  decide

theorem footprint_ok : design.propertyFootprintOkB runHaltExclusive.footprint = true := by
  decide

theorem support_rules : design.propertyExprSupportRules runHaltExclusive =
    [cmdRule, fsmRule] := by
  rfl

/-- Projection leaves only the three command writes relevant to the pair. -/
theorem cmd_projected_writes : (cmdRule.body.projectRegs runHaltCoords).regWrites =
    [(haltedReg.name, 1), (runningReg.name, 1), (runningReg.name, 1)] := by
  decide

/-- Projection leaves only the five FSM writes relevant to the pair. -/
theorem fsm_projected_writes : (fsmRule.body.projectRegs runHaltCoords).regWrites =
    [(runningReg.name, 1), (haltedReg.name, 1), (runningReg.name, 1),
      (haltedReg.name, 1), (runningReg.name, 1)] := by
  decide

def runHaltOk (σ : St) : Prop :=
  σ.regs runningReg.name 1 = 0#1 ∨ σ.regs haltedReg.name 1 = 0#1

theorem runHaltOk_iff_pairExclusive (σ : St) : runHaltOk σ ↔
    PairSafety.Exclusive
      (PairSafety.observe runningReg.name haltedReg.name σ) := by
  rcases bv1_cases (σ.regs runningReg.name 1) with hr | hr <;>
    rcases bv1_cases (σ.regs haltedReg.name 1) with hh | hh <;>
    simp [runHaltOk, PairSafety.Exclusive, PairSafety.observe, hr, hh]

theorem fsm_pair_certificate :
    PairSafety.preservesExclusiveB runningReg.name haltedReg.name
      (fsmRule.body.projectRegs runHaltCoords) = true := by
  decide

theorem projectedFsm_preserves_runHalt (σ acc : St) : runHaltOk acc →
    runHaltOk ((fsmRule.body.projectRegs runHaltCoords).run σ acc) := by
  intro inputExclusive
  apply (runHaltOk_iff_pairExclusive _).2
  exact PairSafety.preservesExclusiveB_sound runningReg.name haltedReg.name
    (by decide) _ fsm_pair_certificate σ acc
    ((runHaltOk_iff_pairExclusive acc).1 inputExclusive)

/-- Host condition needed by the diagnostic: start without reset is permitted
only when the pre-cycle core is not still marked halted. -/
def cmdStartSafe (σ : St) : Prop :=
  cmdValid.eval σ = 1#1 →
  (Expr.eq cmdIdx (L7 13)).eval σ = 1#1 →
  (Expr.eq (.slice cmdData 1 1) (L1 1)).eval σ = 1#1 →
  (Expr.eq (.slice cmdData 0 1) (L1 1)).eval σ ≠ 1#1 →
  σ.regs haltedReg.name 1 = 0#1

/-- Complete command action after projecting to `running` and `halted`. -/
def runHaltCmdAction : Act :=
  .ite cmdValid
    (.ite (.eq cmdIdx (L7 13))
      (.seq
        (.ite (.eq (.slice cmdData 0 1) (L1 1))
          (.seq (haltedReg.set (L1 0)) (runningReg.set (L1 0))) .skip)
        (.ite (.eq (.slice cmdData 1 1) (L1 1))
          (runningReg.set (L1 1)) .skip))
      .skip)
    .skip

theorem cmd_projection_eq : cmdRule.body.projectRegs runHaltCoords = runHaltCmdAction := by
  rfl

theorem projectedCmd_preserves_runHalt (σ : St) :
    runHaltOk σ → cmdStartSafe σ →
      runHaltOk ((cmdRule.body.projectRegs runHaltCoords).run σ σ) := by
  intro inputExclusive safe
  rw [cmd_projection_eq]
  unfold runHaltCmdAction
  simp only [Act.run]
  have evalZero : (L1 0).eval σ = 0#1 := rfl
  have evalOne : (L1 1).eval σ = 1#1 := rfl
  by_cases valid : cmdValid.eval σ = 1#1
  · simp only [valid, ↓reduceIte]
    by_cases index : (Expr.eq cmdIdx (L7 13)).eval σ = 1#1
    · simp only [index, ↓reduceIte]
      by_cases reset : (Expr.eq (.slice cmdData 0 1) (L1 1)).eval σ = 1#1
      · by_cases start :
          (Expr.eq (.slice cmdData 1 1) (L1 1)).eval σ = 1#1 <;>
          simp [reset, start, Act.run, runHaltOk, Reg.set, RegEnv.set,
            runningReg, haltedReg, evalZero, evalOne]
      · by_cases start :
          (Expr.eq (.slice cmdData 1 1) (L1 1)).eval σ = 1#1
        · have haltedClear := safe valid index start reset
          have haltedClear' : σ.regs "halted" 1 = 0#1 := by
            simpa [haltedReg] using haltedClear
          simp [reset, start, Act.run, runHaltOk, Reg.set, runningReg,
            haltedReg, RegEnv.set, evalOne, haltedClear']
        · simpa [reset, start, Act.run, runHaltOk] using inputExclusive
    · simpa [index, runHaltOk] using inputExclusive
  · simpa [valid, runHaltOk] using inputExclusive

theorem runHaltOk_projectRegs_iff (action : Act) (σ acc : St) :
    runHaltOk ((action.projectRegs runHaltCoords).run σ acc) ↔
      runHaltOk (action.run σ acc) := by
  unfold runHaltOk
  rw [action.projectRegs_run runHaltCoords runningReg.name 1
      (by simp [runHaltCoords]) σ acc,
    action.projectRegs_run runHaltCoords haltedReg.name 1
      (by simp [runHaltCoords]) σ acc]

theorem runHaltPropertyStep (σ : St) : runHaltOk σ → cmdStartSafe σ →
    runHaltOk (design.propertyExprCycle runHaltExclusive σ) := by
  intro inputExclusive safe
  have cmdProjected := projectedCmd_preserves_runHalt σ inputExclusive safe
  have cmdFull : runHaltOk (cmdRule.body.run σ σ) :=
    (runHaltOk_projectRegs_iff cmdRule.body σ σ).1 cmdProjected
  have fsmProjected := projectedFsm_preserves_runHalt σ
    (cmdRule.body.run σ σ) cmdFull
  have fsmFull : runHaltOk
      (fsmRule.body.run σ (cmdRule.body.run σ σ)) :=
    (runHaltOk_projectRegs_iff fsmRule.body σ
      (cmdRule.body.run σ σ)).1 fsmProjected
  simpa [Design.propertyExprCycle, Design.propertyCycle, support_rules] using fsmFull

theorem runHaltExclusive_reset : runHaltExclusive.eval design.reset := by
  simp only [runHaltExclusive, ExprProperty.eval, Reg.rd, Expr.eval]
  decide

/-- Closed witness showing why an unrestricted theorem would be false. -/
def haltedStartOnly : St :=
  let ρ := design.reset.regs
    |>.set haltedReg.name (1#1)
    |>.set runningReg.name (0#1)
    |>.set cmdValidPort.name (1#1)
    |>.set cmdIdxPort.name (13#7)
    |>.set cmdDataPort.name (2#32)
  { design.reset with regs := ρ }

theorem startOnlyAfterHalt_initially_exclusive : runHaltExclusive.eval haltedStartOnly := by
  simp only [runHaltExclusive, ExprProperty.eval, Reg.rd, Expr.eval]
  decide

theorem runHaltExclusive_not_unconditional : ¬ runHaltExclusive.eval (design.cycle haltedStartOnly) := by
  intro full
  have reduced : runHaltExclusive.eval
      (design.propertyExprCycle runHaltExclusive haltedStartOnly) :=
    (runHaltExclusive.supports _ _
      (design.cycle_agreeOn_propertyCycle runHaltExclusive.footprint
        haltedStartOnly)).mp full
  have notReduced : ¬ runHaltExclusive.eval
      (design.propertyExprCycle runHaltExclusive haltedStartOnly) := by
    simp only [runHaltExclusive, ExprProperty.eval, Reg.rd, Expr.eval]
    decide
  exact notReduced reduced

/-- Exact state-dependent environment contract used by the open theorem. -/
def cmdProtocolAssumption : InputAssumption := fun σ ι =>
  cmdStartSafe (σ.setInputs design.inputs ι)

theorem setInputs_runHaltOk_iff (σ : St) (ι : InEnv) :
    runHaltOk (σ.setInputs design.inputs ι) ↔ runHaltOk σ := by
  unfold runHaltOk
  rw [σ.setInputs_regs_notin design.inputs ι runningReg.name 1 (by decide),
    σ.setInputs_regs_notin design.inputs ι haltedReg.name 1 (by decide)]

theorem runHaltExclusive_eval_iff (σ : St) : runHaltExclusive.eval σ ↔ runHaltOk σ := by
  rfl

theorem runHaltOpenPropertyStep (σ : St) (ι : InEnv) :
    runHaltExclusive.eval σ → cmdProtocolAssumption σ ι →
      runHaltExclusive.eval (design.propertyExprCycleOpen runHaltExclusive ι σ) := by
  intro inputExclusive accepted
  apply (runHaltExclusive_eval_iff _).2
  exact runHaltPropertyStep (σ.setInputs design.inputs ι)
    ((setInputs_runHaltOk_iff σ ι).2 ((runHaltExclusive_eval_iff σ).1 inputExclusive))
    accepted

/-- Headline result: `running` and `halted` cannot both be one in any state
reachable under the explicit command protocol. Other inputs are unrestricted. -/
theorem runHaltExclusive_under_cmdProtocol :
    (design.toAssumedOpenTSys cmdProtocolAssumption).Invariant runHaltExclusive.eval :=
  design.invariant_of_assumedPropertyExprCycleOpen cmdProtocolAssumption runHaltExclusive
    runHaltExclusive_reset runHaltOpenPropertyStep

end Machines.Lnp64mini.RunHaltInvariant
