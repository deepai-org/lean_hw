-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Tactics
import Loom.Hw.PairSafety
import Machines.Lnp64mini.Core
import Machines.Lnp64mini.RunHaltInvariant
import Machines.Lnp64mini.LifecycleInvariant
import Machines.Tutorial.SatCounter

/-!
# Property-directed cycle projection regressions

The generic theorem removes every rule that cannot write the projected
coordinate. The LNP64mini checks below ensure this is useful on the large
core, rather than only on a toy design.
-/

namespace Tests.CycleSupport

open Loom.Hw
open Machines.Lnp64mini
open Machines.Lnp64mini.RunHaltInvariant
open Machines.Lnp64mini.LifecycleInvariant

set_option maxRecDepth 100000

example : (design.regSupportRules faultCauseReg.name 8).map (fun r => r.name) =
    ["fsm", "tarr_funnel"] := by native_decide

example : (design.regSupportRules "trace_hit" 1).map (fun r => r.name) =
    ["pulse_defaults", "cmd", "fsm"] := by native_decide

example : design.regSupportRules "cur_dom" 8 = [domainRule] := rfl

/-- A 21-rule LNP64mini cycle reduces definitionally to the sole rule that
can write `cur_dom`; unrelated cache, bus, scheduler, and gate logic vanishes. -/
theorem cur_dom_cycle_is_local (σ : St) :
    (design.cycle σ).regs "cur_dom" 8 =
      (domainRule.body.run σ σ).regs "cur_dom" 8 := by
  cycle_support
  rfl

example : design.memSupportRules "rf" = [rfFunnelRule] := rfl

/-- The register-file projection likewise retains only its write funnel. -/
theorem rf_cycle_is_local (σ : St) (addr width : Nat) :
    (design.cycle σ).mems "rf" addr width =
      (rfFunnelRule.body.run σ σ).mems "rf" addr width := by
  cycle_support
  rfl

/-! A two-coordinate property support. These observation mirrors are maintained
by two rules out of the 21-rule core; the union retains each rule once and in
its original last-write-wins order. -/

def observationCoords : List (String × Nat) :=
  [(ddrRdLReg.name, 64), (curDomReg.name, 8)]

example : (design.regPropertySupport observationCoords).map (fun rule => rule.name) =
    ["ddr_rd_l", "domain"] := by native_decide

example : design.regSupportRules ddrRdLReg.name 64 = [ddrRdLRule] := rfl

/-- Two observations are proved from a two-rule property cone. The right sides
deliberately use the pre-cycle state, matching D9 semantics. -/
theorem observations_after_cycle (σ : St) :
    (design.cycle σ).regs ddrRdLReg.name 64 =
      (if (Expr.and mDone (.not hp_core_owns)).eval σ = 1#1 then
        mRdata.eval σ else σ.regs ddrRdLReg.name 64) ∧
    (design.cycle σ).regs curDomReg.name 8 = domCur.eval σ := by
  constructor
  · cycle_support
    rw [show design.regSupportRules ddrRdLReg.name 64 = [ddrRdLRule] from rfl]
    by_cases h : (Expr.and mDone (.not hp_core_owns)).eval σ = 1#1
    · simp [ddrRdLRule, Act.run, h]
    · simp [ddrRdLRule, Act.run, h]
  · cycle_support
    rfl

def mixedFootprint : PropertyFootprint where
  regs := [(curDomReg.name, 8)]
  mems := [(rfBank.name, 64)]

/-- Heterogeneous register/memory atoms combine into the same mixed footprint
without a manually maintained coordinate list. -/
def mixedExprProperty : ExprProperty :=
  .and
    (.atom curDomReg.rd (fun _ => True))
    (.atom (rfBank.rd (.lit 0#10)) (fun _ => True))

example : mixedExprProperty.footprint = mixedFootprint := by
  native_decide

example : mixedExprProperty.footprint.Supports mixedExprProperty.eval :=
  mixedExprProperty.supports

example : (design.propertyExprSupportRules mixedExprProperty).map
    (fun rule => rule.name) = ["rf_funnel", "domain"] := by
  native_decide

example : design.propertyFootprintOkB mixedFootprint = true := by native_decide

example : (design.propertySupportRules mixedFootprint).map (fun rule => rule.name) =
    ["rf_funnel", "domain"] := by native_decide

/-! Intra-rule memory and mixed-footprint projection on the real thread-array
funnel. One retained rule owns eight memory writes and three register writes;
the property needs one of each. -/

def tarrFootprint : PropertyFootprint where
  regs := [(inGateReg.name, 32)]
  mems := [(tpcBank.name, 64)]

def tarrExprProperty : ExprProperty :=
  .and
    (.atom inGateReg.rd (fun _ => True))
    (.atom (tpcBank.rd (.lit 0#5)) (fun _ => True))

example : tarrExprProperty.footprint = tarrFootprint := by native_decide

example : (design.propertyExprSupportRules tarrExprProperty).map
    (fun rule => rule.name) = ["tarr_funnel"] := by native_decide

example : tarrFunnelRule.body.regWrites =
    [(inGateReg.name, 32), (faultCauseReg.name, 8),
      (tlbVldReg.name, 8)] := by
  native_decide

example : tarrFunnelRule.body.memWrites =
    [tdomBank.name, tcontBank.name, tcdomBank.name, gdepthBank.name,
      tpcBank.name, tsleepBank.name, tpBank.name, sigmaskBank.name] := by
  native_decide

example : (tarrFunnelRule.body.projectFootprint tarrFootprint).regWrites =
    [(inGateReg.name, 32)] := by native_decide

example : (tarrFunnelRule.body.projectFootprint tarrFootprint).memWrites =
    [tpcBank.name] := by native_decide

example (σ : St) :
    St.AgreeOn tarrFootprint.regs tarrFootprint.mems
      (design.cycle σ) (design.propertyProjectedCycle tarrFootprint σ) :=
  design.cycle_agreeOn_propertyProjectedCycle tarrFootprint σ

/-- One reduced state simultaneously covers a register observation and every
address of a memory observation. -/
example (σ : St) :
    St.AgreeOn mixedFootprint.regs mixedFootprint.mems
      (design.cycle σ) (design.propertyCycle mixedFootprint σ) :=
  design.cycle_agreeOn_propertyCycle mixedFootprint σ

def misspelledFootprint : PropertyFootprint where
  regs := [("cur_dmo", 8)]
  mems := [(rfBank.name, 63)]

/-! Negative controls: both a misspelled register and wrong memory width are
named, rather than yielding a deceptively tiny support. -/
example : design.propertyFootprintOkB misspelledFootprint = false := by
  native_decide

example : design.invalidPropertyRegs misspelledFootprint = [("cur_dmo", 8)] := by
  native_decide

example : design.invalidPropertyMems misspelledFootprint = [(rfBank.name, 63)] := by
  native_decide

/-! ### A machine-scale composed invariant

The board debug map observes `running ∧ halted` as a protocol violation.
State its complement here using the same typed expressions: at least one bit
is clear. Unlike the small tutorial example below, this property is over the
complete LNP64mini design. Its inferred writer cone retains only the command
surface and FSM rule.
-/

example : runHaltExclusive.footprint.regs =
    [(runningReg.name, 1), (haltedReg.name, 1)] := by
  native_decide

example : design.propertyFootprintOkB runHaltExclusive.footprint = true := by
  native_decide

example : (design.propertyExprSupportRules runHaltExclusive).map
    (fun rule => rule.name) = ["cmd", "fsm"] := by
  native_decide

/-! Projecting inside those two retained rules removes hundreds of unrelated
writes while preserving both selected accumulator coordinates. -/
example : (cmdRule.body.projectRegs runHaltCoords).regWrites =
    [(haltedReg.name, 1), (runningReg.name, 1), (runningReg.name, 1)] := by
  native_decide

example : (fsmRule.body.projectRegs runHaltCoords).regWrites =
    [(runningReg.name, 1), (haltedReg.name, 1), (runningReg.name, 1),
      (haltedReg.name, 1), (runningReg.name, 1)] := by
  native_decide

example (action : Act) (σ acc : St) :
    ((action.projectRegs runHaltCoords).run σ acc).regs runningReg.name 1 =
      (action.run σ acc).regs runningReg.name 1 :=
  action.projectRegs_run runHaltCoords runningReg.name 1 (by simp [runHaltCoords]) σ acc

example : PairSafety.preservesExclusiveB runningReg.name haltedReg.name
    (fsmRule.body.projectRegs runHaltCoords) = true := by
  native_decide

/-- A host-visible counterexample to treating the debug predicate as an
unconditional machine invariant.  Command 13 with only its start bit set can
restart a state whose `halted` bit is still one.  The host protocol normally
combines reset and start; that protocol assumption is not part of `Design`.
-/
example : runHaltExclusive.eval haltedStartOnly := by
  simp only [runHaltExclusive, ExprProperty.eval, Reg.rd, Expr.eval]
  native_decide

example : ¬ runHaltExclusive.eval
    (design.propertyExprCycle runHaltExclusive haltedStartOnly) := by
  simp only [runHaltExclusive, ExprProperty.eval, Reg.rd, Expr.eval]
  native_decide

/-! A larger composed invariant that is valid for the closed transition
system: environment-owned inputs do not change during `Design.cycle`.  This
is intentionally a closed-design claim; `cycleOpen` may drive these values.
Twelve heterogeneous atoms infer twelve coordinates but no writer rules out
of LNP64mini's 21-rule cycle. -/

def zeroInput {w : Nat} (input : Reg w) : ExprProperty :=
  .atom input.rd (fun value => value = 0#w)

def closedInputsZero : ExprProperty := ExprProperty.all
  [ zeroInput mDonePort
  , zeroInput mRdataPort
  , zeroInput mBusyPort
  , zeroInput gpDonePort
  , zeroInput gpRdataPort
  , zeroInput gpBusyPort
  , zeroInput cmdValidPort
  , zeroInput cmdIdxPort
  , zeroInput cmdDataPort
  , zeroInput resKillPort
  , zeroInput doorbellPort
  , zeroInput holdPort ]

example : closedInputsZero.footprint.regs.length = 12 := by native_decide

example : design.propertyFootprintOkB closedInputsZero.footprint = true := by
  native_decide

example : design.propertyExprSupportRules closedInputsZero = [] := by
  native_decide

theorem closedInputsZero_reset : closedInputsZero.eval design.reset := by
  simp only [closedInputsZero, ExprProperty.all, zeroInput,
    List.foldr_cons, List.foldr_nil, ExprProperty.eval, Reg.rd, Expr.eval]
  decide

theorem closedInputsZero_step (σ : St) : closedInputsZero.eval σ →
    closedInputsZero.eval (design.propertyExprCycle closedInputsZero σ) := by
  intro h
  simpa [Design.propertyExprCycle, Design.propertyCycle,
    show design.propertySupportRules closedInputsZero.footprint = [] from rfl]
    using h

theorem closedInputsZero_invariant :
    design.toTSys.Invariant closedInputsZero.eval :=
  design.invariant_of_propertyExprCycle closedInputsZero
    closedInputsZero_reset closedInputsZero_step

/-- Explicit environment contract for the open form of the same property. -/
def zeroInputsAssumption : InputAssumption := fun σ ι =>
  closedInputsZero.eval (σ.setInputs design.inputs ι)

theorem openInputsZero_invariant :
    (design.toAssumedOpenTSys zeroInputsAssumption).Invariant
      closedInputsZero.eval :=
  design.invariant_of_assumedPropertyExprCycleOpen zeroInputsAssumption
    closedInputsZero closedInputsZero_reset (by
      intro σ ι _ accepted
      simpa [Design.propertyExprCycleOpen, Design.propertyCycleOpen,
        Design.propertyCycle,
        show design.propertySupportRules closedInputsZero.footprint = [] from rfl]
        using accepted)

def haltedBeforeStart : St :=
  let ρ := design.reset.regs
    |>.set haltedReg.name (1#1)
    |>.set runningReg.name (0#1)
  { design.reset with regs := ρ }

def startOnlyEnv : InEnv := haltedStartOnly.regs

example : ¬ cmdProtocolAssumption haltedBeforeStart startOnlyEnv := by
  simp only [cmdProtocolAssumption, cmdStartSafe]
  decide

/-! The next machine-scale invariant expands both the state footprint and
the nonempty writer cone. -/

example : (design.propertyExprSupportRules lifecycleSafe).map
    (fun rule => rule.name) = ["zeroing", "cmd", "fsm"] := by
  native_decide

example : (design.toAssumedOpenTSys lifecycleAssumption).Invariant
    lifecycleSafe.eval :=
  lifecycleSafe_under_hostProtocol

end Tests.CycleSupport

namespace Tests.CycleSupport.Tutorial

open Loom.Hw
open Machines.Tutorial.SatCounter

def satCoords : List (String × Nat) :=
  [(count.name, 8), (sat.name, 1)]

def satFootprint : PropertyFootprint where
  regs := satCoords

/-- The implication `sat → count = 255`, represented as a one-bit EDSL
expression so its footprint can be inferred rather than listed. -/
def satOkExpr : Expr 1 :=
  .or (.not sat.rd) (.eq count.rd (.lit 255#8))

/-- The same property with two differently typed atoms combined in `Prop`.
This is the shape used when a property is clearer as several observations
than as one bit-vector expression. -/
def satOkProperty : ExprProperty :=
  .or
    (.atom sat.rd (fun value => value = 0#1))
    (.atom count.rd (fun value => value = 255#8))

theorem satOkProperty_iff (σ : St) : satOkProperty.eval σ ↔ SatOk σ := by
  by_cases hs : σ.regs sat.name 1 = 1#1
  · simp [satOkProperty, ExprProperty.eval, SatOk, Reg.rd, Expr.eval, hs]
  · have hz : σ.regs sat.name 1 = 0#1 := by bv_omega
    simp [satOkProperty, ExprProperty.eval, SatOk, Reg.rd, Expr.eval, hz]

example : satOkProperty.footprint.regs =
    [(sat.name, 1), (count.name, 8)] := by
  native_decide

example : design.propertyFootprintOkB satOkProperty.footprint = true := by
  native_decide

example : (design.propertyExprSupportRules satOkProperty).map
    (fun rule => rule.name) = ["tick"] := by
  native_decide

example (σ : St) : design.propertyExprCycle satOkProperty σ =
    design.propertyCycle satFootprint σ := by
  rfl

theorem satOkExpr_iff (σ : St) :
    satOkExpr.eval σ = 1#1 ↔ SatOk σ := by
  by_cases hs : σ.regs sat.name 1 = 1#1
  · by_cases hc : σ.regs count.name 8 = 255#8
    · simp [satOkExpr, SatOk, Reg.rd, Expr.eval, hs, hc]
    · simp [satOkExpr, SatOk, Reg.rd, Expr.eval, hs, hc]
  · have hz : σ.regs sat.name 1 = 0#1 := by bv_omega
    by_cases hc : σ.regs count.name 8 = 255#8
    · simp [satOkExpr, SatOk, Reg.rd, Expr.eval, hz, hc]
    · simp [satOkExpr, SatOk, Reg.rd, Expr.eval, hz, hc]

example : (PropertyFootprint.ofExpr satOkExpr).regs =
    [(sat.name, 1), (count.name, 8)] := by
  native_decide

example : (PropertyFootprint.ofExpr satOkExpr).mems = [] := by
  native_decide

example : design.propertyFootprintOkB (.ofExpr satOkExpr) = true := by
  native_decide

example : (design.exprPropertySupportRules satOkExpr).map (fun rule => rule.name) =
    ["tick"] := by
  native_decide

example (σ : St) :
    design.exprPropertyCycle satOkExpr σ =
      design.propertyCycle satFootprint σ := by
  rfl

example : (PropertyFootprint.ofExpr satOkExpr).Supports
    (fun σ => satOkExpr.eval σ = 1#1) :=
  PropertyFootprint.supports_eval satOkExpr (fun value => value = 1#1)

example : design.propertyFootprintOkB satFootprint = true := by native_decide

example : satFootprint.Supports (satFootprint.lift SatOk) :=
  satFootprint.supports_lift SatOk

example : (design.regPropertySupport satCoords).map (fun rule => rule.name) =
    ["tick"] := by
  native_decide

/-- The tutorial invariant's entire transition cone is the one `tick` rule;
both projections use the same inferred support rather than unfolding
`Design.cycle` independently. -/
example (σ : St) :
    (design.cycle σ).regs count.name 8 =
      ((design.regPropertySupport satCoords).foldl
        (fun state rule => rule.body.run σ state) σ).regs count.name 8 ∧
    (design.cycle σ).regs sat.name 1 =
      ((design.regPropertySupport satCoords).foldl
        (fun state rule => rule.body.run σ state) σ).regs sat.name 1 := by
  constructor
  · exact design.cycle_regs_eq_propertySupport satCoords count.name 8
      (by simp [satCoords]) σ
  · exact design.cycle_regs_eq_propertySupport satCoords sat.name 1
      (by simp [satCoords]) σ

theorem satOk_supported : satFootprint.Supports SatOk := by
  intro σ τ hagree
  constructor
  · intro hP hsat
    have hsat' : σ.regs sat.name 1 = 1#1 := by
      rw [hagree.1 sat.name 1 (by simp [satFootprint, satCoords])]
      exact hsat
    calc
      τ.regs count.name 8 = σ.regs count.name 8 :=
        (hagree.1 count.name 8 (by simp [satFootprint, satCoords])).symm
      _ = 255#8 := hP hsat'
  · intro hP hsat
    have hsat' : τ.regs sat.name 1 = 1#1 := by
      rw [← hagree.1 sat.name 1 (by simp [satFootprint, satCoords])]
      exact hsat
    calc
      σ.regs count.name 8 = τ.regs count.name 8 :=
        hagree.1 count.name 8 (by simp [satFootprint, satCoords])
      _ = 255#8 := hP hsat'

theorem satOk_propertyStep (σ : St) :
    SatOk σ → SatOk (design.propertyCycle satFootprint σ) := by
  intro hP
  unfold Design.propertyCycle
  rw [show design.propertySupportRules satFootprint = [⟨"tick", tick⟩] from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [show tick =
    .ite (.eq count.rd (.lit 255#8))
      (sat.set (.lit 1#1))
      (count.set (.add count.rd (.lit 1#8))) from rfl]
  by_cases hcond : (Expr.eq count.rd (.lit 255#8)).eval σ = 1#1
  · have hc : σ.regs count.name 8 = 255#8 := by
      simpa [Reg.rd, Expr.eval] using hcond
    simp only [count] at hc
    intro _
    simp [Reg.rd, Reg.set, Act.run, Expr.eval,
      count, sat, RegEnv.set, hc]
  · have hc : σ.regs count.name 8 ≠ 255#8 := by
      intro heq
      apply hcond
      simp [Reg.rd, Expr.eval, heq]
    simp only [count] at hc
    intro hsat
    have hsat' : σ.regs sat.name 1 = 1#1 := by
      simpa [Reg.rd, Reg.set, Act.run, Expr.eval,
        count, sat, RegEnv.set, hcond, hc] using hsat
    exact absurd (hP hsat') hc

theorem satOkExpr_propertyStep (σ : St) :
    satOkExpr.eval σ = 1#1 →
      satOkExpr.eval (design.exprPropertyCycle satOkExpr σ) = 1#1 := by
  intro hP
  apply (satOkExpr_iff _).2
  change SatOk (design.propertyCycle satFootprint σ)
  exact satOk_propertyStep σ ((satOkExpr_iff σ).1 hP)

theorem satOkProperty_step (σ : St) :
    satOkProperty.eval σ →
      satOkProperty.eval (design.propertyExprCycle satOkProperty σ) := by
  intro hP
  apply (satOkProperty_iff _).2
  change SatOk (design.propertyCycle satFootprint σ)
  exact satOk_propertyStep σ ((satOkProperty_iff σ).1 hP)

/-- The real tutorial invariant through the expression-shaped API: its state
coordinates, support proof, and one-rule writer cone all come from
`satOkExpr.readSites`. -/
theorem satOkExpr_invariant :
    design.toTSys.Invariant (fun σ => satOkExpr.eval σ = 1#1) :=
  design.invariant_of_exprPropertyCycle satOkExpr
    (fun value => value = 1#1)
    (by
      apply (satOkExpr_iff _).2
      intro hsat
      simp [Design.reset, design, declarations, sat, RegEnv.set] at hsat)
    satOkExpr_propertyStep

/-- The same real invariant through propositionally composed atoms. -/
theorem satOkProperty_invariant : design.toTSys.Invariant satOkProperty.eval :=
  design.invariant_of_propertyExprCycle satOkProperty
    (by
      apply (satOkProperty_iff _).2
      intro hsat
      simp [Design.reset, design, declarations, sat, RegEnv.set] at hsat)
    satOkProperty_step

/-- The tutorial's real invariant, reproved through the generic reduced-cycle
combinator rather than by unfolding the full design transition. -/
theorem satOk_invariant_via_propertyCycle :
    design.toTSys.Invariant SatOk :=
  design.invariant_of_propertyCycle satFootprint SatOk satOk_supported
    (by
      intro hsat
      simp [Design.reset, design, declarations, sat, RegEnv.set] at hsat)
    satOk_propertyStep

end Tests.CycleSupport.Tutorial
