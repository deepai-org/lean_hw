-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Hw.Semantics
import Loom.Hw.CompileCorrect
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO

/-!
# Tutorial design: a saturating counter

The worked example for `TUTORIAL.md`, built by following that document's
steps exactly. Two registers, one rule, one invariant, transported to the
compiled RTL and emitted as Verilog.
-/

namespace Machines.Tutorial.SatCounter

open Loom.Hw

/-- The counter value. -/
def count : Expr 8 := .reg 8 "count"
/-- The saturation flag. -/
def sat : Expr 1 := .reg 1 "sat"

/-- Each cycle: once the counter reaches 255, raise the sticky flag;
otherwise keep counting. -/
def tick : Act :=
  .ite (.eq count (.lit 255))
    (.write 1 "sat" (.lit 1))
    (.write 8 "count" (.add count (.lit 1)))

/-- The complete design. -/
def design : Design where
  name := "satcounter"
  regs := [⟨"count", 8, 0⟩, ⟨"sat", 1, 0⟩]
  mems := []
  rules := [⟨"tick", tick⟩]

/-- The compiler's side conditions, discharged by its decision procedure. -/
theorem design_wf : Compile.DesignWF design :=
  Compile.designWFCheck_sound design (by decide)

/-- The property: the flag only rises at saturation. -/
def SatOk (σ : St) : Prop :=
  σ.regs "sat" 1 = 1#1 → σ.regs "count" 8 = 255#8

/-- `SatOk` holds in every reachable state of the model. -/
theorem satOk_invariant : design.toTSys.Invariant SatOk := by
  apply Loom.TSys.Inductive.invariant
  constructor
  · -- reset: the flag starts at zero
    intro s hinit
    have : s = design.reset := hinit
    subst this
    intro hsat
    simp [Design.reset, design, RegEnv.set] at hsat
  · -- step: one cycle preserves the property
    intro s s' hP hstep
    have hcycle : design.cycle s = s' := hstep
    subst hcycle
    by_cases hc : s.regs "count" 8 = 255#8
    · -- saturated: the rule writes `sat`, leaves `count` unchanged
      intro _
      simp [Design.cycle, design, tick, Act.run, Expr.eval, count,
        RegEnv.set, hc]
    · -- not saturated: the rule writes `count`, leaves `sat` unchanged
      intro hsat
      have hsat' : s.regs "sat" 1 = 1#1 := by
        simpa [Design.cycle, design, tick, Act.run, Expr.eval, count, sat,
          RegEnv.set, hc] using hsat
      exact absurd (hP hsat') hc

/-- The same property, now of every reachable state of the compiled RTL. -/
theorem satOk_rtl :
    (Compile.compile design).toTSys.Invariant
      (fun state => SatOk (Compile.forgetSt state)) :=
  (Compile.simulation design design_wf).invariant_pullback satOk_invariant

end Machines.Tutorial.SatCounter

/-- Emit the Verilog (`lake env lean --run` needs a root-level `main`). -/
def main : IO Unit :=
  Machines.Tutorial.SatCounter.design.emit "rtl/satcounter.v"
