-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Hw.Declarations
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
open Loom.Hw.Notation

/-- The counter value. -/
def count : Reg 8 := ⟨"count"⟩
/-- The saturation flag. -/
def sat : Reg 1 := ⟨"sat"⟩

/-- Each cycle: once the counter reaches 255, raise the sticky flag;
otherwise keep counting. -/
def tick : Act :=
  ifA count.rd === 255 then
    sat ⇐ 1
  else
    count ⇐ count.rd + 1

/-- The complete state and external interface, declared from typed handles. -/
def declarations : Declarations :=
  Declarations.empty
    |>.addReg count (exported := true)
    |>.addReg sat (exported := true)

/-- The complete design. -/
def design : Design :=
  Design.ofDecls "satcounter" declarations [⟨"tick", tick⟩]

/-- The compiler's side conditions, discharged by its decision procedure. -/
theorem design_wf : Compile.DesignWF design :=
  Compile.designWFCheck_sound design (by decide)

/-- The property: the flag only rises at saturation. -/
def SatOk (σ : St) : Prop :=
  σ.regs sat.name 1 = 1#1 → σ.regs count.name 8 = 255#8

/-- `SatOk` holds in every reachable state of the model. -/
theorem satOk_invariant : design.toTSys.Invariant SatOk := by
  apply Loom.TSys.Inductive.invariant
  constructor
  · -- reset: the flag starts at zero
    intro s hinit
    simp only [Design.toTSys_init_iff] at hinit
    subst hinit
    intro hsat
    simp [Design.reset, design, declarations, sat, RegEnv.set] at hsat
  · -- step: one cycle preserves the property
    intro s s' hP hstep
    simp only [Design.toTSys_step_iff] at hstep
    subst hstep
    by_cases hc : s.regs count.name 8 = 255#8
    · -- saturated: the rule writes `sat`, leaves `count` unchanged
      simp only [count] at hc
      intro _
      simp [Design.cycle, design, declarations, tick, Reg.rd, Reg.set,
        Act.run, Expr.eval, count, sat, RegEnv.set, hc]
    · -- not saturated: the rule writes `count`, leaves `sat` unchanged
      simp only [count] at hc
      intro hsat
      have hsat' : s.regs sat.name 1 = 1#1 := by
        simpa [Design.cycle, design, declarations, tick, Reg.rd, Reg.set,
          Act.run, Expr.eval, count, sat, RegEnv.set, hc] using hsat
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
