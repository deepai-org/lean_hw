-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Hw.Semantics
import Loom.Hw.CompileCorrect
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO

namespace Machines.PingPong

open Loom.Hw

/-- Two stations pass a single token back and forth every cycle;
a saturating counter records handoffs. -/
def a : Expr 1 := .reg 1 "a"
def b : Expr 1 := .reg 1 "b"
def hops : Expr 8 := .reg 8 "hops"

def swap : Act :=
  .seq (.write 1 "a" b) (.write 1 "b" a)

def countHops : Act :=
  .ite (.eq hops (.lit 255))
    .skip
    (.write 8 "hops" (.add hops (.lit 1)))

def design : Design where
  name := "pingpong"
  regs := [⟨"a", 1, 1⟩, ⟨"b", 1, 0⟩, ⟨"hops", 8, 0⟩]
  mems := []
  rules := [⟨"swap", swap⟩, ⟨"count", countHops⟩]

theorem design_wf : Compile.DesignWF design :=
  Compile.designWFCheck_sound design (by decide)

/-- Exactly one station holds the token. -/
def OneHot (σ : St) : Prop :=
  σ.regs "a" 1 ≠ σ.regs "b" 1

theorem oneHot_invariant : design.toTSys.Invariant OneHot := by
  apply Loom.TSys.Inductive.invariant
  constructor
  · intro s hinit
    simp only [Design.toTSys_init_iff] at hinit
    subst hinit
    simp [OneHot, Design.reset, design, RegEnv.set]
  · intro s s' hP hstep
    simp only [Design.toTSys_step_iff] at hstep
    subst hstep
    by_cases hc : s.regs "hops" 8 = 255#8 <;>
      simpa [OneHot, Design.cycle, design, swap, countHops, Act.run,
        Expr.eval, a, b, hops, RegEnv.set, hc, ne_comm] using hP

/-- The one-hot property holds in every reachable state of the compiled RTL. -/
theorem oneHot_rtl :
    (Compile.compile design).toTSys.Invariant
      (fun state => OneHot (Compile.forgetSt state)) :=
  (Compile.simulation design design_wf).invariant_pullback oneHot_invariant

#print axioms oneHot_rtl

end Machines.PingPong

/-- Emit the Verilog (`lake env lean --run` needs a root-level `main`). -/
def main : IO Unit :=
  Machines.PingPong.design.emit "rtl/pingpong.v"
