-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.CertifiedDesign
import Loom.Hw.Declarations

/-!
# Certified recovery coordinator cell

Large islands may have an arbitrary number of incident channels. The System
renderer folds their local completion levels through instances of this fixed
two-input cell, then uses one more instance to combine the resulting island
completion with global reset. No variable-arity handwritten Boolean
expression enters the structural text boundary.
-/

namespace Loom.Hw
namespace System.RecoveryCoordinator

def left : Reg 1 := ⟨"left"⟩
def right : Reg 1 := ⟨"right"⟩

def design : Design :=
  Design.ofDecls "system_recovery_coordinator_cell"
    (Declarations.empty
      |>.addInput left
      |>.addInput right
      |>.addCombOutput "and_out" (.and left.rd right.rd)
      |>.addCombOutput "or_out" (.or left.rd right.rd)) []

def compilerReady : Bool :=
  Compile.designWFCheck design && design.fastWFB

theorem compilerReady_true : compilerReady = true := by decide

def certified : CertifiedDesign design := by
  have checks := Bool.and_eq_true_iff.mp compilerReady_true
  exact CertifiedDesign.ofChecks checks.1 checks.2

/-- Executable meaning of the structural left-associated coordinator chain.
The renderer instantiates the certified two-input cell once per list member. -/
def fold (previous : Bool) : List Bool → Bool
  | [] => previous
  | done :: rest => fold (previous && done) rest

theorem fold_eq (previous : Bool) (done : List Bool) :
    fold previous done = (previous && done.all id) := by
  induction done generalizing previous with
  | nil => simp [fold]
  | cons head tail ih =>
      simp [fold, ih, Bool.and_assoc]

theorem fold_true_iff (previous : Bool) (done : List Bool) :
    fold previous done = true ↔
      previous = true ∧ ∀ value ∈ done, value = true := by
  rw [fold_eq, Bool.and_eq_true_iff]
  constructor
  · rintro ⟨request, allDone⟩
    exact ⟨request, List.all_eq_true.mp allDone⟩
  · rintro ⟨request, allDone⟩
    exact ⟨request, List.all_eq_true.mpr allDone⟩

/-- Truth-table facts consumed by the eventual whole-System refinement. -/
theorem and_semantics (a b : BitVec 1) (state : St) :
    (Expr.and left.rd right.rd).eval
      ((state.regs.set left.name a |>.set right.name b |> fun regs =>
        { state with regs := regs })) = a &&& b := by
  simp [Reg.rd, Expr.eval, left, right]

theorem or_semantics (a b : BitVec 1) (state : St) :
    (Expr.or left.rd right.rd).eval
      ((state.regs.set left.name a |>.set right.name b |> fun regs =>
        { state with regs := regs })) = a ||| b := by
  simp [Reg.rd, Expr.eval, left, right]

end System.RecoveryCoordinator
end Loom.Hw
