-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Frame
import Loom.Hw.Trees

/-!
# Two-bit action safety

A property cone may retain a large guarded action even after unrelated rules
are removed. This module supplies a tiny proved abstract interpreter for a pair
of distinct one-bit registers. Guards are nondeterministic; sequential writes
retain their order; literal one-bit values stay precise; other expressions are
conservatively either zero or one.

The result is a proof aid only. It neither rewrites a `Design` nor participates
in emission.
-/

namespace Loom.Hw
namespace PairSafety

/-- Abstract values of two one-bit registers, represented by their `toNat`s. -/
abbrev Pair := Nat × Nat

@[simp] private theorem bit_toNat_mem (value : BitVec 1) :
    value.toNat ∈ [0, 1] := by
  rcases bv1_cases value with rfl | rfl <;> simp

private theorem bit_toNat_cases (value : BitVec 1) :
    value.toNat = 0 ∨ value.toNat = 1 := by
  rcases bv1_cases value with rfl | rfl <;> simp

/-- Literal bits remain exact; every other bit expression is conservatively
zero or one. The width test makes the helper usable directly on `Act.write`. -/
def exprValues {width : Nat} (expr : Expr width) : List Nat :=
  if hwidth : width = 1 then
    match hwidth ▸ expr with
    | .lit value => [value.toNat]
    | _ => [0, 1]
  else []

theorem eval_toNat_mem_exprValues {width : Nat} (expr : Expr width)
    (hwidth : width = 1) (σ : St) :
    (expr.eval σ).toNat ∈ exprValues expr := by
  subst width
  cases expr
  · simp [exprValues, Expr.eval]
  all_goals
    change (Expr.eval σ _).toNat ∈ [0, 1]
    exact bit_toNat_mem _

/-- Abstract effect of one register write on the selected pair. -/
def writeOutcomes (left right : String) {width : Nat}
    (name : String) (value : Expr width) (input : Pair) : List Pair :=
  if _hwidth : width = 1 then
    if name = left then
      (exprValues value).map fun bit => (bit, input.2)
    else if name = right then
      (exprValues value).map fun bit => (input.1, bit)
    else [input]
  else [input]

/-- Every possible selected-pair result of an action. Conditions are explored
nondeterministically, so the result over-approximates every concrete run. -/
def outcomes (left right : String) : Act → Pair → List Pair
  | .skip, input => [input]
  | .seq first second, input =>
      (outcomes left right first input).flatMap
        (outcomes left right second)
  | .ite _ thenAction elseAction, input =>
      outcomes left right thenAction input ++
        outcomes left right elseAction input
  | .write _ name value, input => writeOutcomes left right name value input
  | .memWrite .., input => [input]

/-- Concrete selected-pair observation. -/
def observe (left right : String) (σ : St) : Pair :=
  ((σ.regs left 1).toNat, (σ.regs right 1).toNat)

/-- Soundness of the action abstraction. -/
theorem observe_run_mem_outcomes (left right : String) (distinct : left ≠ right) :
    ∀ (action : Act) (σ acc : St),
      observe left right (action.run σ acc) ∈
        outcomes left right action (observe left right acc) := by
  intro action
  induction action with
  | skip => intro σ acc; simp [outcomes, observe, Act.run]
  | seq first second ihFirst ihSecond =>
      intro σ acc
      simp only [Act.run, outcomes, List.mem_flatMap]
      exact ⟨observe left right (first.run σ acc),
        ihFirst σ acc, ihSecond σ (first.run σ acc)⟩
  | ite guard thenAction elseAction ihThen ihElse =>
      intro σ acc
      by_cases hguard : guard.eval σ = 1#1
      · simp [Act.run, outcomes, hguard, ihThen σ acc]
      · simp [Act.run, outcomes, hguard, ihElse σ acc]
  | write width name value =>
      intro σ acc
      by_cases hwidth : width = 1
      · subst width
        by_cases hleft : name = left
        · subst name
          simp [Act.run, outcomes, writeOutcomes, observe, RegEnv.set,
            Ne.symm distinct, eval_toNat_mem_exprValues]
        · by_cases hright : name = right
          · subst name
            simp [Act.run, outcomes, writeOutcomes, observe, RegEnv.set,
              hleft, Ne.symm hleft, eval_toNat_mem_exprValues]
          · simp [Act.run, outcomes, writeOutcomes, observe, RegEnv.set,
              hleft, hright, Ne.symm hleft, Ne.symm hright]
      · simp [Act.run, outcomes, writeOutcomes, observe, RegEnv.set, hwidth]
  | memWrite => intro σ acc; simp [Act.run, outcomes, observe]

/-- The pair excludes simultaneous one values. -/
def Exclusive (pair : Pair) : Prop := pair.1 = 0 ∨ pair.2 = 0

def exclusiveB (pair : Pair) : Bool := pair.1 == 0 || pair.2 == 0

def exclusiveInputs : List Pair := [(0, 0), (0, 1), (1, 0)]

/-- Executable certificate: every abstract result from every exclusive input
remains exclusive. -/
def preservesExclusiveB (left right : String) (action : Act) : Bool :=
  exclusiveInputs.all fun input =>
    (outcomes left right action input).all exclusiveB

private theorem observe_mem_exclusiveInputs (left right : String) (σ : St)
    (exclusive : Exclusive (observe left right σ)) :
    observe left right σ ∈ exclusiveInputs := by
  rcases bv1_cases (σ.regs left 1) with hl | hl <;>
    rcases bv1_cases (σ.regs right 1) with hr | hr <;>
    simp [observe, exclusiveInputs, hl, hr, Exclusive] at exclusive ⊢

/-- A successful executable certificate proves preservation for `Act.run`. -/
theorem preservesExclusiveB_sound (left right : String) (distinct : left ≠ right)
    (action : Act) (accepted : preservesExclusiveB left right action = true)
    (σ acc : St) (inputExclusive : Exclusive (observe left right acc)) :
    Exclusive (observe left right (action.run σ acc)) := by
  have inputMem := observe_mem_exclusiveInputs left right acc inputExclusive
  have concreteMem := observe_run_mem_outcomes left right distinct action σ acc
  simp only [preservesExclusiveB, List.all_eq_true] at accepted
  have outputsAccepted := accepted _ inputMem
  have concreteAccepted := outputsAccepted _ concreteMem
  simpa [exclusiveB, Exclusive, Bool.or_eq_true, beq_iff_eq] using concreteAccepted

end PairSafety
end Loom.Hw
