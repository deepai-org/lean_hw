-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Footprint

/-!
# Optional register-footprint coverage checks

This experimental release-checker layer is deliberately above the stable
action footprint API. Changes here must not invalidate the R-MC development,
which depends only on `Loom.Hw.Footprint`.
-/

namespace Loom.Hw

/-- Check that `covered` over-approximates the register writes in an action. -/
def Act.regWritesCoveredB (covered : List (String × Nat)) : Act → Bool
  | .skip => true
  | .seq left right =>
      left.regWritesCoveredB covered && right.regWritesCoveredB covered
  | .ite _ thenAction elseAction =>
      thenAction.regWritesCoveredB covered &&
        elseAction.regWritesCoveredB covered
  | .write width name _ => decide ((name, width) ∈ covered)
  | .memWrite .. => true

/-- A successful shared footprint check covers every syntactic register
write in the source action. -/
theorem Act.regWritesCoveredB_sound (covered : List (String × Nat)) :
    ∀ action : Act, action.regWritesCoveredB covered = true →
      ∀ key ∈ action.regWrites, key ∈ covered := by
  intro action
  induction action with
  | skip | memWrite => simp [Act.regWritesCoveredB, Act.regWrites]
  | seq left right leftIH rightIH | ite _ left right leftIH rightIH =>
      intro accepted key present
      simp only [Act.regWritesCoveredB, Bool.and_eq_true] at accepted
      simp only [Act.regWrites, List.mem_append] at present
      exact present.elim (leftIH accepted.1 key) (rightIH accepted.2 key)
  | write width name value =>
      intro accepted key present
      simp only [Act.regWrites, List.mem_singleton] at present
      subst key
      simpa [Act.regWritesCoveredB] using accepted

/-- If a key is absent from a checked over-approximation, the action cannot
write that key. -/
theorem Act.not_mem_regWrites_of_covered {covered : List (String × Nat)}
    {action : Act} (accepted : action.regWritesCoveredB covered = true)
    {key : String × Nat} (absent : key ∉ covered) :
    key ∉ action.regWrites := by
  intro present
  exact absent (Act.regWritesCoveredB_sound covered action accepted key present)

end Loom.Hw
