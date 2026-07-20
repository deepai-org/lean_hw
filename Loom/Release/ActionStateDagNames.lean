-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ActionStateDag
import Mathlib.Data.List.Nodup

/-!
# Register-name bridge for release composition

This small, non-hot-path module connects source-list name uniqueness to the
array-indexed premise used by action-DAG semantic projections. Keeping the
Mathlib list lemma out of `ActionStateDag` prevents every generated checker
worker from inheriting that dependency.
-/

namespace Loom.Release.Symbolic.ActionWide

open Loom.Hw

/-- A source register list with distinct names gives the array-indexed
uniqueness premise used by action-DAG semantic specialization. -/
theorem registerNamesUnique_toArray (registers : List RegDecl)
    (namesUnique : (registers.map (·.name)).Nodup) :
    RegisterNamesUnique registers.toArray := by
  intro left right leftReg rightReg leftFound rightFound namesEq
  rw [List.getElem?_toArray] at leftFound rightFound
  have leftBound : left < registers.length :=
    (getElem?_eq_some_iff.mp leftFound).1
  have rightBound : right < registers.length :=
    (getElem?_eq_some_iff.mp rightFound).1
  have leftValue : registers[left] = leftReg :=
    (getElem?_eq_some_iff.mp leftFound).2
  have rightValue : registers[right] = rightReg :=
    (getElem?_eq_some_iff.mp rightFound).2
  have leftNameBound : left < (registers.map (·.name)).length := by
    simpa using leftBound
  have rightNameBound : right < (registers.map (·.name)).length := by
    simpa using rightBound
  apply (namesUnique.getElem_inj_iff
    (i := left) (j := right) (hi := leftNameBound)
    (hj := rightNameBound)).mp
  erw [List.getElem_map, List.getElem_map]
  rw [leftValue, rightValue]
  exact namesEq

end Loom.Release.Symbolic.ActionWide
