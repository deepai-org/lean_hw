-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Tutorial.SatCounter

/-!
# Typed-declaration migration regression

The tutorial is the first existing design migrated to typed handles and
`Declarations`.  This test pins the new authoring form to the exact previous
core `Design`, including action elaboration and interface policy.  Equality of
the source value also makes every derived semantic and compiled view equal.
-/

namespace Tests.TutorialDeclarations

open Loom.Hw

private def legacyTick : Act :=
  .ite (.eq (.reg 8 "count") (.lit 255))
    (.write 1 "sat" (.lit 1))
    (.write 8 "count" (.add (.reg 8 "count") (.lit 1)))

private def legacyDesign : Design where
  name := "satcounter"
  regs := [⟨"count", 8, 0⟩, ⟨"sat", 1, 0⟩]
  mems := []
  rules := [⟨"tick", legacyTick⟩]
  outputs := ["count", "sat"]

/-- The migration changes authoring only, not the core design value. -/
theorem design_eq_legacy :
    Machines.Tutorial.SatCounter.design = legacyDesign := rfl

/-- Consequently the compiler receives exactly the same value. -/
theorem compiled_eq_legacy :
    Compile.compile Machines.Tutorial.SatCounter.design =
      Compile.compile legacyDesign :=
  congrArg Compile.compile design_eq_legacy

end Tests.TutorialDeclarations
