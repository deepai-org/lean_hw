import Machines.Acc8.Core

/-!
# A-R — the Acc8 core refines the Acc8 spec

The pathfinder refinement: one core cycle is exactly one spec step through
`Core.abs`. Exercises the `Simulation` spine end to end before LNP64-µ's
multicycle proof (R-MC) needs it.
-/

namespace Machines.Acc8.Theorems.AR

open Machines.Acc8 Loom

/-- The commuting square: a core cycle simulates a spec step. -/
theorem square (σ : Loom.Hw.St) :
    Core.abs ((Core.design (Core.abs σ).prog).cycle σ) = step (Core.abs σ) := by
  sorry

/-- **A-R.** The core refines the spec. -/
theorem refines (prog : BitVec 8 → BitVec 16) :
    Nonempty (Simulation (machine prog) (Core.design prog).toTSys) := by
  sorry

end Machines.Acc8.Theorems.AR
