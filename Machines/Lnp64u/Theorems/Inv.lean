import Machines.Lnp64u.Logic.Wf

/-!
# The workhorse: machine well-formedness is invariant

Everything in the Phase-1 ladder either strengthens `Wf` or is its
corollary. Proof strategy (µLog DESIGN.md): show `Wf` inductive over
`step`'s phases, then per-instruction preservation lemmas, one kernel
function at a time.
-/

namespace Machines.Lnp64u.Theorems.Inv

open Machines.Lnp64u Loom

/-- Boot states are well-formed. -/
theorem init_wf (m : Manifest) (hwf : m.WF) : Wf m.initState := by
  sorry

/-- `Wf` is preserved by one cycle. -/
theorem step_wf (m : Manifest) (hwf : m.WF) (σ : MachineState)
    (h : Wf σ) : Wf (step m σ) := by
  sorry

/-- The invariant. -/
theorem wf_invariant (m : Manifest) (hwf : m.WF) :
    (machine m).Invariant Wf :=
  (TSys.Inductive.invariant
    { init := fun σ h => h ▸ init_wf m hwf
      step := fun σ σ' hσ hstep => by
        have : step m σ = σ' := hstep
        exact this ▸ step_wf m hwf σ hσ })

end Machines.Lnp64u.Theorems.Inv
