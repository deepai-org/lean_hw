-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Logic.AcyclicPhase
import Machines.Lnp64u.Theorems.Inv

/-!
# The combined `Wf ∧ Acyclic` invariant (L1)

The workhorse invariant strengthened with lineage acyclicity. `Wf` alone is not
inductive for the revocation opcodes (`cap_drop` and friends): their preservation
proofs need to know the lineage forest has no cycles. This file threads the two
together into one inductive predicate, reducing the whole to the two exec-level
obligations `ExecPreservesWf` and `ExecPreservesAcyclic`.
-/

namespace Machines.Lnp64u.Theorems.Inv

open Machines.Lnp64u Loom

/-- **The combined invariant.** `Wf σ ∧ Acyclic σ` holds in every reachable
state, reduced to the two exec-level obligations. `Acyclic` closes the gap that
made `Wf` alone non-inductive for the capability-revocation opcodes. -/
theorem wfa_invariant (hexecwf : ExecPreservesWf) (hexecac : ExecPreservesAcyclic)
    (m : Manifest) (hwf : m.WF) :
    (machine m).Invariant (fun σ => Wf σ ∧ Acyclic σ) :=
  (TSys.Inductive.invariant
    { init := fun σ h => ⟨h ▸ init_wf m hwf, h ▸ init_acyclic m⟩
      step := fun σ σ' hσ hstep => by
        have hst : step m σ = σ' := hstep
        exact hst ▸ ⟨step_wf hexecwf m hwf σ hσ.1, acyclic_step hexecac m σ hσ.1 hσ.2⟩ })

end Machines.Lnp64u.Theorems.Inv
