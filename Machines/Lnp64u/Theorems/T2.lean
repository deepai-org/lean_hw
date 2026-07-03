import Machines.Lnp64u.Logic.Wf

/-!
# T2 — Authority confinement (invariant form)

The authority of every reachable state lies within the downward closure of
the manifest roots under dup-narrow, grant-subrange, gate-transfer, drop,
and revoke. Upgraded to the adversarial logical-relation form (T2′) in
Phase 3.
-/

namespace Machines.Lnp64u.Theorems.T2

open Machines.Lnp64u Loom

/-- Boot authority is exactly the manifest roots (each root dominates
itself). -/
theorem init_confined (m : Manifest) : AuthorityConfined m m.initState := by
  intro d s e h
  simp only [Manifest.initState, Manifest.bootDom, Option.map_eq_some_iff] at h
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨d, s, k, hk, CapKind.le_refl k⟩

/-- One-cycle preservation: every capability creation (dup, grant) derives
from a live parent, which the induction hypothesis places under a root;
transfer moves kinds unchanged; drop/revoke only remove. -/
theorem step_confined (m : Manifest) (hwf : m.WF) (σ : MachineState)
    (hσwf : Wf σ) (h : AuthorityConfined m σ) :
    AuthorityConfined m (step m σ) := by
  sorry

/-- **T2.** Authority confinement over all reachable states. -/
theorem authority_confined (m : Manifest) (hwf : m.WF) :
    (machine m).Invariant
      (fun σ => Wf σ ∧ AuthorityConfined m σ) := by
  sorry

end Machines.Lnp64u.Theorems.T2
