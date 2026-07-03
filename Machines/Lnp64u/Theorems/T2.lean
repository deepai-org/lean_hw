import Machines.Lnp64u.Logic.Wf
import Machines.Lnp64u.Logic.Authority

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
  intro d s e' hc
  obtain ⟨d0, s0, e0, h0, hle⟩ := Wip.step_dominated m σ d s e' hc
  obtain ⟨dr, sr, k0, hr, hler⟩ := h d0 s0 e0 h0
  exact ⟨dr, sr, k0, hr, CapKind.le_trans hle hler⟩

/-- **T2.** Authority confinement over all reachable states. -/
theorem authority_confined (m : Manifest) (hwf : m.WF) :
    (machine m).Invariant
      (fun σ => Wf σ ∧ AuthorityConfined m σ) := by
  have hexec := execPreservesWfA_of_system Machines.Lnp64u.Isa.Wip.system_preserves_wfa
  refine Loom.TSys.invariant_of_inductive_of_imp
    (Q := fun σ => (Wf σ ∧ Acyclic σ) ∧ AuthorityConfined m σ)
    ?_ (fun σ hq => ⟨hq.1.1, hq.2⟩)
  exact
    { init := fun σ hi =>
        ⟨⟨hi ▸ Machines.Lnp64u.Theorems.Inv.init_wf m hwf, hi ▸ init_acyclic m⟩,
         hi ▸ init_confined m⟩
      step := fun σ σ' hσ hstep => by
        have hst : step m σ = σ' := hstep
        exact hst ▸ ⟨step_wfa hexec m hwf σ hσ.1.1 hσ.1.2,
                     step_confined m hwf σ hσ.1.1 hσ.2⟩ }

end Machines.Lnp64u.Theorems.T2
