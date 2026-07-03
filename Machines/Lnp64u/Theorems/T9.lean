import Machines.Lnp64u.Logic.Wf
import Machines.Lnp64u.Logic.AcyclicWfa
import Machines.Lnp64u.Logic.Budget

/-!
# T9 — Conservation

Cap slots, lineage cells, and budget time are exactly accounted: the
lineage ledger balances (occupied cells = derived entries, a bijection via
`DomWf`), and budgets never exceed their manifest quota. Drop and revoke
restore precisely what was held — the counting form of the bijection.
-/

namespace Machines.Lnp64u.Theorems.T9

open Machines.Lnp64u Loom

/-- The boot ledger balances: no cells, no derived entries. -/
theorem init_balanced (m : Manifest) : LedgerBalanced m.initState := by
  intro d
  have h1 : cellCount (m.initState.doms d) = 0 := by
    simp [cellCount, Manifest.initState, Manifest.bootDom]
  have h2 : derivedCount (m.initState.doms d) = 0 := by
    rw [derivedCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro s _
    cases h : (m.initState.doms d).caps s with
    | none => simp [h]
    | some e =>
        have : e.lineage = none := by
          simp [Manifest.initState, Manifest.bootDom] at h
          obtain ⟨k, _, hk⟩ := h
          simp [← hk]
        simp [h, this]
  rw [h1, h2]

/-- **T9 (lineage ledger).** Cells and derived entries balance in every
reachable state. -/
theorem ledger_balanced (m : Manifest) (hwf : m.WF) :
    (machine m).Invariant LedgerBalanced :=
  fun s hr => LedgerBalanced_of_Wf s (wfa_invariant m hwf s hr).1

/-- **T9 (budget).** No domain's remaining budget ever exceeds its quota. -/
theorem budget_bounded (m : Manifest) (hwf : m.WF) :
    (machine m).Invariant
      (fun σ => ∀ d, (σ.doms d).budget ≤ (m.doms d).budgetQ) := by
  refine Loom.TSys.Inductive.invariant
    { init := fun σ hi d => ?_
      step := fun σ σ' hσ hstep d => ?_ }
  · subst hi
    simp [Manifest.initState, Manifest.bootDom]
  · have hst : step m σ = σ' := hstep
    exact hst ▸ Wip.step_budget_bounded m σ hσ d

end Machines.Lnp64u.Theorems.T9
