import Machines.Lnp64u.Logic.Acyclic
import Machines.Lnp64u.Logic.ExecWf
import Machines.Lnp64u.Step

/-!
# Acyclicity is preserved by the non-`exec` phases (L1 support)

`refillPhase`, `moverPhase`, and the cycle bump touch only budgets, memory,
the Mover job, and the cycle counter — never a domain's `caps` or `lineage`
tables — so they preserve lineage acyclicity for free (`parentRef` is a
function of `caps`/`lineage` alone). This is the acyclicity companion to the
`Wf` phase lemmas, leaving only `corePhase` (the instruction effect).
-/

namespace Machines.Lnp64u

open Loom

/-- `refillPhase` only rewrites budgets, so `caps`/`lineage` are untouched. -/
theorem acyclic_refillPhase (m : Manifest) (σ : MachineState) (hac : Acyclic σ) :
    Acyclic (refillPhase m σ) := by
  refine acyclic_of_parentRef_eq σ _ (parentRef_eq_of_doms σ _ (fun d => ?_)) hac
  unfold refillPhase
  split
  · exact ⟨rfl, rfl⟩
  · simp only; split <;> exact ⟨rfl, rfl⟩

theorem acyclic_moverPhase (σ : MachineState) (hac : Acyclic σ) :
    Acyclic (moverPhase σ) :=
  acyclic_of_parentRef_eq σ _
    (parentRef_eq_of_doms σ _ (fun d => by simp [moverPhase_doms])) hac

/-- Bumping the cycle counter touches no domain. -/
theorem acyclic_setCycle (σ : MachineState) (n : Nat) (hac : Acyclic σ) :
    Acyclic { σ with cycle := n } :=
  acyclic_of_parentRef_eq σ _ (parentRef_eq_of_doms σ _ (fun _ => ⟨rfl, rfl⟩)) hac

end Machines.Lnp64u
