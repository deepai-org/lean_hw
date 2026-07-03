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

/-- Halting a domain (halt-base plus optional gate unwind) touches only
`run`/`cause`/`gates` — never `caps`/`lineage`. -/
theorem acyclic_haltDom (σ : MachineState) (d : DomainId) (cause : Loom.Word32)
    (hac : Acyclic σ) : Acyclic (σ.haltDom d cause) := by
  refine acyclic_of_parentRef_eq σ _ (parentRef_eq_of_doms σ _ (fun d' => ?_)) hac
  unfold MachineState.haltDom
  split
  · refine ⟨?_, ?_⟩ <;> simp
  · split
    · refine ⟨?_, ?_⟩ <;> simp
    · refine ⟨?_, ?_⟩ <;> simp

theorem acyclic_haltWith (σ : MachineState) (d : DomainId) (f : Fault)
    (hac : Acyclic σ) : Acyclic (haltWith σ d f) :=
  acyclic_haltDom σ d _ hac

/-- A `setDom` whose update leaves `caps`/`lineage` fixed preserves acyclicity —
already available as `acyclic_setDom`; specialized here for register writes. -/
theorem acyclic_setReg_dom (σ : MachineState) (d : DomainId) (r : RegId)
    (v : Loom.Word32) (hac : Acyclic σ) :
    Acyclic (σ.setDom d fun ds => ds.setReg r v) :=
  acyclic_setDom σ d _ (fun ds => by
    unfold DomainState.setReg; split <;> exact ⟨rfl, rfl⟩) hac

/-- **The `exec`-level acyclicity obligation** (companion to `ExecPreservesWf`):
every instruction's semantics preserves lineage acyclicity, given the state is
well-formed and acyclic. `Wf` is needed because `installDerived`'s fresh-leaf
argument uses `parent_live`. -/
def ExecPreservesAcyclic : Prop :=
  ∀ (instr : Instr), instr ∈ isa → ∀ (c : Ctx) (σ : MachineState),
    Wf σ → Acyclic σ → (σ.doms c.d).run = .running → σ.inflight = none →
    (∀ a σ', instr.sem.exec c σ = .ok a σ' → Acyclic σ') ∧
    (∀ e σ', instr.sem.exec c σ = .err e σ' → Acyclic σ')

end Machines.Lnp64u
