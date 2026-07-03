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

/-- `retire` preserves acyclicity, reduced to `ExecPreservesAcyclic`. Mirrors
`retire_preserves_wf`: decode-failure and fault paths halt (acyclicity-neutral),
the pc bump preserves caps/lineage, and the instruction effect is the obligation.
`Wf σ` is needed to run the exec obligation (which itself needs `Wf`). -/
theorem retire_preserves_acyclic (hexec : ExecPreservesAcyclic) (σ : MachineState)
    (d : DomainId) (w : Loom.Word32) (hwf : Wf σ) (hac : Acyclic σ)
    (hdrun : (σ.doms d).run = .running) (hinf : σ.inflight = none) :
    Acyclic (retire σ d w) := by
  unfold retire
  split
  · exact acyclic_haltWith σ d .illegalInstruction hac
  · rename_i instr hdec
    have hpcproj : ∀ (d' : DomainId),
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').caps = (σ.doms d').caps) ∧
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').lineage = (σ.doms d').lineage) ∧
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').slotGen = (σ.doms d').slotGen) ∧
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').regions = (σ.doms d').regions) ∧
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').run = (σ.doms d').run) ∧
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').serving = (σ.doms d').serving) := by
      intro d'; unfold MachineState.setDom
      by_cases hp : d' = d
      · subst hp; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hp]
    set σ1 := σ.setDom d (fun ds => { ds with pc := ds.pc + 1 }) with hσ1
    have hσ1wf : Wf σ1 := by
      refine wf_of_skeleton_sameGates σ σ1
        (fun d' => (hpcproj d').1) (fun d' => (hpcproj d').2.1) (fun d' => (hpcproj d').2.2.1)
        (fun d' => (hpcproj d').2.2.2.1) (fun d' => (hpcproj d').2.2.2.2.1)
        (fun d' => (hpcproj d').2.2.2.2.2) rfl rfl ?_ hwf
      intro fl' hfl'; rw [show σ1.inflight = σ.inflight from rfl, hinf] at hfl'
      exact absurd hfl' (by simp)
    have hσ1ac : Acyclic σ1 := acyclic_setDom σ d _ (fun ds => ⟨rfl, rfl⟩) hac
    have hσ1run : (σ1.doms d).run = .running := by rw [(hpcproj d).2.2.2.2.1]; exact hdrun
    have hmem : instr ∈ isa := Loom.Isa.decode_mem isa hdec
    obtain ⟨hok, herr⟩ := hexec instr hmem { d := d, pc := (σ.doms d).pc, op := operandsOf w }
      σ1 hσ1wf hσ1ac hσ1run hinf
    show Acyclic (match instr.sem.exec { d := d, pc := (σ.doms d).pc, op := operandsOf w } σ1 with
      | .ok _ σ' => σ'
      | .err e σ' => σ'.setDom d (fun ds => ds.setReg (operandsOf w).rd e.toWord)
      | .fault f => haltWith σ d f)
    cases hexr : instr.sem.exec { d := d, pc := (σ.doms d).pc, op := operandsOf w } σ1 with
    | ok a σ' => simp only [hexr]; exact hok a σ' hexr
    | err e σ' => simp only [hexr]; exact acyclic_setReg_dom σ' d _ _ (herr e σ' hexr)
    | fault f => simp only [hexr]; exact acyclic_haltWith σ d f hac

end Machines.Lnp64u
