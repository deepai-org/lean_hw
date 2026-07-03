import Machines.Lnp64u.Logic.AcyclicPhase
import Machines.Lnp64u.Logic.BaseOpsWf

/-!
# `SpecM` computations that preserve acyclicity (L1 support for ExecPreservesAcyclic)

The acyclicity companion to `PreservesWf`: the base ALU/branch/memory opcodes'
`exec` are compositions of `reg`/`setReg`/`load`/`store`/`updDomPc`, none of
which touch a domain's `caps` or `lineage` tables, so each preserves lineage
acyclicity. This discharges the base half of `ExecPreservesAcyclic`, reducing it
to the eleven system opcodes — exactly parallel to `BaseOpsWf`.
-/

namespace Machines.Lnp64u

open Loom.Isa SpecM Machines.Lnp64u.Isa

/-- A `SpecM` computation preserves lineage acyclicity. -/
def PreservesAcyclic {α : Type} (m : SpecM α) : Prop :=
  ∀ σ, Acyclic σ →
    (∀ a σ', m σ = .ok a σ' → Acyclic σ') ∧
    (∀ e σ', m σ = .err e σ' → Acyclic σ')

/-- A read-only computation (state unchanged on every outcome) preserves it. -/
theorem PreservesAcyclic.of_readOnly {α : Type} (m : SpecM α)
    (hok : ∀ σ a σ', m σ = .ok a σ' → σ' = σ)
    (herr : ∀ σ e σ', m σ = .err e σ' → σ' = σ) : PreservesAcyclic m :=
  fun σ hac => ⟨fun a σ' he => (hok σ a σ' he) ▸ hac, fun e σ' he => (herr σ e σ' he) ▸ hac⟩

theorem PreservesAcyclic.pure {α : Type} (a : α) : PreservesAcyclic (Pure.pure a : SpecM α) :=
  PreservesAcyclic.of_readOnly _
    (fun σ a' σ' he => by rw [specM_pure] at he; injection he with _ h2; exact h2.symm)
    (fun σ e σ' he => by rw [specM_pure] at he; simp at he)

theorem PreservesAcyclic.bind {α β : Type} {m : SpecM α} {f : α → SpecM β}
    (hm : PreservesAcyclic m) (hf : ∀ a, PreservesAcyclic (f a)) :
    PreservesAcyclic (m >>= f) := by
  intro σ hac
  refine ⟨?_, ?_⟩
  · intro b σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he; exact (hf a σ1 ((hm σ hac).1 a σ1 hmσ)).1 b σ' he
    | err e σ1 => rw [hmσ] at he; simp at he
    | fault f => rw [hmσ] at he; simp at he
  · intro e σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he; exact (hf a σ1 ((hm σ hac).1 a σ1 hmσ)).2 e σ' he
    | err e1 σ1 => rw [hmσ] at he; injection he with h1 h2; subst h2; exact (hm σ hac).2 e1 σ1 hmσ
    | fault f => rw [hmσ] at he; simp at he

theorem PreservesAcyclic.iteBool {α : Type} (b : Bool) {m1 m2 : SpecM α}
    (h1 : PreservesAcyclic m1) (h2 : PreservesAcyclic m2) :
    PreservesAcyclic (if b then m1 else m2) := by
  cases b <;> simp only [Bool.false_eq_true, if_true, if_false]
  · exact h2
  · exact h1

theorem PreservesAcyclic.reg (d : DomainId) (r : RegId) : PreservesAcyclic (SpecM.reg d r) :=
  PreservesAcyclic.of_readOnly _
    (fun σ a σ' he => by unfold SpecM.reg at he; injection he with _ h2; exact h2.symm)
    (fun σ e σ' he => by unfold SpecM.reg at he; simp at he)

theorem PreservesAcyclic.raise {α : Type} (e : Errno) :
    PreservesAcyclic (SpecM.raise e : SpecM α) :=
  PreservesAcyclic.of_readOnly _
    (fun σ a σ' he => by unfold SpecM.raise at he; simp at he)
    (fun σ e' σ' he => by unfold SpecM.raise at he; injection he with _ h2; exact h2.symm)

theorem PreservesAcyclic.require (cond : Bool) (e : Errno) :
    PreservesAcyclic (SpecM.require cond e) :=
  PreservesAcyclic.of_readOnly _
    (fun σ a σ' he => require_ok cond e σ he)
    (fun σ e' σ' he => require_err_state cond e σ he)

theorem PreservesAcyclic.load (d : DomainId) (a : Addr) : PreservesAcyclic (SpecM.load d a) :=
  PreservesAcyclic.of_readOnly _
    (fun σ v σ' he => load_ok d a σ he)
    (fun σ e σ' he => load_err_state d a σ he)

theorem PreservesAcyclic.setReg (d : DomainId) (r : RegId) (v : Loom.Word32) :
    PreservesAcyclic (SpecM.setReg d r v) := by
  intro σ hac
  refine ⟨?_, ?_⟩
  · intro a σ' he
    unfold SpecM.setReg SpecM.modify at he; injection he with _ h2; subst h2
    exact acyclic_setReg_dom σ d r v hac
  · intro e σ' he; unfold SpecM.setReg SpecM.modify at he; simp at he

theorem PreservesAcyclic.updDomPc (d : DomainId) (k : DomainState → Addr) :
    PreservesAcyclic (SpecM.updDom d (fun ds => { ds with pc := k ds })) := by
  intro σ hac
  refine ⟨?_, ?_⟩
  · intro a σ' he
    simp only [SpecM.updDom, SpecM.modify] at he; injection he with _ h2; subst h2
    exact acyclic_setDom σ d _ (fun ds => ⟨rfl, rfl⟩) hac
  · intro e σ' he; simp [SpecM.updDom, SpecM.modify] at he

theorem PreservesAcyclic.store (d : DomainId) (a : Addr) (v : Loom.Word32) :
    PreservesAcyclic (SpecM.store d a v) := by
  intro σ hac
  unfold SpecM.store
  refine ⟨?_, ?_⟩
  · intro x σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp only [SpecM.demand, hc, if_true, specM_pure, specM_bind, SpecM.set] at he
      injection he with _ h2; subst h2; exact acyclic_write σ a v hac
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he
  · intro e σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp [SpecM.demand, hc, specM_pure, specM_bind, SpecM.set] at he
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he

/-- **The base opcodes preserve acyclicity.** Every declaration in `Isa.base`
preserves lineage acyclicity — its `exec` never touches `caps`/`lineage`. -/
theorem base_preserves_acyclic : ∀ instr ∈ base, ∀ c : Ctx,
    PreservesAcyclic (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  · exact PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.setReg _ _ _))
  · exact PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.setReg _ _ _))
  · exact PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.setReg _ _ _))
  · exact PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.setReg _ _ _))
  · exact PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.setReg _ _ _))
  · exact PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.setReg _ _ _))
  · exact PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.setReg _ _ _))
  · exact PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.setReg _ _ _)
  · exact PreservesAcyclic.setReg _ _ _
  · exact PreservesAcyclic.bind (PreservesAcyclic.reg _ _)
      (fun _ => PreservesAcyclic.bind (PreservesAcyclic.load _ _) (fun _ => PreservesAcyclic.setReg _ _ _))
  · exact PreservesAcyclic.bind (PreservesAcyclic.reg _ _)
      (fun _ => PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.store _ _ _))
  · exact PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.iteBool _ (PreservesAcyclic.updDomPc _ _) (PreservesAcyclic.pure ())))
  · exact PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.bind (PreservesAcyclic.reg _ _) (fun _ => PreservesAcyclic.iteBool _ (PreservesAcyclic.updDomPc _ _) (PreservesAcyclic.pure ())))
  · exact PreservesAcyclic.bind (PreservesAcyclic.reg _ _)
      (fun _ => PreservesAcyclic.bind (PreservesAcyclic.setReg _ _ _)
        (fun _ => PreservesAcyclic.updDomPc _ _))

/-- The remaining acyclicity obligation: the eleven system opcodes preserve
acyclicity, given `Wf` (for `installDerived`'s fresh-leaf argument). Companion
to `SystemOpsPreserveWf`. -/
def SystemOpsPreserveAcyclic : Prop :=
  ∀ instr ∈ Machines.Lnp64u.Isa.system, ∀ (c : Ctx) (σ : MachineState),
    Wf σ → Acyclic σ → (σ.doms c.d).run = .running → σ.inflight = none →
    (∀ a σ', instr.sem.exec c σ = .ok a σ' → Acyclic σ') ∧
    (∀ e σ', instr.sem.exec c σ = .err e σ' → Acyclic σ')

/-- `ExecPreservesAcyclic` follows from base-op preservation plus the system-op
obligation — exactly parallel to `execPreservesWf_of_system`. -/
theorem execPreservesAcyclic_of_system (hsys : SystemOpsPreserveAcyclic) :
    ExecPreservesAcyclic := by
  intro instr hmem c σ hwf hac _ _
  have hmem' : instr ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
    have hiseq : Machines.Lnp64u.isa =
      (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray := rfl
    rw [hiseq, Array.mem_toArray] at hmem; exact hmem
  rcases List.mem_append.mp hmem' with hb | hsys'
  · exact ⟨fun a σ' he => (base_preserves_acyclic instr hb c σ hac).1 a σ' he,
           fun e σ' he => (base_preserves_acyclic instr hb c σ hac).2 e σ' he⟩
  · exact hsys instr hsys' c σ hwf hac ‹_› ‹_›

/-- Any `updDom` whose update leaves `caps`/`lineage` fixed preserves acyclicity. -/
theorem PreservesAcyclic.updDom (d : DomainId) (f : DomainState → DomainState)
    (hf : ∀ ds, (f ds).caps = ds.caps ∧ (f ds).lineage = ds.lineage) :
    PreservesAcyclic (SpecM.updDom d f) := by
  intro σ hac
  refine ⟨?_, ?_⟩
  · intro a σ' he; simp only [SpecM.updDom, SpecM.modify] at he; injection he with _ h2; subst h2
    exact acyclic_setDom σ d f hf hac
  · intro e σ' he; simp [SpecM.updDom, SpecM.modify] at he

end Machines.Lnp64u
