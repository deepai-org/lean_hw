import Machines.Lnp64u.SpecM
import Machines.Lnp64u.Isa.System
import Machines.Lnp64u.Logic.Wf
import Machines.Lnp64u.Logic.PhaseLemmas
import Machines.Lnp64u.Logic.Acyclic

/-!
# `SpecM` computations that preserve the invariant (L1 support for ExecPreservesWf)

`ExecPreservesWf` says every instruction's semantics preserves `Wf`. This file
builds the compositional framework: `PreservesWf m` for a `SpecM` computation,
closed under `pure`/`bind`, and established for the read-only and register-write
primitives. Base ALU/branch/memory instructions are built entirely from these,
so their `exec` preserves `Wf` by construction — reducing `ExecPreservesWf` to
the eleven system opcodes (the capability-kernel operations).
-/

namespace Machines.Lnp64u

open Loom

/-- Definitional unfoldings of the `SpecM` monad operations. -/
@[simp] theorem specM_pure {α : Type} (a : α) (σ : MachineState) :
    (Pure.pure a : SpecM α) σ = .ok a σ := rfl
@[simp] theorem specM_bind {α β : Type} (m : SpecM α) (f : α → SpecM β) (σ : MachineState) :
    (m >>= f) σ = (match m σ with
      | .ok a σ' => f a σ' | .err e σ' => .err e σ' | .fault g => .fault g) := rfl

/-- A `SpecM` computation preserves the invariant: from a well-formed state
with no in-flight instruction, every `ok`/`err` outcome is well-formed (and
still has no in-flight instruction, since instruction semantics never touch
the pipeline register). -/
def PreservesWf {α : Type} (m : SpecM α) : Prop :=
  ∀ σ, Wf σ → σ.inflight = none →
    (∀ a σ', m σ = .ok a σ' → Wf σ' ∧ σ'.inflight = none) ∧
    (∀ e σ', m σ = .err e σ' → Wf σ' ∧ σ'.inflight = none)

theorem PreservesWf.pure {α : Type} (a : α) : PreservesWf (Pure.pure a : SpecM α) := by
  intro σ hwf hinf
  refine ⟨?_, ?_⟩
  · intro a' σ' he; rw [specM_pure] at he
    injection he with h1 h2; exact ⟨h2 ▸ hwf, h2 ▸ hinf⟩
  · intro e σ' he; rw [specM_pure] at he; simp at he

theorem PreservesWf.bind {α β : Type} {m : SpecM α} {f : α → SpecM β}
    (hm : PreservesWf m) (hf : ∀ a, PreservesWf (f a)) : PreservesWf (m >>= f) := by
  intro σ hwf hinf
  refine ⟨?_, ?_⟩
  · intro b σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 =>
        rw [hmσ] at he
        obtain ⟨hwf1, hinf1⟩ := (hm σ hwf hinf).1 a σ1 hmσ
        exact (hf a σ1 hwf1 hinf1).1 b σ' he
    | err e σ1 => rw [hmσ] at he; simp at he
    | fault f => rw [hmσ] at he; simp at he
  · intro e σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 =>
        rw [hmσ] at he
        obtain ⟨hwf1, hinf1⟩ := (hm σ hwf hinf).1 a σ1 hmσ
        exact (hf a σ1 hwf1 hinf1).2 e σ' he
    | err e1 σ1 =>
        rw [hmσ] at he; injection he with h1 h2; subst h2
        exact (hm σ hwf hinf).2 e1 σ1 hmσ
    | fault f => rw [hmσ] at he; simp at he

theorem PreservesWf.get : PreservesWf SpecM.get := by
  intro σ hwf hinf
  refine ⟨?_, ?_⟩
  · intro a σ' he; simp only [SpecM.get] at he; injection he with h1 h2
    exact ⟨h2 ▸ hwf, h2 ▸ hinf⟩
  · intro e σ' he; simp [SpecM.get] at he

theorem PreservesWf.reg (d : DomainId) (r : RegId) : PreservesWf (SpecM.reg d r) := by
  intro σ hwf hinf
  refine ⟨?_, ?_⟩
  · intro a σ' he; simp only [SpecM.reg] at he; injection he with h1 h2
    exact ⟨h2 ▸ hwf, h2 ▸ hinf⟩
  · intro e σ' he; simp [SpecM.reg] at he

theorem PreservesWf.setReg (d : DomainId) (r : RegId) (v : Loom.Word32) :
    PreservesWf (SpecM.setReg d r v) := by
  intro σ hwf hinf
  refine ⟨?_, ?_⟩
  · intro a σ' he
    simp only [SpecM.setReg, SpecM.modify] at he; injection he with h1 h2
    subst h2
    exact ⟨wf_setReg σ d r v hwf, hinf⟩
  · intro e σ' he; simp [SpecM.setReg, SpecM.modify] at he

theorem PreservesWf.raise {α : Type} (e : Errno) : PreservesWf (SpecM.raise e : SpecM α) := by
  intro σ hwf hinf
  refine ⟨?_, ?_⟩
  · intro a σ' he; simp [SpecM.raise] at he
  · intro e' σ' he; simp only [SpecM.raise] at he; injection he with h1 h2
    exact ⟨h2 ▸ hwf, h2 ▸ hinf⟩

theorem PreservesWf.require (cond : Bool) (e : Errno) :
    PreservesWf (SpecM.require cond e) := by
  unfold SpecM.require; split
  · exact PreservesWf.pure ()
  · exact PreservesWf.raise e


/-- Writing memory preserves `Wf` — `mem` is not read by `Wf`. -/
theorem wf_write (σ : MachineState) (a : Addr) (v : Loom.Word32) (h : Wf σ) :
    Wf (σ.write a v) :=
  wf_of_skeleton_sameGates σ (σ.write a v)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl rfl (fun fl hfl => h.inflight_running fl hfl) h

/-- Advancing (or otherwise rewriting) a domain's pc preserves `Wf`. -/
theorem wf_updDomPc (σ : MachineState) (d : DomainId) (k : DomainState → Addr) (h : Wf σ) :
    Wf (σ.setDom d (fun ds => { ds with pc := k ds })) := by
  have hproj : ∀ (d' : DomainId),
      (((σ.setDom d (fun ds => { ds with pc := k ds })).doms d').caps = (σ.doms d').caps) ∧
      (((σ.setDom d (fun ds => { ds with pc := k ds })).doms d').lineage = (σ.doms d').lineage) ∧
      (((σ.setDom d (fun ds => { ds with pc := k ds })).doms d').slotGen = (σ.doms d').slotGen) ∧
      (((σ.setDom d (fun ds => { ds with pc := k ds })).doms d').regions = (σ.doms d').regions) ∧
      (((σ.setDom d (fun ds => { ds with pc := k ds })).doms d').run = (σ.doms d').run) ∧
      (((σ.setDom d (fun ds => { ds with pc := k ds })).doms d').serving = (σ.doms d').serving) := by
    intro d'; unfold MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ hp]
  refine wf_of_skeleton_sameGates σ _
    (fun d' => (hproj d').1) (fun d' => (hproj d').2.1) (fun d' => (hproj d').2.2.1)
    (fun d' => (hproj d').2.2.2.1) (fun d' => (hproj d').2.2.2.2.1) (fun d' => (hproj d').2.2.2.2.2)
    rfl rfl ?_ h
  intro fl' hfl'
  have hinfeq : (σ.setDom d (fun ds => { ds with pc := k ds })).inflight = σ.inflight := rfl
  rw [hinfeq] at hfl'; rw [(hproj fl'.dom).2.2.2.2.1]; exact h.inflight_running fl' hfl'

theorem PreservesWf.updDomPc (d : DomainId) (k : DomainState → Addr) :
    PreservesWf (SpecM.updDom d (fun ds => { ds with pc := k ds })) := by
  intro σ hwf hinf
  refine ⟨?_, ?_⟩
  · intro a σ' he
    simp only [SpecM.updDom, SpecM.modify] at he; injection he with h1 h2; subst h2
    exact ⟨wf_updDomPc σ d k hwf, hinf⟩
  · intro e σ' he; simp [SpecM.updDom, SpecM.modify] at he

theorem PreservesWf.demand (cond : Bool) (f : Fault) : PreservesWf (SpecM.demand cond f) := by
  unfold SpecM.demand; split
  · exact PreservesWf.pure ()
  · intro σ hwf hinf
    refine ⟨?_, ?_⟩ <;> (intro a σ' he; simp [SpecM.fatal] at he)

theorem PreservesWf.load (d : DomainId) (a : Addr) : PreservesWf (SpecM.load d a) := by
  unfold SpecM.load
  exact PreservesWf.bind PreservesWf.get
    (fun σ0 => PreservesWf.bind (PreservesWf.demand _ _) (fun _ => PreservesWf.pure _))

theorem PreservesWf.store (d : DomainId) (a : Addr) (v : Loom.Word32) :
    PreservesWf (SpecM.store d a v) := by
  intro σ hwf hinf
  refine ⟨?_, ?_⟩
  · intro x σ' he
    -- store σ = (get >>= fun σ0 => demand ... >>= fun _ => set (σ0.write a v)) σ
    simp only [SpecM.store, specM_bind, SpecM.get] at he
    by_cases hcov : σ.domCovers d a { r := false, w := true, x := false }
    · simp only [SpecM.demand, hcov, if_true, specM_pure, specM_bind, SpecM.set] at he
      injection he with h1 h2; subst h2
      exact ⟨wf_write σ a v hwf, hinf⟩
    · simp [SpecM.demand, hcov, SpecM.fatal, specM_bind] at he
  · intro e σ' he
    simp only [SpecM.store, specM_bind, SpecM.get] at he
    by_cases hcov : σ.domCovers d a { r := false, w := true, x := false }
    · simp [SpecM.demand, hcov, specM_pure, specM_bind, SpecM.set] at he
    · simp [SpecM.demand, hcov, SpecM.fatal, specM_bind] at he


/-- Preservation is closed under `if`. -/
theorem PreservesWf.ite {α : Type} (c : Prop) [Decidable c] {m1 m2 : SpecM α}
    (h1 : PreservesWf m1) (h2 : PreservesWf m2) : PreservesWf (if c then m1 else m2) := by
  split
  · exact h1
  · exact h2

/-- Preservation is closed under `Bool`-guarded `if`. -/
theorem PreservesWf.iteBool {α : Type} (b : Bool) {m1 m2 : SpecM α}
    (h1 : PreservesWf m1) (h2 : PreservesWf m2) :
    PreservesWf (if b = true then m1 else m2) := by
  split
  · exact h1
  · exact h2


/-- Changing a domain's budget preserves `Wf` (`budget` is not read by `Wf`). -/
theorem wf_updDomBudget (σ : MachineState) (d : DomainId) (bf : DomainState → Nat)
    (h : Wf σ) : Wf (σ.setDom d (fun ds => { ds with budget := bf ds })) := by
  have hproj : ∀ (d' : DomainId),
      (((σ.setDom d (fun ds => { ds with budget := bf ds })).doms d').caps = (σ.doms d').caps) ∧
      (((σ.setDom d (fun ds => { ds with budget := bf ds })).doms d').lineage = (σ.doms d').lineage) ∧
      (((σ.setDom d (fun ds => { ds with budget := bf ds })).doms d').slotGen = (σ.doms d').slotGen) ∧
      (((σ.setDom d (fun ds => { ds with budget := bf ds })).doms d').regions = (σ.doms d').regions) ∧
      (((σ.setDom d (fun ds => { ds with budget := bf ds })).doms d').run = (σ.doms d').run) ∧
      (((σ.setDom d (fun ds => { ds with budget := bf ds })).doms d').serving = (σ.doms d').serving) := by
    intro d'; unfold MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ hp]
  refine wf_of_skeleton_sameGates σ _
    (fun d' => (hproj d').1) (fun d' => (hproj d').2.1) (fun d' => (hproj d').2.2.1)
    (fun d' => (hproj d').2.2.2.1) (fun d' => (hproj d').2.2.2.2.1) (fun d' => (hproj d').2.2.2.2.2)
    rfl rfl ?_ h
  intro fl' hfl'
  have : (σ.setDom d (fun ds => { ds with budget := bf ds })).inflight = σ.inflight := rfl
  rw [this] at hfl'; rw [(hproj fl'.dom).2.2.2.2.1]; exact h.inflight_running fl' hfl'

theorem PreservesWf.updDomBudget (d : DomainId) (bf : DomainState → Nat) :
    PreservesWf (SpecM.updDom d (fun ds => { ds with budget := bf ds })) := by
  intro σ hwf hinf
  refine ⟨?_, ?_⟩
  · intro a σ' he; simp only [SpecM.updDom, SpecM.modify] at he; injection he with h1 h2
    subst h2; exact ⟨wf_updDomBudget σ d bf hwf, hinf⟩
  · intro e σ' he; simp [SpecM.updDom, SpecM.modify] at he

/-- Clearing a region register preserves `Wf` (`region_backed` becomes vacuous
for the cleared slot; every other domain and region is unchanged). -/
theorem wf_clearRegion (σ : MachineState) (d : DomainId) (ri : RegionId) (h : Wf σ) :
    Wf (σ.setDom d (fun ds => { ds with regions := Loom.Fun.update ds.regions ri none })) := by
  set σ' := σ.setDom d (fun ds => { ds with regions := Loom.Fun.update ds.regions ri none }) with hσ'
  have hdoms : ∀ d' : DomainId,
      (σ'.doms d').caps = (σ.doms d').caps ∧ (σ'.doms d').lineage = (σ.doms d').lineage ∧
      (σ'.doms d').slotGen = (σ.doms d').slotGen ∧ (σ'.doms d').run = (σ.doms d').run ∧
      (σ'.doms d').serving = (σ.doms d').serving := by
    intro d'; rw [hσ']; unfold MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ hp]
  have hreg : ∀ d' r, (σ'.doms d').regions r =
      if d' = d ∧ r = ri then none else (σ.doms d').regions r := by
    intro d' r; rw [hσ']; unfold MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp only [Loom.Fun.update_same]
      by_cases hr : r = ri
      · subst hr; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hr, hr]
    · simp [Loom.Fun.update_ne _ _ _ _ hp, hp]
  have hlive : ∀ r, σ'.liveRef r = σ.liveRef r := by
    intro r; unfold MachineState.liveRef DomainState.liveCap
    rw [(hdoms r.dom).1, (hdoms r.dom).2.2.1]
  have hgates : σ'.gates = σ.gates := by rw [hσ']; rfl
  have hmover : σ'.mover = σ.mover := by rw [hσ']; rfl
  have hinf : σ'.inflight = σ.inflight := by rw [hσ']; rfl
  have hpar : ∀ d' s, σ'.parentOf d' s = σ.parentOf d' s := by
    intro d' s; unfold MachineState.parentOf; rw [(hdoms d').1, (hdoms d').2.1]
  constructor
  · intro d'
    have hd := h.doms d'
    exact ⟨fun s => by rw [(hdoms d').2.2.1]; exact hd.gen_pos s,
      fun s e l => by rw [(hdoms d').1, (hdoms d').2.1]; exact hd.cell_backed s e l,
      fun s s' e e' l => by rw [(hdoms d').1]; exact hd.ptr_inj s s' e e' l,
      fun l => by rw [(hdoms d').2.1, (hdoms d').1]; exact hd.cell_used l,
      fun s base len p => by rw [(hdoms d').1]; exact hd.wx s base len p,
      fun s e base len p => by rw [(hdoms d').1]; exact hd.bounds s e base len p⟩
  · intro d' s p; rw [hpar, hlive]; exact h.parent_live d' s p
  · intro d' r rg; rw [hreg]; split
    · intro hc; exact absurd hc (by simp)
    · intro hrg
      obtain ⟨e, hl, hle⟩ := h.region_backed d' r rg hrg
      refine ⟨e, ?_, hle⟩; unfold DomainState.liveCap
      rw [(hdoms rg.backing.dom).1, (hdoms rg.backing.dom).2.2.1]; exact hl
  · intro job; rw [hmover]; intro hj
    obtain ⟨o1, o2, o3, o4⟩ := h.mover_wf job hj
    exact ⟨o1, o2, by rw [hlive]; exact o3, by rw [hlive]; exact o4⟩
  · intro g a; rw [hgates]; intro ha
    obtain ⟨s1, s2, s3, s4⟩ := h.gate_serving g a ha
    exact ⟨by rw [(hdoms _).2.2.2.2]; exact s1,
      by rw [(hdoms _).2.2.2.1]; exact s2, s3, s4⟩
  · intro d' g; rw [(hdoms d').2.2.2.2]; intro hs; rw [hgates]; exact h.serving_gate d' g hs
  · intro d' g; rw [(hdoms d').2.2.2.1]; intro hb; rw [hgates]; exact h.blocked_gate d' g hb
  · intro fl' hfl'; rw [hinf] at hfl'; rw [(hdoms fl'.dom).2.2.2.1]; exact h.inflight_running fl' hfl'

theorem PreservesWf.clearRegion (d : DomainId) (ri : RegionId) :
    PreservesWf (SpecM.updDom d (fun ds => { ds with regions := Loom.Fun.update ds.regions ri none })) := by
  intro σ hwf hinf
  refine ⟨?_, ?_⟩
  · intro a σ' he; simp only [SpecM.updDom, SpecM.modify] at he; injection he with h1 h2
    subst h2; exact ⟨wf_clearRegion σ d ri hwf, hinf⟩
  · intro e σ' he; simp [SpecM.updDom, SpecM.modify] at he


/-- Installing a region register preserves `Wf`, provided the region's backing
capability is live and dominates the region's authority (the `region_backed`
obligation for the new entry; every other region is unchanged). -/
theorem wf_installRegion (σ : MachineState) (d : DomainId) (ri : RegionId) (rgn : Region)
    (hb : ∃ e, ((σ.doms rgn.backing.dom).liveCap rgn.backing.slot rgn.backing.gen) = some e ∧
      (CapKind.mem rgn.base rgn.len rgn.perms).le e.kind) (h : Wf σ) :
    Wf (σ.setDom d (fun ds => { ds with regions := Loom.Fun.update ds.regions ri (some rgn) })) := by
  set σ' := σ.setDom d (fun ds => { ds with regions := Loom.Fun.update ds.regions ri (some rgn) })
    with hσ'
  have hdoms : ∀ d' : DomainId,
      (σ'.doms d').caps = (σ.doms d').caps ∧ (σ'.doms d').lineage = (σ.doms d').lineage ∧
      (σ'.doms d').slotGen = (σ.doms d').slotGen ∧ (σ'.doms d').run = (σ.doms d').run ∧
      (σ'.doms d').serving = (σ.doms d').serving := by
    intro d'; rw [hσ']; unfold MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ hp]
  have hreg : ∀ d' r, (σ'.doms d').regions r =
      if d' = d ∧ r = ri then some rgn else (σ.doms d').regions r := by
    intro d' r; rw [hσ']; unfold MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp only [Loom.Fun.update_same]
      by_cases hr : r = ri
      · subst hr; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hr, hr]
    · simp [Loom.Fun.update_ne _ _ _ _ hp, hp]
  have hlive : ∀ r, σ'.liveRef r = σ.liveRef r := by
    intro r; unfold MachineState.liveRef DomainState.liveCap; rw [(hdoms r.dom).1, (hdoms r.dom).2.2.1]
  have hgates : σ'.gates = σ.gates := by rw [hσ']; rfl
  have hmover : σ'.mover = σ.mover := by rw [hσ']; rfl
  have hinf : σ'.inflight = σ.inflight := by rw [hσ']; rfl
  have hpar : ∀ d' s, σ'.parentOf d' s = σ.parentOf d' s := by
    intro d' s; unfold MachineState.parentOf; rw [(hdoms d').1, (hdoms d').2.1]
  constructor
  · intro d'
    have hd := h.doms d'
    exact ⟨fun s => by rw [(hdoms d').2.2.1]; exact hd.gen_pos s,
      fun s e l => by rw [(hdoms d').1, (hdoms d').2.1]; exact hd.cell_backed s e l,
      fun s s' e e' l => by rw [(hdoms d').1]; exact hd.ptr_inj s s' e e' l,
      fun l => by rw [(hdoms d').2.1, (hdoms d').1]; exact hd.cell_used l,
      fun s base len p => by rw [(hdoms d').1]; exact hd.wx s base len p,
      fun s e base len p => by rw [(hdoms d').1]; exact hd.bounds s e base len p⟩
  · intro d' s p; rw [hpar, hlive]; exact h.parent_live d' s p
  · intro d' r rg; rw [hreg]; split
    · -- the newly-installed region: use the backing guarantee
      intro hrg; simp only [Option.some.injEq] at hrg; subst hrg
      obtain ⟨e, hle, hdom⟩ := hb
      refine ⟨e, ?_, hdom⟩
      unfold DomainState.liveCap; rw [(hdoms rgn.backing.dom).1, (hdoms rgn.backing.dom).2.2.1]
      exact hle
    · intro hrg
      obtain ⟨e, hl, hle⟩ := h.region_backed d' r rg hrg
      refine ⟨e, ?_, hle⟩; unfold DomainState.liveCap
      rw [(hdoms rg.backing.dom).1, (hdoms rg.backing.dom).2.2.1]; exact hl
  · intro job; rw [hmover]; intro hj
    obtain ⟨o1, o2, o3, o4⟩ := h.mover_wf job hj
    exact ⟨o1, o2, by rw [hlive]; exact o3, by rw [hlive]; exact o4⟩
  · intro g a; rw [hgates]; intro ha
    obtain ⟨s1, s2, s3, s4⟩ := h.gate_serving g a ha
    exact ⟨by rw [(hdoms _).2.2.2.2]; exact s1, by rw [(hdoms _).2.2.2.1]; exact s2, s3, s4⟩
  · intro d' g; rw [(hdoms d').2.2.2.2]; intro hs; rw [hgates]; exact h.serving_gate d' g hs
  · intro d' g; rw [(hdoms d').2.2.2.1]; intro hb'; rw [hgates]; exact h.blocked_gate d' g hb'
  · intro fl' hfl'; rw [hinf] at hfl'; rw [(hdoms fl'.dom).2.2.2.1]; exact h.inflight_running fl' hfl'


/-- A free slot has no capability entry. -/
theorem freeSlot_caps_none (σ : MachineState) (d : DomainId) {s : Slot}
    (h : σ.freeSlot d = some s) : (σ.doms d).caps s = none := by
  unfold MachineState.freeSlot at h
  have := List.find?_some h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, bne_iff_ne] at this
  exact this.1

/-- A free lineage cell is empty. -/
theorem freeCell_none (σ : MachineState) (d : DomainId) {l : LineageId}
    (h : σ.freeCell d = some l) : (σ.doms d).lineage l = none := by
  unfold MachineState.freeCell at h
  have := List.find?_some h
  simpa only [Option.isNone_iff_eq_none] using this

/-- Installing a fresh derived capability preserves `Wf`, given: the slot and
cell are free, the kind is W^X + in-bounds if memory, and the parent is live.
The `installDerived` invariant lemma behind `cap_dup`/`mem_grant`. -/
theorem wf_installDerived (σ : MachineState) (d : DomainId) (s : Slot) (l : LineageId)
    (kind : CapKind) (parent : CapRef)
    (hs : (σ.doms d).caps s = none) (hl : (σ.doms d).lineage l = none)
    (hwx : ∀ base len p, kind = .mem base len p → p.wx = true ∧ base.toNat + len.toNat ≤ memWords)
    (hpar : σ.liveRef parent = true) (h : Wf σ) :
    Wf (σ.installDerived d s l kind parent).1 := by
  set σ' := (σ.installDerived d s l kind parent).1 with hσ'
  have hgen : ∀ d', (σ'.doms d').slotGen = (σ.doms d').slotGen := by
    intro d'; rw [hσ']; unfold MachineState.installDerived MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ hp]
  have hcaps : ∀ d' s', (σ'.doms d').caps s' =
      if d' = d ∧ s' = s then some { kind := kind, lineage := some l } else (σ.doms d').caps s' := by
    intro d' s'; rw [hσ']; unfold MachineState.installDerived MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp only [Loom.Fun.update_same]
      by_cases hss : s' = s
      · subst hss; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hss, hss]
    · simp [Loom.Fun.update_ne _ _ _ _ hp, hp]
  have hlin : ∀ d' l', (σ'.doms d').lineage l' =
      if d' = d ∧ l' = l then some { parent := parent } else (σ.doms d').lineage l' := by
    intro d' l'; rw [hσ']; unfold MachineState.installDerived MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp only [Loom.Fun.update_same]
      by_cases hll : l' = l
      · subst hll; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hll, hll]
    · simp [Loom.Fun.update_ne _ _ _ _ hp, hp]
  have hrun : ∀ d', (σ'.doms d').run = (σ.doms d').run := by
    intro d'; rw [hσ']; unfold MachineState.installDerived MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ hp]
  have hserv : ∀ d', (σ'.doms d').serving = (σ.doms d').serving := by
    intro d'; rw [hσ']; unfold MachineState.installDerived MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ hp]
  have hreg : ∀ d', (σ'.doms d').regions = (σ.doms d').regions := by
    intro d'; rw [hσ']; unfold MachineState.installDerived MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ hp]
  have hgates : σ'.gates = σ.gates := by rw [hσ']; rfl
  have hmover : σ'.mover = σ.mover := by rw [hσ']; rfl
  have hinf : σ'.inflight = σ.inflight := by rw [hσ']; rfl
  -- live capabilities are preserved (the new slot was free)
  have hlivecap : ∀ (dd : DomainId) (ss : Slot) (gg : Gen) (e : CapEntry),
      (σ.doms dd).liveCap ss gg = some e → (σ'.doms dd).liveCap ss gg = some e := by
    intro dd ss gg e hlc
    have hne : ¬ (dd = d ∧ ss = s) := by
      rintro ⟨rfl, rfl⟩
      unfold DomainState.liveCap at hlc; rw [hs] at hlc; simp at hlc
    unfold DomainState.liveCap at hlc ⊢
    rw [hcaps, if_neg hne, hgen]; exact hlc
  have hliveref : ∀ r, σ.liveRef r = true → σ'.liveRef r = true := by
    intro r hr
    unfold MachineState.liveRef at hr ⊢
    rw [Option.isSome_iff_exists] at hr; obtain ⟨e, he⟩ := hr
    rw [hlivecap r.dom r.slot r.gen e he]; rfl
  constructor
  · intro d'
    have hd := h.doms d'
    constructor
    · intro s0; rw [hgen]; exact hd.gen_pos s0
    · intro s0 e0 l0 he0 hle0
      rw [hlin]
      by_cases hnew : d' = d ∧ s0 = s
      · rw [hcaps, if_pos hnew] at he0; injection he0 with hek
        subst hek; simp only [Option.some.injEq] at hle0; subst hle0
        rw [if_pos ⟨hnew.1, rfl⟩]; simp
      · rw [hcaps, if_neg hnew] at he0
        by_cases hlc : d' = d ∧ l0 = l
        · simp [hlc]
        · rw [if_neg hlc]; exact hd.cell_backed s0 e0 l0 he0 hle0
    · intro s1 s2 e1 e2 l0 he1 he2 hl1 hl2
      by_cases h1 : d' = d ∧ s1 = s <;> by_cases h2 : d' = d ∧ s2 = s
      · obtain ⟨_, rfl⟩ := h1; obtain ⟨_, rfl⟩ := h2; rfl
      · obtain ⟨hdd, rfl⟩ := h1; subst hdd
        rw [hcaps, if_pos (And.intro rfl rfl)] at he1; injection he1 with hek1; subst hek1
        simp only [Option.some.injEq] at hl1; subst hl1
        rw [hcaps, if_neg h2] at he2
        exact absurd (hd.cell_backed s2 e2 l he2 hl2) (by rw [hl]; simp)
      · obtain ⟨hdd, rfl⟩ := h2; subst hdd
        rw [hcaps, if_pos (And.intro rfl rfl)] at he2; injection he2 with hek2; subst hek2
        simp only [Option.some.injEq] at hl2; subst hl2
        rw [hcaps, if_neg h1] at he1
        exact absurd (hd.cell_backed s1 e1 l he1 hl1) (by rw [hl]; simp)
      · rw [hcaps, if_neg h1] at he1; rw [hcaps, if_neg h2] at he2
        exact hd.ptr_inj s1 s2 e1 e2 l0 he1 he2 hl1 hl2
    · intro l0 hl0
      rw [hlin] at hl0
      by_cases hnew : d' = d ∧ l0 = l
      · obtain ⟨hd1, hd2⟩ := hnew; subst l0
        refine ⟨s, { kind := kind, lineage := some l }, ?_, rfl⟩
        rw [hcaps, if_pos ⟨hd1, rfl⟩]
      · rw [if_neg hnew] at hl0
        obtain ⟨s0, e0, hc0, he0⟩ := hd.cell_used l0 hl0
        refine ⟨s0, e0, ?_, he0⟩
        rw [hcaps]; by_cases hns : d' = d ∧ s0 = s
        · exfalso; obtain ⟨hd1, hd2⟩ := hns; rw [hd1, hd2, hs] at hc0
          exact absurd hc0 (by simp)
        · rw [if_neg hns]; exact hc0
    · intro s0 base len p hcase
      by_cases hnew : d' = d ∧ s0 = s
      · rcases hcase with hc | ⟨l0, hc⟩ <;>
          (rw [hcaps, if_pos hnew] at hc
           simp only [Option.some.injEq, CapEntry.mk.injEq] at hc
           exact (hwx base len p hc.1).1)
      · rcases hcase with hc | ⟨l0, hc⟩
        · rw [hcaps, if_neg hnew] at hc; exact hd.wx s0 base len p (Or.inl hc)
        · rw [hcaps, if_neg hnew] at hc; exact hd.wx s0 base len p (Or.inr ⟨l0, hc⟩)
    · intro s0 e0 base len p hc hk
      by_cases hnew : d' = d ∧ s0 = s
      · rw [hcaps, if_pos hnew] at hc
        simp only [Option.some.injEq] at hc; subst hc
        exact (hwx base len p hk).2
      · rw [hcaps, if_neg hnew] at hc; exact hd.bounds s0 e0 base len p hc hk
  · intro d' s0 p0 hpar0
    by_cases hnew : d' = d ∧ s0 = s
    · obtain ⟨hd1, hd2⟩ := hnew
      have hc1 : (σ'.doms d').caps s0 = some { kind := kind, lineage := some l } := by
        rw [hcaps, if_pos ⟨hd1, hd2⟩]
      have hl1 : (σ'.doms d').lineage l = some { parent := parent } := by
        rw [hlin, if_pos ⟨hd1, rfl⟩]
      have hpeq : σ'.parentOf d' s0 = some parent := by
        simp [MachineState.parentOf, hc1, hl1]
      rw [hpeq] at hpar0; injection hpar0 with hh; subst hh; exact hliveref parent hpar
    · have hpeq : σ'.parentOf d' s0 = σ.parentOf d' s0 := by
        have hcs : (σ'.doms d').caps s0 = (σ.doms d').caps s0 := by rw [hcaps, if_neg hnew]
        unfold MachineState.parentOf; rw [hcs]
        cases hc0 : (σ.doms d').caps s0 with
        | none => rfl
        | some e0 =>
            cases hle0 : e0.lineage with
            | none => simp [hle0]
            | some l0 =>
                have hll : (σ'.doms d').lineage l0 = (σ.doms d').lineage l0 := by
                  rw [hlin]; by_cases hlc : d' = d ∧ l0 = l
                  · exfalso; obtain ⟨he1, he2⟩ := hlc
                    have hcb := (h.doms d').cell_backed s0 e0 l0 hc0 hle0
                    rw [he1, he2, hl] at hcb; simp at hcb
                  · rw [if_neg hlc]
                simp [hle0, hll]
      rw [hpeq] at hpar0; exact hliveref p0 (h.parent_live d' s0 p0 hpar0)
  · intro d' r rg; rw [hreg]; intro hrg
    obtain ⟨e, hl0, hle⟩ := h.region_backed d' r rg hrg
    exact ⟨e, hlivecap _ _ _ _ hl0, hle⟩
  · intro job; rw [hmover]; intro hj
    obtain ⟨o1, o2, o3, o4⟩ := h.mover_wf job hj
    exact ⟨o1, o2, hliveref _ o3, hliveref _ o4⟩
  · intro g a; rw [hgates]; intro ha
    obtain ⟨s1, s2, s3, s4⟩ := h.gate_serving g a ha
    exact ⟨by rw [hserv]; exact s1, by rw [hrun]; exact s2, s3, s4⟩
  · intro d' g; rw [hserv]; intro hs0; rw [hgates]; exact h.serving_gate d' g hs0
  · intro d' g; rw [hrun]; intro hb; rw [hgates]; exact h.blocked_gate d' g hb
  · intro fl' hfl'; rw [hinf] at hfl'; rw [hrun]; exact h.inflight_running fl' hfl'


/-- `allocDerived` preserves `Wf` on success, given the kind is W^X/in-bounds
(if memory) and the parent is live. It allocates a free slot and cell and calls
`installDerived`. The bridge for `cap_dup`/`mem_grant`. -/
theorem allocDerived_ok (owner : DomainId) (kind : CapKind) (parent : CapRef)
    (σ : MachineState) {hw : Loom.Word32} {σ' : MachineState}
    (hwx : ∀ base len p, kind = .mem base len p → p.wx = true ∧ base.toNat + len.toNat ≤ memWords)
    (hpar : σ.liveRef parent = true) (h : Wf σ)
    (he : Machines.Lnp64u.Isa.allocDerived owner kind parent σ = .ok hw σ') : Wf σ' := by
  unfold Machines.Lnp64u.Isa.allocDerived at he
  simp only [SpecM.get, specM_bind] at he
  cases hfs : σ.freeSlot owner with
  | none => rw [hfs] at he; simp [SpecM.raise] at he
  | some s =>
      rw [hfs] at he
      cases hfc : σ.freeCell owner with
      | none => rw [hfc] at he; simp [SpecM.raise] at he
      | some l =>
          rw [hfc] at he
          simp only [SpecM.set, specM_bind, specM_pure] at he
          injection he with _ h2
          have hσ' : σ' = (σ.installDerived owner s l kind parent).1 := by
            rw [← h2]
          rw [hσ']
          exact wf_installDerived σ owner s l kind parent
            (freeSlot_caps_none σ owner hfs) (freeCell_none σ owner hfc) hwx hpar h



/-- Programming the Mover preserves `Wf`, given the job's capabilities are live
and owned by the job's owner (the `mover_wf` obligation for the new job; only
the `mover` field changes). Infrastructure for the `move` opcode. -/
theorem wf_setMover (σ : MachineState) (job : MoverJob)
    (h1 : job.src.dom = job.owner) (h2 : job.dst.dom = job.owner)
    (h3 : σ.liveRef job.src = true) (h4 : σ.liveRef job.dst = true) (h : Wf σ) :
    Wf { σ with mover := some job } := by
  obtain ⟨hdoms, hpl, hrb, _hmw, hgs, hsg, hbg, hir⟩ := h
  refine ⟨hdoms, hpl, hrb, ?_, hgs, hsg, hbg, hir⟩
  intro j hj; simp only [Option.some.injEq] at hj; subst hj
  exact ⟨h1, h2, h3, h4⟩


/-- `load` is read-only: on success the state is unchanged and the value read. -/
theorem load_ok (d : DomainId) (a : Addr) (σ : MachineState) {v : Loom.Word32}
    {σ' : MachineState} (he : SpecM.load d a σ = .ok v σ') : σ' = σ := by
  unfold SpecM.load at he
  simp only [SpecM.get, specM_bind] at he
  by_cases hc : σ.domCovers d a { r := true, w := false, x := false }
  · simp only [SpecM.demand, hc, if_true, specM_pure, specM_bind] at he
    injection he with _ h2; exact h2.symm
  · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he

/-- `require`/`get`/`reg` are read-only on success. -/
theorem require_ok (cond : Bool) (e : Errno) (σ : MachineState) {σ' : MachineState}
    (he : SpecM.require cond e σ = .ok () σ') : σ' = σ := by
  unfold SpecM.require at he; split at he
  · injection he with _ h2; exact h2.symm
  · simp [SpecM.raise] at he

theorem demand_ok (cond : Bool) (f : Fault) (σ : MachineState) {σ' : MachineState}
    (he : SpecM.demand cond f σ = .ok () σ') : σ' = σ := by
  unfold SpecM.demand at he; split at he
  · injection he with _ h2; exact h2.symm
  · simp [SpecM.fatal] at he


theorem require_err_state (cond : Bool) (e : Errno) (σ : MachineState) {e0 : Errno}
    {σ' : MachineState} (he : SpecM.require cond e σ = .err e0 σ') : σ' = σ := by
  unfold SpecM.require at he; split at he
  · simp at he
  · simp only [SpecM.raise] at he; injection he with _ h2; exact h2.symm

theorem load_err_state (d : DomainId) (a : Addr) (σ : MachineState) {e0 : Errno}
    {σ' : MachineState} (he : SpecM.load d a σ = .err e0 σ') : σ' = σ := by
  unfold SpecM.load at he
  simp only [SpecM.get, specM_bind] at he
  by_cases hc : σ.domCovers d a { r := true, w := false, x := false }
  · simp [SpecM.demand, hc, specM_pure, specM_bind] at he
  · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he


/-- Sweeping region registers preserves `Wf`: only dead-backed regions are
cleared (`region_backed` survivors keep their live backing). -/
theorem wf_sweepRegions (σ : MachineState) (h : Wf σ) : Wf σ.sweepRegions := by
  have hd : ∀ d, (σ.sweepRegions.doms d).caps = (σ.doms d).caps ∧
      (σ.sweepRegions.doms d).lineage = (σ.doms d).lineage ∧
      (σ.sweepRegions.doms d).slotGen = (σ.doms d).slotGen ∧
      (σ.sweepRegions.doms d).run = (σ.doms d).run ∧
      (σ.sweepRegions.doms d).serving = (σ.doms d).serving := by
    intro d; unfold MachineState.sweepRegions; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hg : σ.sweepRegions.gates = σ.gates := rfl
  have hm : σ.sweepRegions.mover = σ.mover := rfl
  have hi : σ.sweepRegions.inflight = σ.inflight := rfl
  have hlr : ∀ r, σ.sweepRegions.liveRef r = σ.liveRef r := by
    intro r; unfold MachineState.liveRef DomainState.liveCap; rw [(hd r.dom).1, (hd r.dom).2.2.1]
  have hpar : ∀ d s, σ.sweepRegions.parentOf d s = σ.parentOf d s := by
    intro d s; unfold MachineState.parentOf; rw [(hd d).1, (hd d).2.1]
  constructor
  · intro d; have hh := h.doms d
    exact ⟨fun s => by rw [(hd d).2.2.1]; exact hh.gen_pos s,
      fun s e l => by rw [(hd d).1, (hd d).2.1]; exact hh.cell_backed s e l,
      fun s s' e e' l => by rw [(hd d).1]; exact hh.ptr_inj s s' e e' l,
      fun l => by rw [(hd d).2.1, (hd d).1]; exact hh.cell_used l,
      fun s base len p => by rw [(hd d).1]; exact hh.wx s base len p,
      fun s e base len p => by rw [(hd d).1]; exact hh.bounds s e base len p⟩
  · intro d s p; rw [hpar, hlr]; exact h.parent_live d s p
  · intro d r rg hrg
    have horig : (σ.doms d).regions r = some rg ∧ σ.liveRef rg.backing = true := by
      simp only [MachineState.sweepRegions] at hrg
      split at hrg
      · next rg0 hro =>
          split at hrg
          · next hlv =>
              simp only [Option.some.injEq] at hrg; subst hrg; exact ⟨hro, hlv⟩
          · next hlv => simp at hrg
      · next => simp at hrg
    obtain ⟨e, hl, hle⟩ := h.region_backed d r rg horig.1
    refine ⟨e, ?_, hle⟩; unfold DomainState.liveCap
    rw [(hd rg.backing.dom).1, (hd rg.backing.dom).2.2.1]; exact hl
  · intro job; rw [hm]; intro hj
    obtain ⟨o1, o2, o3, o4⟩ := h.mover_wf job hj
    exact ⟨o1, o2, by rw [hlr]; exact o3, by rw [hlr]; exact o4⟩
  · intro g a; rw [hg]; intro ha
    obtain ⟨s1, s2, s3, s4⟩ := h.gate_serving g a ha
    exact ⟨by rw [(hd _).2.2.2.2]; exact s1, by rw [(hd _).2.2.2.1]; exact s2, s3, s4⟩
  · intro d g; rw [(hd d).2.2.2.2]; intro hs; rw [hg]; exact h.serving_gate d g hs
  · intro d g; rw [(hd d).2.2.2.1]; intro hb; rw [hg]; exact h.blocked_gate d g hb
  · intro fl hfl; rw [hi] at hfl; rw [(hd fl.dom).2.2.2.1]; exact h.inflight_running fl hfl


/-- Sweeping the Mover preserves `Wf`: it clears a job with a dead capability
(then `mover_wf` is vacuous) or leaves a live job, and only writes memory. -/
theorem wf_sweepMover (σ : MachineState) (h : Wf σ) : Wf σ.sweepMover := by
  unfold MachineState.sweepMover
  cases hmv : σ.mover with
  | none => simpa [hmv] using h
  | some job =>
      by_cases hchk : σ.liveRef job.src && σ.liveRef job.dst
      · simp only [hchk, if_true]; exact h
      · simp only [hchk, if_false]
        -- the resulting state clears the mover (and maybe writes memory)
        set σ0 : MachineState := { σ with mover := none } with hσ0
        have hcl : Wf σ0 := by
          obtain ⟨hdoms, hpl, hrb, _, hgs, hsg, hbg, hir⟩ := h
          exact ⟨hdoms, hpl, hrb, by intro j hj; rw [hσ0] at hj; simp at hj, hgs, hsg, hbg, hir⟩
        by_cases hcov : σ0.domCovers job.owner job.statusAddr { r := false, w := true, x := false }
        · simp only [hcov, if_true]
          -- writing the status word changes only memory
          exact wf_of_skeleton_sameGates σ0 (σ0.write job.statusAddr Errno.staleHandle.toWord)
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
            (fun _ => rfl) rfl rfl (fun fl hfl => hcl.inflight_running fl hfl) hcl
        · simp only [hcov, if_false]; exact hcl


/-- Reparenting (redirecting every cell whose parent is `old` to `new`)
preserves `Wf`, given `new` is live. Only lineage-cell parents change; the
redirected cells now point at a live capability. -/
theorem wf_reparent (σ : MachineState) (old new : CapRef) (hnew : σ.liveRef new = true)
    (h : Wf σ) : Wf (σ.reparent old new) := by
  set σ' := σ.reparent old new with hσ'
  have hcaps : ∀ d, (σ'.doms d).caps = (σ.doms d).caps := fun d => rfl
  have hgen : ∀ d, (σ'.doms d).slotGen = (σ.doms d).slotGen := fun d => rfl
  have hreg : ∀ d, (σ'.doms d).regions = (σ.doms d).regions := fun d => rfl
  have hrun : ∀ d, (σ'.doms d).run = (σ.doms d).run := fun d => rfl
  have hserv : ∀ d, (σ'.doms d).serving = (σ.doms d).serving := fun d => rfl
  have hg : σ'.gates = σ.gates := rfl
  have hm : σ'.mover = σ.mover := rfl
  have hi : σ'.inflight = σ.inflight := rfl
  have hlin : ∀ d l, (σ'.doms d).lineage l =
      match (σ.doms d).lineage l with
      | some cell => some (if cell.parent = old then { parent := new } else cell)
      | none => none := fun d l => rfl
  have hlr : ∀ r, σ'.liveRef r = σ.liveRef r := by
    intro r; unfold MachineState.liveRef DomainState.liveCap; rw [hcaps, hgen]
  constructor
  · intro d; have hd := h.doms d
    refine ⟨fun s => by rw [hgen]; exact hd.gen_pos s, ?_, ?_, ?_,
      fun s base len p => by rw [hcaps]; exact hd.wx s base len p,
      fun s e base len p => by rw [hcaps]; exact hd.bounds s e base len p⟩
    · intro s e l he hl; rw [hlin]
      cases hc : (σ.doms d).lineage l with
      | none => have := hd.cell_backed s e l (by rw [hcaps] at he; exact he) hl
                rw [hc] at this; simp at this
      | some cell => simp [hc]
    · intro s s' e e' l; rw [hcaps]; exact hd.ptr_inj s s' e e' l
    · intro l hl; rw [hlin] at hl
      have hl2 : ((σ.doms d).lineage l).isSome := by
        cases hc : (σ.doms d).lineage l with
        | none => rw [hc] at hl; simp at hl
        | some _ => simp [hc]
      obtain ⟨s, e, hc, he⟩ := hd.cell_used l hl2
      exact ⟨s, e, by rw [hcaps]; exact hc, he⟩
  · intro d s p hp
    rw [hlr]
    have hcompute : σ'.parentOf d s =
        ((σ.parentOf d s).map (fun p0 => if p0 = old then new else p0)) := by
      unfold MachineState.parentOf
      cases hce : (σ.doms d).caps s with
      | none => simp [hcaps, hce]
      | some e =>
          cases hle : e.lineage with
          | none => simp [hcaps, hce, hle]
          | some l =>
              cases hc : (σ.doms d).lineage l with
              | none => simp [hcaps, hce, hle, hlin, hc]
              | some cell => by_cases hpp : cell.parent = old <;>
                             simp [hcaps, hce, hle, hlin, hc, hpp]
    rw [hcompute] at hp; simp only [Option.map_eq_some_iff] at hp
    obtain ⟨p0, hp0, hpeq⟩ := hp
    by_cases hpp : p0 = old
    · rw [if_pos hpp] at hpeq; subst hpeq; exact hnew
    · rw [if_neg hpp] at hpeq; subst hpeq; exact h.parent_live d s p0 hp0
  · intro d r rg; rw [hreg]; intro hrg
    obtain ⟨e, hl, hle⟩ := h.region_backed d r rg hrg
    refine ⟨e, ?_, hle⟩; unfold DomainState.liveCap; rw [hcaps, hgen]; exact hl
  · intro job; rw [hm]; intro hj
    obtain ⟨o1, o2, o3, o4⟩ := h.mover_wf job hj
    exact ⟨o1, o2, by rw [hlr]; exact o3, by rw [hlr]; exact o4⟩
  · intro g a; rw [hg]; intro ha
    obtain ⟨s1, s2, s3, s4⟩ := h.gate_serving g a ha
    exact ⟨by rw [hserv]; exact s1, by rw [hrun]; exact s2, s3, s4⟩
  · intro d g; rw [hserv]; intro hs; rw [hg]; exact h.serving_gate d g hs
  · intro d g; rw [hrun]; intro hb; rw [hg]; exact h.blocked_gate d g hb
  · intro fl hfl; rw [hi] at hfl; rw [hrun]; exact h.inflight_running fl hfl


/-- The composed `clearSlot` + region-sweep + Mover-sweep preserves `Wf`, given
that after the drop no lineage cell points at the removed capability's reference
(established by `reparent`/`orphanChildren`). The revocation core behind
`cap_drop`. -/
theorem wf_clearSlot_sweep (σ : MachineState) (d : DomainId) (s : Slot)
    (hno : ∀ dd ss, σ.parentOf dd ss ≠ some ⟨d, s, (σ.doms d).slotGen s⟩)
    (h : Wf σ) : Wf (((σ.clearSlot d s).sweepRegions).sweepMover) := by
  set σ1 := σ.clearSlot d s with hσ1
  set σ3 := (σ1.sweepRegions).sweepMover with hσ3
  have hcaps : ∀ d' s', (σ3.doms d').caps s' =
      if d' = d ∧ s' = s then none else (σ.doms d').caps s' := by
    intro d' s'; rw [hσ3, sweepMover_doms, sweepRegions_caps, hσ1, clearSlot_caps]
  have hgen : ∀ d' s', (σ3.doms d').slotGen s' =
      if d' = d ∧ s' = s then bumpGen ((σ.doms d).slotGen s) else (σ.doms d').slotGen s' := by
    intro d' s'; rw [hσ3, sweepMover_doms, sweepRegions_slotGen, hσ1, clearSlot_slotGen]
  have hrun : ∀ d', (σ3.doms d').run = (σ.doms d').run := by
    intro d'; rw [hσ3, sweepMover_doms, sweepRegions_run, hσ1, clearSlot_run]
  have hserv : ∀ d', (σ3.doms d').serving = (σ.doms d').serving := by
    intro d'; rw [hσ3, sweepMover_doms, sweepRegions_serving, hσ1, clearSlot_serving]
  have hgates : σ3.gates = σ.gates := by rw [hσ3, sweepMover_gates, sweepRegions_gates]; rfl
  have hinf : σ3.inflight = σ.inflight := by rw [hσ3, sweepMover_inflight, sweepRegions_inflight]; rfl
  have hlin : ∀ d' l, (σ3.doms d').lineage l =
      if d' = d ∧ removedCell σ d s = some l then none else (σ.doms d').lineage l := by
    intro d' l; rw [hσ3, sweepMover_doms, sweepRegions_lineage, hσ1, clearSlot_lineage]
  have hlc : ∀ dd ss gg e, ¬ (dd = d ∧ ss = s) →
      (σ.doms dd).liveCap ss gg = some e → (σ3.doms dd).liveCap ss gg = some e := by
    intro dd ss gg e hne hlive
    unfold DomainState.liveCap at hlive ⊢; rw [hcaps, if_neg hne, hgen, if_neg hne]; exact hlive
  have hlr : ∀ r, σ.liveRef r = true → ¬ (r.dom = d ∧ r.slot = s) → σ3.liveRef r = true := by
    intro r hr hne
    unfold MachineState.liveRef at hr ⊢
    rw [Option.isSome_iff_exists] at hr; obtain ⟨e, he⟩ := hr
    rw [hlc r.dom r.slot r.gen e hne he]; rfl
  -- helper: the removed cell (in domain d) is owned only by slot s
  have hrmowner : ∀ s0 e0, (σ.doms d).caps s0 = some e0 →
      e0.lineage = removedCell σ d s → removedCell σ d s ≠ none → s0 = s := by
    intro s0 e0 hc0 hle0 hne
    have hex : ∃ l, removedCell σ d s = some l := Option.ne_none_iff_exists'.mp hne
    obtain ⟨l, hl⟩ := hex
    have hrc : ∃ er, (σ.doms d).caps s = some er ∧ er.lineage = some l := by
      unfold removedCell at hl
      cases hrc0 : (σ.doms d).caps s with
      | none => rw [hrc0] at hl; simp at hl
      | some er => rw [hrc0] at hl; simp only [Option.bind_some] at hl; exact ⟨er, rfl, hl⟩
    obtain ⟨er, herc, herl⟩ := hrc
    exact (h.doms d).ptr_inj s0 s e0 er l (by exact hc0) herc (hle0.trans hl) herl
  constructor
  · intro d'; have hd := h.doms d'
    refine ⟨fun s0 => by rw [hgen]; split; exact bumpGen_pos _; exact hd.gen_pos s0, ?_, ?_, ?_,
      ?_, ?_⟩
    · -- cell_backed
      intro s0 e0 l0 he0 hle0
      have hne : ¬ (d' = d ∧ s0 = s) := fun hc => by
        rw [hcaps, if_pos hc] at he0; simp at he0
      rw [hcaps, if_neg hne] at he0
      rw [hlin]
      by_cases hif : d' = d ∧ removedCell σ d s = some l0
      · exfalso; obtain ⟨rfl, hrm⟩ := hif
        have : s0 = s := hrmowner s0 e0 he0 (by rw [hle0, hrm]) (by rw [hrm]; simp)
        exact hne ⟨rfl, this⟩
      · rw [if_neg hif]; exact hd.cell_backed s0 e0 l0 he0 hle0
    · -- ptr_inj
      intro s1 s2 e1 e2 l0 he1 he2 hl1 hl2
      have hne1 : ¬ (d' = d ∧ s1 = s) := fun hc => by rw [hcaps, if_pos hc] at he1; simp at he1
      have hne2 : ¬ (d' = d ∧ s2 = s) := fun hc => by rw [hcaps, if_pos hc] at he2; simp at he2
      rw [hcaps, if_neg hne1] at he1; rw [hcaps, if_neg hne2] at he2
      exact hd.ptr_inj s1 s2 e1 e2 l0 he1 he2 hl1 hl2
    · -- cell_used
      intro l0 hl0
      rw [hlin] at hl0
      by_cases hif : d' = d ∧ removedCell σ d s = some l0
      · rw [if_pos hif] at hl0; simp at hl0
      · rw [if_neg hif] at hl0
        obtain ⟨s0, e0, hc0, he0⟩ := hd.cell_used l0 hl0
        have hne : ¬ (d' = d ∧ s0 = s) := by
          rintro ⟨hd0, hs0⟩
          rw [hd0, hs0] at hc0
          have hrm : removedCell σ d s = some l0 := by
            rw [removedCell, hc0]; simp only [Option.bind_some]; exact he0
          exact hif ⟨hd0, hrm⟩
        exact ⟨s0, e0, by rw [hcaps, if_neg hne]; exact hc0, he0⟩
    · intro s0 base len p hcase
      have hne : ¬ (d' = d ∧ s0 = s) := by
        rintro ⟨rfl, rfl⟩; rcases hcase with hc | ⟨l, hc⟩ <;>
          (rw [hcaps, if_pos ⟨rfl, rfl⟩] at hc; simp at hc)
      rcases hcase with hc | ⟨l, hc⟩
      · rw [hcaps, if_neg hne] at hc; exact hd.wx s0 base len p (Or.inl hc)
      · rw [hcaps, if_neg hne] at hc; exact hd.wx s0 base len p (Or.inr ⟨l, hc⟩)
    · intro s0 e0 base len p hc hk
      have hne : ¬ (d' = d ∧ s0 = s) := by
        rintro ⟨rfl, rfl⟩; rw [hcaps, if_pos ⟨rfl, rfl⟩] at hc; simp at hc
      rw [hcaps, if_neg hne] at hc; exact hd.bounds s0 e0 base len p hc hk
  · -- parent_live
    intro d' s0 p hp
    -- parentOf survives unchanged
    have hpσ : σ.parentOf d' s0 = some p := by
      have hpc : (σ3.doms d').caps s0 = (σ.doms d').caps s0 := by
        rw [hcaps]; by_cases hne : d' = d ∧ s0 = s
        · exfalso
          have hn : σ3.parentOf d' s0 = none := by
            unfold MachineState.parentOf; rw [hcaps, if_pos hne]
            simp [Option.bind_eq_bind]
          rw [hn] at hp; simp at hp
        · rw [if_neg hne]
      have hpar3 : σ3.parentOf d' s0 = some p := hp
      unfold MachineState.parentOf at hpar3 ⊢
      rw [hpc] at hpar3
      cases hc0 : (σ.doms d').caps s0 with
      | none => simp [hc0, Option.bind_eq_bind] at hpar3
      | some e0 =>
          cases hle0 : e0.lineage with
          | none => simp [hc0, hle0, Option.bind_eq_bind] at hpar3
          | some l0 =>
              simp only [hc0, hle0, hlin, Option.bind_eq_bind, Option.bind_some] at hpar3 ⊢
              split at hpar3
              · simp at hpar3
              · exact hpar3
    have hpl := h.parent_live d' s0 p hpσ
    have hpne : ¬ (p.dom = d ∧ p.slot = s) := by
      rintro ⟨hpd, hps⟩
      have hpg : p.gen = (σ.doms d).slotGen s := by
        unfold MachineState.liveRef DomainState.liveCap at hpl
        rw [hpd, hps] at hpl
        cases hcp : (σ.doms d).caps s with
        | none => rw [hcp] at hpl; simp at hpl
        | some e =>
            rw [hcp] at hpl
            simp only [Option.isSome_dite, Option.isSome_some] at hpl
            by_cases hgg : (decide ((σ.doms d).slotGen s = p.gen) && (p.gen != 0)) = true
            · simp only [Bool.and_eq_true, decide_eq_true_eq] at hgg; exact hgg.1.symm
            · rw [if_neg hgg] at hpl; simp at hpl
      have hpeq : p = ⟨d, s, (σ.doms d).slotGen s⟩ := by
        cases p; simp only [CapRef.mk.injEq]; exact ⟨hpd, hps, hpg⟩
      rw [hpeq] at hpσ; exact hno d' s0 hpσ
    exact hlr p hpl hpne
  · -- region_backed
    intro d' r rg hrg
    have hrg' : (σ1.doms d').regions r = some rg ∧ σ1.liveRef rg.backing = true := by
      have hh : (σ3.doms d').regions r = ((σ1.sweepRegions).doms d').regions r := by
        rw [hσ3, sweepMover_doms]
      rw [hh] at hrg
      unfold MachineState.sweepRegions at hrg; simp only at hrg
      split at hrg
      · next rg0 hr0 =>
          split at hrg
          · next hlv => simp only [Option.some.injEq] at hrg; subst hrg; exact ⟨hr0, hlv⟩
          · next => simp at hrg
      · next => simp at hrg
    have hrgσ : (σ.doms d').regions r = some rg := by
      have hh2 : (σ1.doms d').regions r = (σ.doms d').regions r := by rw [hσ1, clearSlot_regions]
      rw [← hh2]; exact hrg'.1
    obtain ⟨e, hlive, hle⟩ := h.region_backed d' r rg hrgσ
    have hbne : ¬ (rg.backing.dom = d ∧ rg.backing.slot = s) := by
      rintro ⟨hbd, hbs⟩
      have hd0 := hrg'.2; rw [hσ1] at hd0
      unfold MachineState.liveRef DomainState.liveCap at hd0
      rw [show ((σ.clearSlot d s).doms rg.backing.dom).caps rg.backing.slot = none from by
        rw [clearSlot_caps, if_pos ⟨hbd, hbs⟩]] at hd0; simp at hd0
    exact ⟨e, hlc rg.backing.dom rg.backing.slot rg.backing.gen e hbne hlive, hle⟩
  · -- mover_wf
    intro job hj
    have hmvsome : σ1.liveRef job.src = true ∧ σ1.liveRef job.dst = true ∧
        σ.mover = some job := by
      have hj3 : (σ1.sweepRegions).sweepMover.mover = some job := by rw [← hσ3]; exact hj
      obtain ⟨hm0, hl1, hl2⟩ := sweepMover_mover_some (σ1.sweepRegions) job hj3
      rw [sweepRegions_liveRef] at hl1 hl2
      refine ⟨hl1, hl2, ?_⟩
      have hmm : (σ1.sweepRegions).mover = σ.mover := by
        rw [sweepRegions_mover, hσ1, clearSlot_mover]
      rw [← hmm]; exact hm0
    obtain ⟨hs1, hs2, hjeq⟩ := hmvsome
    obtain ⟨o1, o2, o3, o4⟩ := h.mover_wf job hjeq
    have hb1 : ¬ (job.src.dom = d ∧ job.src.slot = s) := by
      rintro ⟨hd0, hs0⟩; rw [hσ1] at hs1
      unfold MachineState.liveRef DomainState.liveCap at hs1
      rw [show ((σ.clearSlot d s).doms job.src.dom).caps job.src.slot = none from by
        rw [clearSlot_caps, if_pos ⟨hd0, hs0⟩]] at hs1; simp at hs1
    have hb2 : ¬ (job.dst.dom = d ∧ job.dst.slot = s) := by
      rintro ⟨hd0, hs0⟩; rw [hσ1] at hs2
      unfold MachineState.liveRef DomainState.liveCap at hs2
      rw [show ((σ.clearSlot d s).doms job.dst.dom).caps job.dst.slot = none from by
        rw [clearSlot_caps, if_pos ⟨hd0, hs0⟩]] at hs2; simp at hs2
    exact ⟨o1, o2, hlr job.src o3 hb1, hlr job.dst o4 hb2⟩
  · intro g a; rw [hgates]; intro ha
    obtain ⟨s1, s2, s3, s4⟩ := h.gate_serving g a ha
    exact ⟨by rw [hserv]; exact s1, by rw [hrun]; exact s2, s3, s4⟩
  · intro d' g; rw [hserv]; intro hs; rw [hgates]; exact h.serving_gate d' g hs
  · intro d' g; rw [hrun]; intro hb; rw [hgates]; exact h.blocked_gate d' g hb
  · intro fl hfl; rw [hinf] at hfl; rw [hrun]; exact h.inflight_running fl hfl


/-- After reparenting `ref`'s children onto `new ≠ ref`, no cell points at
`ref`. The `hno` hypothesis `wf_clearSlot_sweep` needs for `cap_drop`'s
reparent branch (`new` is `ref`'s parent, distinct from `ref` by acyclicity). -/
theorem reparent_no_ref (σ : MachineState) (ref new : CapRef) (hne : new ≠ ref)
    (dd : DomainId) (ss : Slot) :
    (σ.reparent ref new).parentOf dd ss ≠ some ref := by
  intro hp
  unfold MachineState.parentOf at hp
  have hcaps : ((σ.reparent ref new).doms dd).caps = (σ.doms dd).caps := rfl
  rw [hcaps] at hp
  cases hc0 : (σ.doms dd).caps ss with
  | none => simp [hc0, Option.bind_eq_bind] at hp
  | some e0 =>
      cases hle0 : e0.lineage with
      | none => simp [hc0, hle0, Option.bind_eq_bind] at hp
      | some l0 =>
          have hlin : ((σ.reparent ref new).doms dd).lineage l0 =
              match (σ.doms dd).lineage l0 with
              | some cell => some (if cell.parent = ref then { parent := new } else cell)
              | none => none := rfl
          simp only [hc0, hle0, hlin, Option.bind_eq_bind, Option.bind_some] at hp
          cases hcc : (σ.doms dd).lineage l0 with
          | none => rw [hcc] at hp; simp at hp
          | some cell =>
              rw [hcc] at hp
              simp only [Option.bind_some] at hp
              by_cases hpp : cell.parent = ref
              · rw [if_pos hpp] at hp; exact hne (Option.some.inj hp)
              · rw [if_neg hpp] at hp; exact hpp (Option.some.inj hp)


/-- After orphaning `ref`'s children (clearing their cells), no cell points
at `ref`. The `hno` hypothesis for `cap_drop`'s root-drop branch. -/
theorem orphan_no_ref (σ : MachineState) (ref : CapRef) (dd : DomainId) (ss : Slot) :
    (σ.orphanChildren ref).parentOf dd ss ≠ some ref := by
  intro hp
  unfold MachineState.parentOf at hp
  rw [orphanChildren_caps] at hp
  cases hc0 : (σ.doms dd).caps ss with
  | none => simp [hc0, Option.bind_eq_bind] at hp
  | some e0 =>
      cases hle0 : e0.lineage with
      | none => simp [hc0, hle0, Option.bind_eq_bind] at hp
      | some l0 =>
          cases hcc : (σ.doms dd).lineage l0 with
          | none =>
              simp only [hc0, hle0, hcc, Option.bind_eq_bind, Option.bind_some,
                Bool.false_eq_true, if_false, orphanChildren_lineage] at hp
              simp [hcc] at hp
          | some cell =>
              by_cases hpe : cell.parent = ref <;>
                simp [hc0, hle0, hcc, hpe, Option.bind_eq_bind, orphanChildren_lineage] at hp



/-- `clearSlot` only removes parent links: for every reference its parent is
either unchanged or dropped to `none`. -/
theorem clearSlot_parentRef_le (σ : MachineState) (d : DomainId) (s : Slot) (r : CapRef) :
    (σ.clearSlot d s).parentRef r = σ.parentRef r ∨ (σ.clearSlot d s).parentRef r = none := by
  unfold MachineState.parentRef MachineState.parentOf
  rw [clearSlot_caps]
  by_cases hds : r.dom = d ∧ r.slot = s
  · right; rw [if_pos hds]; rfl
  · rw [if_neg hds]
    cases hc : (σ.doms r.dom).caps r.slot with
    | none => left; rfl
    | some e =>
        cases hle : e.lineage with
        | none => left; simp [hle]
        | some l =>
            simp only [hle, Option.bind_eq_bind, Option.bind_some]
            rw [clearSlot_lineage]
            by_cases hlrm : r.dom = d ∧ removedCell σ d s = some l
            · right; rw [if_pos hlrm]; rfl
            · left; rw [if_neg hlrm]

/-- `clearSlot` preserves acyclicity. -/
theorem acyclic_clearSlot (σ : MachineState) (d : DomainId) (s : Slot)
    (hac : Acyclic σ) : Acyclic (σ.clearSlot d s) :=
  acyclic_of_parentRef_le σ _ (clearSlot_parentRef_le σ d s) hac

/-- `orphanChildren` only removes parent links (orphaned caps lose their
lineage index; their cells are freed). -/
theorem orphanChildren_parentRef_le (σ : MachineState) (old : CapRef) (r : CapRef) :
    (σ.orphanChildren old).parentRef r = σ.parentRef r ∨
    (σ.orphanChildren old).parentRef r = none := by
  unfold MachineState.parentRef MachineState.parentOf
  rw [orphanChildren_caps]
  cases hc : (σ.doms r.dom).caps r.slot with
  | none => left; rfl
  | some e =>
      cases hle : e.lineage with
      | none => left; simp [hle]
      | some l =>
          cases hcc : (σ.doms r.dom).lineage l with
          | none =>
              -- not a child (lineage none), cap survives, lineage l stays none
              left; simp only [hle, hcc, Bool.false_eq_true, if_false, Option.bind_eq_bind,
                Option.bind_some, orphanChildren_lineage, hcc]
          | some cell =>
              by_cases hpe : cell.parent = old
              · -- orphaned: cap's lineage cleared
                right; simp [hle, hcc, hpe, Option.bind_eq_bind]
              · -- survives unchanged
                left; simp only [hle, hcc, hpe, decide_false, Bool.false_eq_true, if_false,
                  Option.bind_eq_bind, Option.bind_some, orphanChildren_lineage, hcc]

/-- `orphanChildren` preserves acyclicity. -/
theorem acyclic_orphanChildren (σ : MachineState) (old : CapRef)
    (hac : Acyclic σ) : Acyclic (σ.orphanChildren old) :=
  acyclic_of_parentRef_le σ _ (orphanChildren_parentRef_le σ old) hac

/-- The sweeps leave `caps`/`lineage` untouched, hence acyclicity. -/
theorem acyclic_sweepRegions (σ : MachineState) (hac : Acyclic σ) :
    Acyclic σ.sweepRegions :=
  acyclic_of_parentRef_eq σ _
    (parentRef_eq_of_doms σ _ (fun d => ⟨sweepRegions_caps σ d, sweepRegions_lineage σ d⟩)) hac

theorem acyclic_sweepMover (σ : MachineState) (hac : Acyclic σ) :
    Acyclic σ.sweepMover :=
  acyclic_of_parentRef_eq σ _
    (parentRef_eq_of_doms σ _ (fun d => by
      constructor
      · rw [sweepMover_doms]
      · rw [sweepMover_doms])) hac


/-- `reparent ref new` reroutes exactly the links into `ref` onto `new`: its
parent function is `σ`'s with every `some ref` replaced by `some new`. -/
theorem reparent_parentRef (σ : MachineState) (ref new : CapRef) (r : CapRef) :
    (σ.reparent ref new).parentRef r =
      if σ.parentRef r = some ref then some new else σ.parentRef r := by
  unfold MachineState.parentRef MachineState.parentOf
  have hcaps : ((σ.reparent ref new).doms r.dom).caps = (σ.doms r.dom).caps := rfl
  rw [hcaps]
  cases hc : (σ.doms r.dom).caps r.slot with
  | none => simp [hc]
  | some e =>
      cases hle : e.lineage with
      | none => simp [hc, hle]
      | some l =>
          simp only [hc, hle, Option.bind_eq_bind, Option.bind_some]
          have hlin : ((σ.reparent ref new).doms r.dom).lineage l =
              match (σ.doms r.dom).lineage l with
              | some cell => some (if cell.parent = ref then { parent := new } else cell)
              | none => none := rfl
          rw [hlin]
          cases hcc : (σ.doms r.dom).lineage l with
          | none => simp [hcc]
          | some cell =>
              simp only [hcc, Option.bind_some]
              by_cases hpp : cell.parent = ref
              · simp [hpp]
              · simp [hpp]

/-- `reparent`ing `ref`'s children onto its (live) parent `new` preserves
acyclicity: it is the edge contraction that splices `ref` out. -/
theorem acyclic_reparent (σ : MachineState) (ref new : CapRef)
    (hpar : σ.parentRef ref = some new) (hac : Acyclic σ) :
    Acyclic (σ.reparent ref new) :=
  acyclic_contract σ _ ref new hpar (reparent_parentRef σ ref new) hac


/-- Structure of a surviving cap after `orphanChildren`: kind preserved, and
its lineage kept-or-cleared (if kept, the cell is not a child of `old`).
Infrastructure for `wf_orphanChildren` / `cap_drop`'s root-drop branch. -/
theorem orphan_key (σ : MachineState) (old : CapRef) (d : DomainId) (s : Slot)
    (e : CapEntry) (he : ((σ.orphanChildren old).doms d).caps s = some e) :
    ∃ e0, (σ.doms d).caps s = some e0 ∧ e.kind = e0.kind ∧
      (e.lineage = none ∨
       (e.lineage = e0.lineage ∧ ∀ l, e0.lineage = some l →
          ∀ cell, (σ.doms d).lineage l = some cell → cell.parent ≠ old)) := by
  rw [orphanChildren_caps] at he
  split at he
  · next e0 hc0 =>
      split at he
      · next l0 hle0 =>
          split at he
          · next cellf hff =>
              split at he
              · next hpe =>
                  injection he with he; subst e
                  exact ⟨e0, hc0, rfl, Or.inl rfl⟩
              · next hpe =>
                  injection he with he; subst e
                  refine ⟨e0, hc0, rfl, Or.inr ⟨rfl, fun l hl cell hcell => ?_⟩⟩
                  rw [hle0] at hl; simp only [Option.some.injEq] at hl; subst hl
                  rw [hcell] at hff; injection hff with hff; subst hff
                  intro hx; exact hpe (by simp [hx])
          · next hff =>
              injection he with he; subst e
              exact ⟨e0, hc0, rfl, Or.inr ⟨rfl, fun l hl cell hcell => by
                rw [hle0] at hl; simp only [Option.some.injEq] at hl; subst hl
                rw [hcell] at hff; simp at hff⟩⟩
      · next hle0 =>
          injection he with he; subst e
          exact ⟨e0, hc0, rfl, Or.inr ⟨rfl, fun l hl => by rw [hle0] at hl; simp at hl⟩⟩
  · next => simp at he


/-- Orphaning `old`'s children preserves `Wf`: kinds, generations, regions,
gates, and the Mover are untouched; only children's lineage cells are freed. -/
theorem wf_orphanChildren (σ : MachineState) (old : CapRef) (h : Wf σ) :
    Wf (σ.orphanChildren old) := by
  have hlr : ∀ r, (σ.orphanChildren old).liveRef r = σ.liveRef r := by
    intro r; unfold MachineState.liveRef
    exact liveCap_isSome_congr _ _ r.slot r.gen
      (orphanChildren_caps_isSome σ old r.dom r.slot)
      (congrFun (orphanChildren_slotGen σ old r.dom) r.slot)
  have hocK : ∀ d s e0, (σ.doms d).caps s = some e0 →
      ∃ e', ((σ.orphanChildren old).doms d).caps s = some e' ∧ e'.kind = e0.kind := by
    intro d s e0 hc; simp only [orphanChildren_caps, hc]
    cases hl : e0.lineage with
    | none => exact ⟨e0, rfl, rfl⟩
    | some l =>
        refine ⟨_, rfl, ?_⟩
        cases (σ.doms d).lineage l with
        | none => rfl
        | some cell => by_cases hp : cell.parent = old <;> simp [hp]
  constructor
  · intro d; have hd := h.doms d
    refine ⟨fun s => by rw [orphanChildren_slotGen]; exact hd.gen_pos s, ?_, ?_, ?_, ?_, ?_⟩
    · intro s e l he hle
      obtain ⟨e0, hc0, _, hlin⟩ := orphan_key σ old d s e he
      rcases hlin with hn | ⟨heq, hnc⟩
      · rw [hn] at hle; simp at hle
      · have hle0 : e0.lineage = some l := by rw [← heq]; exact hle
        have hcb := hd.cell_backed s e0 l hc0 hle0
        rw [orphanChildren_lineage]
        cases hcc : (σ.doms d).lineage l with
        | none => rw [hcc] at hcb; simp at hcb
        | some cell => have hpar : cell.parent ≠ old := hnc l hle0 cell hcc
                       simp [hcc, hpar]
    · intro s s' e e' l he he' hl hl'
      obtain ⟨e0, hc0, _, hlin⟩ := orphan_key σ old d s e he
      obtain ⟨e0', hc0', _, hlin'⟩ := orphan_key σ old d s' e' he'
      have hle0 : e0.lineage = some l := by
        rcases hlin with hn | ⟨heq, _⟩
        · rw [hn] at hl; simp at hl
        · rw [← heq]; exact hl
      have hle0' : e0'.lineage = some l := by
        rcases hlin' with hn | ⟨heq, _⟩
        · rw [hn] at hl'; simp at hl'
        · rw [← heq]; exact hl'
      exact hd.ptr_inj s s' e0 e0' l hc0 hc0' hle0 hle0'
    · intro l hl
      rw [orphanChildren_lineage] at hl
      cases hcc : (σ.doms d).lineage l with
      | none => rw [hcc] at hl; simp at hl
      | some cell =>
          by_cases hpe : cell.parent = old
          · rw [hcc] at hl; simp [hpe] at hl
          · obtain ⟨s, e0, hc0, he0⟩ := hd.cell_used l (by rw [hcc]; rfl)
            obtain ⟨k0, ln0⟩ := e0; simp only at he0; subst he0
            exact ⟨s, ⟨k0, some l⟩, by
              simp only [orphanChildren_caps, hc0, hcc, hpe, decide_false,
                Bool.false_eq_true, if_false], rfl⟩
    · intro s base len p hcase
      rcases hcase with hc | ⟨l, hc⟩ <;>
        · obtain ⟨e0, hc0, hk, _⟩ := orphan_key σ old d s _ hc
          rcases e0 with ⟨k0, ln0⟩; simp only at hk; subst hk
          exact hd.wx s base len p (by cases ln0 <;> [exact Or.inl hc0; exact Or.inr ⟨_, hc0⟩])
    · intro s e base len p hc hk
      obtain ⟨e0, hc0, hkk, _⟩ := orphan_key σ old d s e hc
      exact hd.bounds s e0 base len p hc0 (by rw [← hkk]; exact hk)
  · intro d s p hp
    rw [hlr]
    apply h.parent_live d s p
    revert hp; unfold MachineState.parentOf
    cases hc0 : ((σ.orphanChildren old).doms d).caps s with
    | none => simp
    | some e =>
        obtain ⟨e0, hc0', _, hlin⟩ := orphan_key σ old d s e hc0
        cases hle : e.lineage with
        | none => simp [hle]
        | some l =>
            rcases hlin with hn | ⟨heq, hnc⟩
            · rw [hn] at hle; simp at hle
            · have hle0 : e0.lineage = some l := by rw [← heq]; exact hle
              simp only [hle, Option.bind_eq_bind, Option.bind_some, hc0']
              rw [hle0]; simp only [Option.bind_eq_bind, Option.bind_some, orphanChildren_lineage]
              cases hcc : (σ.doms d).lineage l with
              | none => simp [hcc]
              | some cell => have hpar : cell.parent ≠ old := hnc l hle0 cell hcc
                             simp [hcc, hpar]
  · intro d r rg hrg
    rw [orphanChildren_regions] at hrg
    obtain ⟨e, hlv, hle⟩ := h.region_backed d r rg hrg
    have hce : (σ.doms rg.backing.dom).caps rg.backing.slot = some e ∧
        (decide ((σ.doms rg.backing.dom).slotGen rg.backing.slot = rg.backing.gen)
          && rg.backing.gen != 0) = true := by
      unfold DomainState.liveCap at hlv
      cases hc : (σ.doms rg.backing.dom).caps rg.backing.slot with
      | none => simp [hc] at hlv
      | some e0 =>
          simp only [hc] at hlv
          by_cases hg : (decide ((σ.doms rg.backing.dom).slotGen rg.backing.slot = rg.backing.gen)
            && rg.backing.gen != 0) = true
          · rw [if_pos hg] at hlv; exact ⟨hlv, hg⟩
          · rw [if_neg hg] at hlv; exact absurd hlv (by simp)
    obtain ⟨hcaps, hg⟩ := hce
    obtain ⟨e', hoc, hk⟩ := hocK rg.backing.dom rg.backing.slot e hcaps
    refine ⟨e', ?_, by rw [hk]; exact hle⟩
    unfold DomainState.liveCap
    simp only [orphanChildren_slotGen, hoc, if_pos hg]
  · intro job; rw [orphanChildren_mover]; intro hj
    obtain ⟨o1, o2, o3, o4⟩ := h.mover_wf job hj
    exact ⟨o1, o2, by rw [hlr]; exact o3, by rw [hlr]; exact o4⟩
  · intro g a; rw [orphanChildren_gates]; intro ha
    obtain ⟨s1, s2, s3, s4⟩ := h.gate_serving g a ha
    exact ⟨by rw [orphanChildren_serving]; exact s1, by rw [orphanChildren_run]; exact s2, s3, s4⟩
  · intro d g; rw [orphanChildren_serving]; intro hs; rw [orphanChildren_gates]
    exact h.serving_gate d g hs
  · intro d g; rw [orphanChildren_run]; intro hb; rw [orphanChildren_gates]
    exact h.blocked_gate d g hb
  · intro fl hfl; rw [orphanChildren_inflight] at hfl; rw [orphanChildren_run]
    exact h.inflight_running fl hfl


/-- The core of `cap_drop`: reparent-or-orphan the dropped capability's
children, then `clearSlot` + sweeps. Preserves both `Wf` and `Acyclic`. This
assembles every `cap_drop` preservation lemma (`wf_reparent`/`wf_orphanChildren`,
`reparent_no_ref`/`orphan_no_ref`, `Acyclic.parentRef_ne`, `wf_clearSlot_sweep`,
and the acyclicity transports). -/
theorem dropCore_preserves (σ : MachineState) (d : DomainId) (s : Slot)
    (hwf : Wf σ) (hac : Acyclic σ) :
    Wf (((((match σ.parentOf d s with
            | some p => σ.reparent ⟨d, s, (σ.doms d).slotGen s⟩ p
            | none => σ.orphanChildren ⟨d, s, (σ.doms d).slotGen s⟩).clearSlot d s)
          ).sweepRegions).sweepMover)
    ∧ Acyclic (((((match σ.parentOf d s with
            | some p => σ.reparent ⟨d, s, (σ.doms d).slotGen s⟩ p
            | none => σ.orphanChildren ⟨d, s, (σ.doms d).slotGen s⟩).clearSlot d s)
          ).sweepRegions).sweepMover) := by
  set ref : CapRef := ⟨d, s, (σ.doms d).slotGen s⟩ with href
  have hpref : σ.parentRef ref = σ.parentOf d s := by
    unfold MachineState.parentRef; rw [href]
  cases hpo : σ.parentOf d s with
  | some p =>
      -- reparent branch
      have hplive : σ.liveRef p = true := hwf.parent_live d s p hpo
      have hpne : p ≠ ref := hac.parentRef_ne σ ref p (by rw [hpref, hpo])
      set σ' := σ.reparent ref p with hσ'
      have hwf' : Wf σ' := wf_reparent σ ref p hplive hwf
      have hac' : Acyclic σ' := acyclic_reparent σ ref p (by rw [hpref, hpo]) hac
      have hslot : (σ'.doms d).slotGen s = (σ.doms d).slotGen s := rfl
      have hno : ∀ dd ss, σ'.parentOf dd ss ≠ some ⟨d, s, (σ'.doms d).slotGen s⟩ := by
        intro dd ss; rw [hslot, ← href]; exact reparent_no_ref σ ref p hpne dd ss
      refine ⟨?_, ?_⟩
      · simp only [hpo]
        exact wf_clearSlot_sweep σ' d s hno hwf'
      · simp only [hpo]
        exact acyclic_sweepMover _ (acyclic_sweepRegions _ (acyclic_clearSlot σ' d s hac'))
  | none =>
      -- orphan branch
      set σ' := σ.orphanChildren ref with hσ'
      have hwf' : Wf σ' := wf_orphanChildren σ ref hwf
      have hac' : Acyclic σ' := acyclic_orphanChildren σ ref hac
      have hslot : (σ'.doms d).slotGen s = (σ.doms d).slotGen s :=
        congrFun (orphanChildren_slotGen σ ref d) s
      have hno : ∀ dd ss, σ'.parentOf dd ss ≠ some ⟨d, s, (σ'.doms d).slotGen s⟩ := by
        intro dd ss; rw [hslot, ← href]; exact orphan_no_ref σ ref dd ss
      refine ⟨?_, ?_⟩
      · simp only [hpo]
        exact wf_clearSlot_sweep σ' d s hno hwf'
      · simp only [hpo]
        exact acyclic_sweepMover _ (acyclic_sweepRegions _ (acyclic_clearSlot σ' d s hac'))


/-- `installDerived` into a free slot/cell adds the parent link at exactly the
`(d, s)` references (its parent function is `σ`'s plus `some parent` at every
`⟨d, s, ·⟩`). Requires the target slot and cell to be free (as `freeSlot`/
`freeCell` guarantee) and `Wf σ` (so no other cap uses the freed cell). -/
theorem installDerived_parentRef (σ : MachineState) (d : DomainId) (s : Slot)
    (l : LineageId) (kind : CapKind) (parent : CapRef)
    (hs : (σ.doms d).caps s = none) (hl : (σ.doms d).lineage l = none)
    (hwf : Wf σ) (r : CapRef) :
    (σ.installDerived d s l kind parent).1.parentRef r =
      if r.dom = d ∧ r.slot = s then some parent else σ.parentRef r := by
  set σ' := (σ.installDerived d s l kind parent).1 with hσ'
  have hcaps : ∀ d' s', (σ'.doms d').caps s' =
      if d' = d ∧ s' = s then some ⟨kind, some l⟩ else (σ.doms d').caps s' := by
    intro d' s'; rw [hσ']; unfold MachineState.installDerived MachineState.setDom; simp only
    by_cases hd : d' = d
    · subst hd; rw [Loom.Fun.update_same]
      by_cases hss : s' = s
      · subst hss; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hss, hss]
    · simp [Loom.Fun.update_ne _ _ _ _ hd, hd]
  have hlin : ∀ d' l', (σ'.doms d').lineage l' =
      if d' = d ∧ l' = l then some ⟨parent⟩ else (σ.doms d').lineage l' := by
    intro d' l'; rw [hσ']; unfold MachineState.installDerived MachineState.setDom; simp only
    by_cases hd : d' = d
    · subst hd; rw [Loom.Fun.update_same]
      by_cases hll : l' = l
      · subst hll; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hll, hll]
    · simp [Loom.Fun.update_ne _ _ _ _ hd, hd]
  unfold MachineState.parentRef MachineState.parentOf
  rw [hcaps r.dom r.slot]
  by_cases hp : r.dom = d ∧ r.slot = s
  · simp only [if_pos hp, Option.bind_eq_bind, Option.bind_some]
    rw [hlin r.dom l, if_pos ⟨hp.1, rfl⟩]
    rfl
  · simp only [if_neg hp]
    cases hc : (σ.doms r.dom).caps r.slot with
    | none => simp [hc, Option.bind_eq_bind]
    | some e =>
        cases hle : e.lineage with
        | none => simp [hc, hle]
        | some l' =>
            simp only [hc, hle, Option.bind_eq_bind, Option.bind_some]
            rw [hlin r.dom l']
            have hll : ¬ (r.dom = d ∧ l' = l) := by
              rintro ⟨hrd, hll⟩; subst hll
              have := (hwf.doms r.dom).cell_backed r.slot e l' hc hle
              rw [hrd, hl] at this; simp at this
            rw [if_neg hll]

/-- `installDerived` into a free slot/cell preserves acyclicity: it is a
fresh-leaf addition (nothing points to a dead ref, by `Wf`; the parent is live
so it is not the new ref). -/
theorem acyclic_installDerived (σ : MachineState) (d : DomainId) (s : Slot)
    (l : LineageId) (kind : CapKind) (parent : CapRef)
    (hs : (σ.doms d).caps s = none) (hl : (σ.doms d).lineage l = none)
    (hplive : σ.liveRef parent = true) (hwf : Wf σ) (hac : Acyclic σ) :
    Acyclic (σ.installDerived d s l kind parent).1 := by
  refine acyclic_add_leaves σ _ (fun r => decide (r.dom = d ∧ r.slot = s)) parent ?_ ?_ ?_ hac
  · -- no p-ref is parent: parent is live, but (d,s) is empty
    intro a hpa heq; subst heq
    simp only [decide_eq_true_eq] at hpa
    unfold MachineState.liveRef DomainState.liveCap at hplive
    rw [hpa.1, hpa.2, hs] at hplive; simp at hplive
  · -- parentRef characterization
    intro r; rw [installDerived_parentRef σ d s l kind parent hs hl hwf r]
    simp only [decide_eq_true_eq]
  · -- nothing points to a p-ref (dead slot) in σ
    intro r a hpa hcyc
    simp only [decide_eq_true_eq] at hpa
    have hlive := hwf.parent_live r.dom r.slot a hcyc
    unfold MachineState.liveRef DomainState.liveCap at hlive
    rw [hpa.1, hpa.2, hs] at hlive; simp at hlive


/-- `destroyMarked` only removes parent links: a marked capability's slot goes
empty (`parentRef` → `none`), a surviving capability whose cell was destroyed
loses its parent (`none`), and all others are unchanged. -/
theorem destroyMarked_parentRef_le (σ : MachineState) (m : DomainId → Slot → Bool)
    (r : CapRef) :
    (σ.destroyMarked m).parentRef r = σ.parentRef r ∨ (σ.destroyMarked m).parentRef r = none := by
  unfold MachineState.parentRef MachineState.parentOf
  have hcaps : ((σ.destroyMarked m).doms r.dom).caps r.slot =
      if m r.dom r.slot then none else (σ.doms r.dom).caps r.slot := rfl
  rw [hcaps]
  by_cases hmk : m r.dom r.slot
  · right; rw [if_pos hmk]; rfl
  · rw [if_neg hmk]
    cases hc : (σ.doms r.dom).caps r.slot with
    | none => left; rfl
    | some e =>
        cases hle : e.lineage with
        | none => left; simp [hle]
        | some l =>
            simp only [hle, Option.bind_eq_bind, Option.bind_some]
            have hlin : ((σ.destroyMarked m).doms r.dom).lineage l =
                if (List.finRange numSlots).any (fun s => m r.dom s &&
                    match (σ.doms r.dom).caps s with
                    | some e => e.lineage == some l | none => false)
                then none else (σ.doms r.dom).lineage l := rfl
            rw [hlin]
            by_cases hcd : (List.finRange numSlots).any (fun s => m r.dom s &&
                    match (σ.doms r.dom).caps s with
                    | some e => e.lineage == some l | none => false)
            · right; rw [if_pos hcd]; rfl
            · left; rw [if_neg hcd]

/-- `destroyMarked` preserves acyclicity (it only removes parent links). The
Acyclic core of `cap_revoke`. -/
theorem acyclic_destroyMarked (σ : MachineState) (m : DomainId → Slot → Bool)
    (hac : Acyclic σ) : Acyclic (σ.destroyMarked m) :=
  acyclic_of_parentRef_le σ _ (destroyMarked_parentRef_le σ m) hac


/-- `allocDerived` preserves acyclicity: it allocates a fresh slot/cell and
`installDerived`s there — a fresh-leaf addition (`acyclic_installDerived`). -/
theorem acyclic_allocDerived (owner : DomainId) (kind : CapKind) (parent : CapRef)
    (σ : MachineState) {hw : Loom.Word32} {σ' : MachineState}
    (hpar : σ.liveRef parent = true) (h : Wf σ) (hac : Acyclic σ)
    (he : Machines.Lnp64u.Isa.allocDerived owner kind parent σ = .ok hw σ') : Acyclic σ' := by
  unfold Machines.Lnp64u.Isa.allocDerived at he
  simp only [SpecM.get, specM_bind] at he
  cases hfs : σ.freeSlot owner with
  | none => rw [hfs] at he; simp [SpecM.raise] at he
  | some s =>
      rw [hfs] at he
      cases hfc : σ.freeCell owner with
      | none => rw [hfc] at he; simp [SpecM.raise] at he
      | some l =>
          rw [hfc] at he
          simp only [SpecM.set, specM_bind, specM_pure] at he
          injection he with _ h2
          have hσ' : σ' = (σ.installDerived owner s l kind parent).1 := by rw [← h2]
          rw [hσ']
          exact acyclic_installDerived σ owner s l kind parent
            (freeSlot_caps_none σ owner hfs) (freeCell_none σ owner hfc) hpar h hac


/-- **The bulk revocation core.** Destroying all descendants of `root` (via
`marks`) plus the sweeps preserves `Wf`. Marking closure (`marks_closed`) gives
`parent_live`: a surviving cell cannot point at a destroyed capability, since it
would itself be a marked descendant. The `cap_revoke` analog of
`wf_clearSlot_sweep`. -/
theorem wf_destroyMarked_sweep (σ : MachineState) (root : CapRef) (h : Wf σ) :
    Wf (((((σ.destroyMarked (σ.marks root)).sweepRegions).sweepMover))) := by
  set m := σ.marks root with hm
  set σ1 := σ.destroyMarked m with hσ1
  set σ3 := (σ1.sweepRegions).sweepMover with hσ3
  have hcaps : ∀ d s, (σ3.doms d).caps s = if m d s then none else (σ.doms d).caps s := by
    intro d s; rw [hσ3, sweepMover_doms, sweepRegions_caps, hσ1, destroyMarked_caps]
  have hgen : ∀ d s, (σ3.doms d).slotGen s =
      if m d s && ((σ.doms d).caps s).isSome then bumpGen ((σ.doms d).slotGen s)
      else (σ.doms d).slotGen s := by
    intro d s; rw [hσ3, sweepMover_doms, sweepRegions_slotGen, hσ1, destroyMarked_slotGen]
  have hrun : ∀ d, (σ3.doms d).run = (σ.doms d).run := by
    intro d; rw [hσ3, sweepMover_doms, sweepRegions_run, hσ1, destroyMarked_run]
  have hserv : ∀ d, (σ3.doms d).serving = (σ.doms d).serving := by
    intro d; rw [hσ3, sweepMover_doms, sweepRegions_serving, hσ1, destroyMarked_serving]
  have hgates : σ3.gates = σ.gates := by rw [hσ3, sweepMover_gates, sweepRegions_gates, hσ1, destroyMarked_gates]
  have hinf : σ3.inflight = σ.inflight := by rw [hσ3, sweepMover_inflight, sweepRegions_inflight, hσ1, destroyMarked_inflight]
  have hlin : ∀ d l, (σ3.doms d).lineage l = ((σ.destroyMarked m).doms d).lineage l := by
    intro d l; rw [hσ3, sweepMover_doms, sweepRegions_lineage, hσ1]
  -- a surviving cap is unmarked; its live ref survives
  have hlc : ∀ dd ss gg e, m dd ss = false → (σ.doms dd).liveCap ss gg = some e →
      (σ3.doms dd).liveCap ss gg = some e := by
    intro dd ss gg e hnm hlive
    unfold DomainState.liveCap at hlive ⊢
    rw [hcaps dd ss, hgen dd ss]
    simp only [hnm, Bool.false_eq_true, if_false, Bool.false_and]
    exact hlive
  have hlr : ∀ r, σ.liveRef r = true → m r.dom r.slot = false → σ3.liveRef r = true := by
    intro r hr hnm
    unfold MachineState.liveRef at hr ⊢; rw [Option.isSome_iff_exists] at hr
    obtain ⟨e, he⟩ := hr; rw [hlc r.dom r.slot r.gen e hnm he]; rfl
  -- caps s = some e in σ3 ⟹ unmarked and caps s = some e in σ
  have hcapσ : ∀ d s e, (σ3.doms d).caps s = some e → m d s = false ∧ (σ.doms d).caps s = some e := by
    intro d s e he; rw [hcaps] at he
    by_cases hmk : m d s
    · rw [if_pos hmk] at he; simp at he
    · simp only [Bool.not_eq_true] at hmk; simp only [hmk, Bool.false_eq_true, if_false] at he; exact ⟨hmk, he⟩
  constructor
  · intro d; have hd := h.doms d
    refine ⟨fun s => by rw [hgen]; split; exact bumpGen_pos _; exact hd.gen_pos s, ?_, ?_, ?_, ?_, ?_⟩
    · -- cell_backed
      intro s e l he hle
      obtain ⟨hnm, hcs⟩ := hcapσ d s e he
      rw [hlin]
      have hlin' : ((σ.destroyMarked m).doms d).lineage l =
          if (List.finRange numSlots).any (fun s' => m d s' &&
              match (σ.doms d).caps s' with | some e' => e'.lineage == some l | none => false)
          then none else (σ.doms d).lineage l := rfl
      rw [hlin']
      have hnd : ¬ (List.finRange numSlots).any (fun s' => m d s' &&
              match (σ.doms d).caps s' with | some e' => e'.lineage == some l | none => false) = true := by
        rw [List.any_eq_true]; rintro ⟨s', _, hs'⟩
        rw [Bool.and_eq_true] at hs'; obtain ⟨hms', hce'⟩ := hs'
        cases hc' : (σ.doms d).caps s' with
        | none => rw [hc'] at hce'; simp at hce'
        | some e' =>
            rw [hc'] at hce'; simp only [beq_iff_eq] at hce'
            have := hd.ptr_inj s s' e e' l hcs hc' hle hce'
            rw [← this] at hms'; rw [hnm] at hms'; simp at hms'
      rw [if_neg hnd]; exact hd.cell_backed s e l hcs hle
    · -- ptr_inj
      intro s s' e e' l he he' hl hl'
      obtain ⟨_, hcs⟩ := hcapσ d s e he
      obtain ⟨_, hcs'⟩ := hcapσ d s' e' he'
      exact hd.ptr_inj s s' e e' l hcs hcs' hl hl'
    · -- cell_used
      intro l hl
      rw [hlin] at hl
      have hlin' : ((σ.destroyMarked m).doms d).lineage l =
          if (List.finRange numSlots).any (fun s' => m d s' &&
              match (σ.doms d).caps s' with | some e' => e'.lineage == some l | none => false)
          then none else (σ.doms d).lineage l := rfl
      rw [hlin'] at hl
      have hnd : ¬ (List.finRange numSlots).any (fun s' => m d s' &&
              match (σ.doms d).caps s' with | some e' => e'.lineage == some l | none => false) = true := by
        intro hb; rw [if_pos hb] at hl; simp at hl
      rw [if_neg hnd] at hl
      obtain ⟨s, e0, hc0, he0⟩ := hd.cell_used l hl
      -- s not marked, else cellDead
      have hnm : m d s = false := by
        by_contra hmk; simp only [Bool.not_eq_false] at hmk
        apply hnd; rw [List.any_eq_true]
        exact ⟨s, List.mem_finRange s, by rw [Bool.and_eq_true]; exact ⟨hmk, by rw [hc0]; simp [he0]⟩⟩
      exact ⟨s, e0, by rw [hcaps]; simp only [hnm, Bool.false_eq_true, if_false]; exact hc0, he0⟩
    · intro s base len p hcase
      rcases hcase with hc | ⟨l, hc⟩ <;> (obtain ⟨_, hcs⟩ := hcapσ d s _ hc)
      · exact hd.wx s base len p (Or.inl hcs)
      · exact hd.wx s base len p (Or.inr ⟨l, hcs⟩)
    · intro s e base len p hc hk
      obtain ⟨_, hcs⟩ := hcapσ d s e hc
      exact hd.bounds s e base len p hcs hk
  · -- parent_live
    intro d s p hp
    have hpσ : σ.parentOf d s = some p := by
      have hpc : (σ3.doms d).caps s = (σ.doms d).caps s := by
        by_cases hmk : m d s
        · exfalso; revert hp; unfold MachineState.parentOf; rw [hcaps]
          simp only [hmk, if_true]; simp
        · simp only [Bool.not_eq_true] at hmk; rw [hcaps]
          simp only [hmk, Bool.false_eq_true, if_false]
      revert hp; unfold MachineState.parentOf; rw [hpc]
      cases hcc : (σ.doms d).caps s with
      | none => simp
      | some e =>
          cases hle : e.lineage with
          | none => simp [hle]
          | some l =>
              simp only [hle, Option.bind_eq_bind, Option.bind_some]; rw [hlin]
              have hdl : ((σ.destroyMarked m).doms d).lineage l =
                  if (List.finRange numSlots).any (fun s' => m d s' &&
                      match (σ.doms d).caps s' with | some e' => e'.lineage == some l | none => false)
                  then none else (σ.doms d).lineage l := rfl
              have : ((σ.destroyMarked m).doms d).lineage l = (σ.doms d).lineage l ∨
                     ((σ.destroyMarked m).doms d).lineage l = none := by
                rw [hdl]; split <;> [right; left] <;> rfl
              rcases this with heq | heq
              · rw [heq]; exact id
              · rw [heq]; simp
    have hmns : m d s = false := by
      by_contra hmk; simp only [Bool.not_eq_false] at hmk
      -- (d,s) marked ⟹ caps s destroyed ⟹ parent_live vacuous; but hp is about σ3.parentOf
      revert hp; unfold MachineState.parentOf; rw [hcaps]; simp only [hmk, if_true]; simp
    -- p not marked (else (d,s) marked by marks_closed)
    have hplive := h.parent_live d s p hpσ
    have hpnm : m p.dom p.slot = false := by
      by_contra hpmk; simp only [Bool.not_eq_false] at hpmk
      have hpg : (σ.doms p.dom).slotGen p.slot = p.gen := by
        unfold MachineState.liveRef DomainState.liveCap at hplive
        cases hcp : (σ.doms p.dom).caps p.slot with
        | none => simp only [hcp] at hplive; simp at hplive
        | some e =>
            simp only [hcp] at hplive
            split at hplive
            · next hgg => exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hgg).1
            · next => simp at hplive
      have := marks_closed σ root d s p hpσ hpg hpmk
      rw [← hm] at this; rw [this] at hmns; simp at hmns
    exact hlr p hplive hpnm
  · -- region_backed
    intro d r rg hrg
    have hrg' : (σ1.doms d).regions r = some rg ∧ σ1.liveRef rg.backing = true := by
      have hh : (σ3.doms d).regions r = ((σ1.sweepRegions).doms d).regions r := by
        rw [hσ3, sweepMover_doms]
      rw [hh] at hrg
      unfold MachineState.sweepRegions at hrg; simp only at hrg
      split at hrg
      · next rg0 hr0 =>
          split at hrg
          · next hlv => simp only [Option.some.injEq] at hrg; subst hrg; exact ⟨hr0, hlv⟩
          · next => simp at hrg
      · next => simp at hrg
    have hrgσ : (σ.doms d).regions r = some rg := by
      have : (σ1.doms d).regions r = (σ.doms d).regions r := by rw [hσ1, destroyMarked_regions]
      rw [← this]; exact hrg'.1
    obtain ⟨e, hlive, hle⟩ := h.region_backed d r rg hrgσ
    have hbnm : m rg.backing.dom rg.backing.slot = false := by
      by_contra hbmk; simp only [Bool.not_eq_false] at hbmk
      have hd0 := hrg'.2; rw [hσ1] at hd0
      unfold MachineState.liveRef DomainState.liveCap at hd0
      rw [show ((σ.destroyMarked m).doms rg.backing.dom).caps rg.backing.slot = none from by
        simp only [destroyMarked_caps, hbmk, if_true]] at hd0; simp at hd0
    exact ⟨e, hlc rg.backing.dom rg.backing.slot rg.backing.gen e hbnm hlive, hle⟩
  · -- mover_wf
    intro job hj
    have hmvsome : σ1.liveRef job.src = true ∧ σ1.liveRef job.dst = true ∧ σ.mover = some job := by
      have hj3 : (σ1.sweepRegions).sweepMover.mover = some job := by rw [← hσ3]; exact hj
      obtain ⟨hm0, hl1, hl2⟩ := sweepMover_mover_some (σ1.sweepRegions) job hj3
      rw [sweepRegions_liveRef] at hl1 hl2
      refine ⟨hl1, hl2, ?_⟩
      rw [sweepRegions_mover] at hm0; rw [hσ1, destroyMarked_mover] at hm0; exact hm0
    obtain ⟨hs1, hs2, hjeq⟩ := hmvsome
    obtain ⟨o1, o2, o3, o4⟩ := h.mover_wf job hjeq
    have hb1 : m job.src.dom job.src.slot = false := by
      by_contra hbmk; simp only [Bool.not_eq_false] at hbmk; rw [hσ1] at hs1
      unfold MachineState.liveRef DomainState.liveCap at hs1
      rw [show ((σ.destroyMarked m).doms job.src.dom).caps job.src.slot = none from by
        simp only [destroyMarked_caps, hbmk, if_true]] at hs1; simp at hs1
    have hb2 : m job.dst.dom job.dst.slot = false := by
      by_contra hbmk; simp only [Bool.not_eq_false] at hbmk; rw [hσ1] at hs2
      unfold MachineState.liveRef DomainState.liveCap at hs2
      rw [show ((σ.destroyMarked m).doms job.dst.dom).caps job.dst.slot = none from by
        simp only [destroyMarked_caps, hbmk, if_true]] at hs2; simp at hs2
    exact ⟨o1, o2, hlr job.src o3 hb1, hlr job.dst o4 hb2⟩
  · intro g a; rw [hgates]; intro ha
    obtain ⟨s1, s2, s3, s4⟩ := h.gate_serving g a ha
    exact ⟨by rw [hserv]; exact s1, by rw [hrun]; exact s2, s3, s4⟩
  · intro d g; rw [hserv]; intro hs; rw [hgates]; exact h.serving_gate d g hs
  · intro d g; rw [hrun]; intro hb; rw [hgates]; exact h.blocked_gate d g hb
  · intro fl hfl; rw [hinf] at hfl; rw [hrun]; exact h.inflight_running fl hfl


/-- `parentRef` after `transferCap`'s recipient install (a `setDom` writing a
fresh slot `s'` holding a cap with lineage `l'`, and cell `l'` = the moved cell):
the new slot points at the moved cell's parent; all others are unchanged. The
`transferCap` analog of `installDerived_parentRef`. -/
theorem setDom_installMove_parentRef (σ : MachineState) (to_ : DomainId) (s' : Slot)
    (l' : LineageId) (kind : CapKind) (cell : LineageCell)
    (hl : (σ.doms to_).lineage l' = none) (hwf : Wf σ) (r : CapRef) :
    (σ.setDom to_ (fun ds =>
      { ds with
        caps := Loom.Fun.update ds.caps s' (some { kind := kind, lineage := some l' })
        lineage := Loom.Fun.update ds.lineage l' (some cell) })).parentRef r =
      if r.dom = to_ ∧ r.slot = s' then some cell.parent else σ.parentRef r := by
  set σ' := σ.setDom to_ (fun ds =>
      { ds with
        caps := Loom.Fun.update ds.caps s' (some { kind := kind, lineage := some l' })
        lineage := Loom.Fun.update ds.lineage l' (some cell) }) with hσ'
  have hcaps : ∀ d' s'', (σ'.doms d').caps s'' =
      if d' = to_ ∧ s'' = s' then some ⟨kind, some l'⟩ else (σ.doms d').caps s'' := by
    intro d' s''; rw [hσ']; unfold MachineState.setDom; simp only
    by_cases hd : d' = to_
    · subst hd; rw [Loom.Fun.update_same]
      by_cases hss : s'' = s'
      · subst hss; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hss, hss]
    · simp [Loom.Fun.update_ne _ _ _ _ hd, hd]
  have hlin : ∀ d' l'' , (σ'.doms d').lineage l'' =
      if d' = to_ ∧ l'' = l' then some cell else (σ.doms d').lineage l'' := by
    intro d' l''; rw [hσ']; unfold MachineState.setDom; simp only
    by_cases hd : d' = to_
    · subst hd; rw [Loom.Fun.update_same]
      by_cases hll : l'' = l'
      · subst hll; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hll, hll]
    · simp [Loom.Fun.update_ne _ _ _ _ hd, hd]
  unfold MachineState.parentRef MachineState.parentOf
  rw [hcaps r.dom r.slot]
  by_cases hp : r.dom = to_ ∧ r.slot = s'
  · simp only [if_pos hp, Option.bind_eq_bind, Option.bind_some]
    rw [hlin r.dom l', if_pos ⟨hp.1, rfl⟩]; rfl
  · simp only [if_neg hp]
    cases hc : (σ.doms r.dom).caps r.slot with
    | none => simp [hc, Option.bind_eq_bind]
    | some e =>
        cases hle : e.lineage with
        | none => simp [hc, hle]
        | some l'' =>
            simp only [hc, hle, Option.bind_eq_bind, Option.bind_some]
            rw [hlin r.dom l'']
            by_cases hpp : r.dom = to_ ∧ l'' = l'
            · exfalso; obtain ⟨hd, hll⟩ := hpp
              have hcb := (hwf.doms r.dom).cell_backed r.slot e l'' hc hle
              rw [hd, hll, hl] at hcb; simp at hcb
            · rw [if_neg hpp]


theorem wf_installMove (σ : MachineState) (d : DomainId) (s : Slot) (l : LineageId)
    (kind : CapKind) (cell : LineageCell)
    (hs : (σ.doms d).caps s = none) (hl : (σ.doms d).lineage l = none)
    (hwx : ∀ base len p, kind = .mem base len p → p.wx = true ∧ base.toNat + len.toNat ≤ memWords)
    (hpar : σ.liveRef cell.parent = true) (h : Wf σ) :
    Wf (σ.setDom d (fun ds =>
      { ds with
        caps := Loom.Fun.update ds.caps s (some { kind := kind, lineage := some l })
        lineage := Loom.Fun.update ds.lineage l (some cell) })) := by
  set σ' := σ.setDom d (fun ds =>
      { ds with
        caps := Loom.Fun.update ds.caps s (some { kind := kind, lineage := some l })
        lineage := Loom.Fun.update ds.lineage l (some cell) }) with hσ'
  have hgen : ∀ d', (σ'.doms d').slotGen = (σ.doms d').slotGen := by
    intro d'; rw [hσ']; unfold MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ hp]
  have hcaps : ∀ d' s', (σ'.doms d').caps s' =
      if d' = d ∧ s' = s then some { kind := kind, lineage := some l } else (σ.doms d').caps s' := by
    intro d' s'; rw [hσ']; unfold MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp only [Loom.Fun.update_same]
      by_cases hss : s' = s
      · subst hss; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hss, hss]
    · simp [Loom.Fun.update_ne _ _ _ _ hp, hp]
  have hlin : ∀ d' l', (σ'.doms d').lineage l' =
      if d' = d ∧ l' = l then some cell else (σ.doms d').lineage l' := by
    intro d' l'; rw [hσ']; unfold MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp only [Loom.Fun.update_same]
      by_cases hll : l' = l
      · subst hll; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hll, hll]
    · simp [Loom.Fun.update_ne _ _ _ _ hp, hp]
  have hrun : ∀ d', (σ'.doms d').run = (σ.doms d').run := by
    intro d'; rw [hσ']; unfold MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ hp]
  have hserv : ∀ d', (σ'.doms d').serving = (σ.doms d').serving := by
    intro d'; rw [hσ']; unfold MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ hp]
  have hreg : ∀ d', (σ'.doms d').regions = (σ.doms d').regions := by
    intro d'; rw [hσ']; unfold MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ hp]
  have hgates : σ'.gates = σ.gates := by rw [hσ']; rfl
  have hmover : σ'.mover = σ.mover := by rw [hσ']; rfl
  have hinf : σ'.inflight = σ.inflight := by rw [hσ']; rfl
  -- live capabilities are preserved (the new slot was free)
  have hlivecap : ∀ (dd : DomainId) (ss : Slot) (gg : Gen) (e : CapEntry),
      (σ.doms dd).liveCap ss gg = some e → (σ'.doms dd).liveCap ss gg = some e := by
    intro dd ss gg e hlc
    have hne : ¬ (dd = d ∧ ss = s) := by
      rintro ⟨rfl, rfl⟩
      unfold DomainState.liveCap at hlc; rw [hs] at hlc; simp at hlc
    unfold DomainState.liveCap at hlc ⊢
    rw [hcaps, if_neg hne, hgen]; exact hlc
  have hliveref : ∀ r, σ.liveRef r = true → σ'.liveRef r = true := by
    intro r hr
    unfold MachineState.liveRef at hr ⊢
    rw [Option.isSome_iff_exists] at hr; obtain ⟨e, he⟩ := hr
    rw [hlivecap r.dom r.slot r.gen e he]; rfl
  constructor
  · intro d'
    have hd := h.doms d'
    constructor
    · intro s0; rw [hgen]; exact hd.gen_pos s0
    · intro s0 e0 l0 he0 hle0
      rw [hlin]
      by_cases hnew : d' = d ∧ s0 = s
      · rw [hcaps, if_pos hnew] at he0; injection he0 with hek
        subst hek; simp only [Option.some.injEq] at hle0; subst hle0
        rw [if_pos ⟨hnew.1, rfl⟩]; simp
      · rw [hcaps, if_neg hnew] at he0
        by_cases hlc : d' = d ∧ l0 = l
        · simp [hlc]
        · rw [if_neg hlc]; exact hd.cell_backed s0 e0 l0 he0 hle0
    · intro s1 s2 e1 e2 l0 he1 he2 hl1 hl2
      by_cases h1 : d' = d ∧ s1 = s <;> by_cases h2 : d' = d ∧ s2 = s
      · obtain ⟨_, rfl⟩ := h1; obtain ⟨_, rfl⟩ := h2; rfl
      · obtain ⟨hdd, rfl⟩ := h1; subst hdd
        rw [hcaps, if_pos (And.intro rfl rfl)] at he1; injection he1 with hek1; subst hek1
        simp only [Option.some.injEq] at hl1; subst hl1
        rw [hcaps, if_neg h2] at he2
        exact absurd (hd.cell_backed s2 e2 l he2 hl2) (by rw [hl]; simp)
      · obtain ⟨hdd, rfl⟩ := h2; subst hdd
        rw [hcaps, if_pos (And.intro rfl rfl)] at he2; injection he2 with hek2; subst hek2
        simp only [Option.some.injEq] at hl2; subst hl2
        rw [hcaps, if_neg h1] at he1
        exact absurd (hd.cell_backed s1 e1 l he1 hl1) (by rw [hl]; simp)
      · rw [hcaps, if_neg h1] at he1; rw [hcaps, if_neg h2] at he2
        exact hd.ptr_inj s1 s2 e1 e2 l0 he1 he2 hl1 hl2
    · intro l0 hl0
      rw [hlin] at hl0
      by_cases hnew : d' = d ∧ l0 = l
      · obtain ⟨hd1, hd2⟩ := hnew; subst l0
        refine ⟨s, { kind := kind, lineage := some l }, ?_, rfl⟩
        rw [hcaps, if_pos ⟨hd1, rfl⟩]
      · rw [if_neg hnew] at hl0
        obtain ⟨s0, e0, hc0, he0⟩ := hd.cell_used l0 hl0
        refine ⟨s0, e0, ?_, he0⟩
        rw [hcaps]; by_cases hns : d' = d ∧ s0 = s
        · exfalso; obtain ⟨hd1, hd2⟩ := hns; rw [hd1, hd2, hs] at hc0
          exact absurd hc0 (by simp)
        · rw [if_neg hns]; exact hc0
    · intro s0 base len p hcase
      by_cases hnew : d' = d ∧ s0 = s
      · rcases hcase with hc | ⟨l0, hc⟩ <;>
          (rw [hcaps, if_pos hnew] at hc
           simp only [Option.some.injEq, CapEntry.mk.injEq] at hc
           exact (hwx base len p hc.1).1)
      · rcases hcase with hc | ⟨l0, hc⟩
        · rw [hcaps, if_neg hnew] at hc; exact hd.wx s0 base len p (Or.inl hc)
        · rw [hcaps, if_neg hnew] at hc; exact hd.wx s0 base len p (Or.inr ⟨l0, hc⟩)
    · intro s0 e0 base len p hc hk
      by_cases hnew : d' = d ∧ s0 = s
      · rw [hcaps, if_pos hnew] at hc
        simp only [Option.some.injEq] at hc; subst hc
        exact (hwx base len p hk).2
      · rw [hcaps, if_neg hnew] at hc; exact hd.bounds s0 e0 base len p hc hk
  · intro d' s0 p0 hpar0
    by_cases hnew : d' = d ∧ s0 = s
    · obtain ⟨hd1, hd2⟩ := hnew
      have hc1 : (σ'.doms d').caps s0 = some { kind := kind, lineage := some l } := by
        rw [hcaps, if_pos ⟨hd1, hd2⟩]
      have hl1 : (σ'.doms d').lineage l = some cell := by
        rw [hlin, if_pos ⟨hd1, rfl⟩]
      have hpeq : σ'.parentOf d' s0 = some cell.parent := by
        simp [MachineState.parentOf, hc1, hl1]
      rw [hpeq] at hpar0; injection hpar0 with hh; subst hh; exact hliveref cell.parent hpar
    · have hpeq : σ'.parentOf d' s0 = σ.parentOf d' s0 := by
        have hcs : (σ'.doms d').caps s0 = (σ.doms d').caps s0 := by rw [hcaps, if_neg hnew]
        unfold MachineState.parentOf; rw [hcs]
        cases hc0 : (σ.doms d').caps s0 with
        | none => rfl
        | some e0 =>
            cases hle0 : e0.lineage with
            | none => simp [hle0]
            | some l0 =>
                have hll : (σ'.doms d').lineage l0 = (σ.doms d').lineage l0 := by
                  rw [hlin]; by_cases hlc : d' = d ∧ l0 = l
                  · exfalso; obtain ⟨he1, he2⟩ := hlc
                    have hcb := (h.doms d').cell_backed s0 e0 l0 hc0 hle0
                    rw [he1, he2, hl] at hcb; simp at hcb
                  · rw [if_neg hlc]
                simp [hle0, hll]
      rw [hpeq] at hpar0; exact hliveref p0 (h.parent_live d' s0 p0 hpar0)
  · intro d' r rg; rw [hreg]; intro hrg
    obtain ⟨e, hl0, hle⟩ := h.region_backed d' r rg hrg
    exact ⟨e, hlivecap _ _ _ _ hl0, hle⟩
  · intro job; rw [hmover]; intro hj
    obtain ⟨o1, o2, o3, o4⟩ := h.mover_wf job hj
    exact ⟨o1, o2, hliveref _ o3, hliveref _ o4⟩
  · intro g a; rw [hgates]; intro ha
    obtain ⟨s1, s2, s3, s4⟩ := h.gate_serving g a ha
    exact ⟨by rw [hserv]; exact s1, by rw [hrun]; exact s2, s3, s4⟩
  · intro d' g; rw [hserv]; intro hs0; rw [hgates]; exact h.serving_gate d' g hs0
  · intro d' g; rw [hrun]; intro hb; rw [hgates]; exact h.blocked_gate d' g hb
  · intro fl' hfl'; rw [hinf] at hfl'; rw [hrun]; exact h.inflight_running fl' hfl'



/-- The shared tail of `transferCap`: after installing `new` and redirecting
`old`'s children to it, clearing `old`'s slot and sweeping preserves `Wf`. The
`reparent` guarantees no surviving cell points at `old` (`reparent_no_ref`), so
`wf_clearSlot_sweep` applies. -/
theorem wf_reparent_clear_sweep (σ₁ : MachineState) (old new : CapRef)
    (hne : new ≠ old) (hnew : σ₁.liveRef new = true)
    (hgen : old.gen = (σ₁.doms old.dom).slotGen old.slot) (h : Wf σ₁) :
    Wf ((((σ₁.reparent old new).clearSlot old.dom old.slot).sweepRegions).sweepMover) := by
  have h2 : Wf (σ₁.reparent old new) := wf_reparent σ₁ old new hnew h
  apply wf_clearSlot_sweep (σ₁.reparent old new) old.dom old.slot ?_ h2
  intro dd ss
  have hno := reparent_no_ref σ₁ old new hne dd ss
  have hgen2 : ((σ₁.reparent old new).doms old.dom).slotGen old.slot =
      (σ₁.doms old.dom).slotGen old.slot := rfl
  rw [hgen2, ← hgen]
  have holdeq : (⟨old.dom, old.slot, old.gen⟩ : CapRef) = old := by cases old; rfl
  rw [holdeq]; exact hno

/-!
The combinator toolkit is complete: `pure`, `bind`, `ite`, and the primitives
`get`/`reg`/`setReg`/`raise`/`require`/`demand`/`updDomPc`/`load`/`store` all
preserve the invariant. Every **base** ALU/branch/memory instruction's `exec`
is a composition of these, so `PreservesWf (baseOp.sem.exec c)` follows
mechanically for each. What remains for a full `ExecPreservesWf` is the eleven
**system** opcodes, whose `exec` calls the capability-kernel operations
(`installDerived`, `clearSlot`, `destroyMarked`, `transferCap`, the region/Mover
sweeps, gate call/return) — proving those preserve `Wf` is exactly T2/T3/T8/T9's
kernel-level content, the irreducible Phase-1 core.
-/


end Machines.Lnp64u
