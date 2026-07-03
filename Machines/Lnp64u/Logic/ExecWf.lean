import Machines.Lnp64u.SpecM
import Machines.Lnp64u.Isa.System
import Machines.Lnp64u.Logic.Wf
import Machines.Lnp64u.Logic.PhaseLemmas

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
