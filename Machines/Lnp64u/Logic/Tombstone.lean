-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Logic.SlotGen
import Machines.Lnp64u.Logic.AcyclicWfa

/-!
# Tombstones, reference fate, and the revoke-forever machinery (T3 support)

The forward-evolution facts `revoke_temporal_safety` needs, packaged as one
transitive step relation `Evo` plus two reachability invariants:

* **`Tombstoned`** — a slot whose generation has saturated at `genRetired`
  with no entry is permanently unusable: `freeSlot` filters retired slots,
  so no instruction ever installs into it again.
* **`RefFate`** — the complete fate of a reference `r` frozen with entry
  kind `k`: it is either still live at its generation with its kind intact
  (in-place mutations never change a kind), strictly outlived (generation
  advanced past it — dead forever by monotonicity), or tombstoned. Every
  machine operation transports `RefFate`.
* **`MoverLiveMem`** — the Mover's destination is always a *live memory*
  capability: `move` checks the class at issue, the sweeps abort the job
  the moment an endpoint dies, and in-place mutations keep kinds.
* **`ClassLineage`** — a derived capability has the same class as its live
  parent (`cap_dup`/`mem_grant` derive within a class, transfer preserves
  entries, drop splices class-uniform chains). This is what makes every
  *marked* descendant of a gate-class root a gate-class capability, which
  can never back a region register or a Mover job.

`Evo` composed over `step` also yields slot-generation monotonicity for the
whole machine — `T3.gen_monotone`'s content — including the two gate opcodes
missing from `SlotGen.lean`'s work-in-progress dispatch.
-/

namespace Machines.Lnp64u

open Loom.Isa SpecM Machines.Lnp64u.Isa

/-! ## The fate vocabulary -/

/-- A permanently dead slot: retired generation, no entry. `freeSlot`
excludes retired slots, so nothing is ever installed here again. -/
def Tombstoned (d : DomainId) (s : Slot) (σ : MachineState) : Prop :=
  (σ.doms d).caps s = none ∧ (σ.doms d).slotGen s = genRetired

/-- The fate of reference `r` carrying entry kind `k`: live-with-kind,
strictly outlived, or tombstoned. Transported by every operation. -/
def RefFate (r : CapRef) (k : CapKind) (σ : MachineState) : Prop :=
  ((σ.doms r.dom).slotGen r.slot = r.gen ∧
    ∃ e, (σ.doms r.dom).caps r.slot = some e ∧ e.kind = k) ∨
  (r.gen.toNat < ((σ.doms r.dom).slotGen r.slot).toNat) ∨
  ((σ.doms r.dom).caps r.slot = none ∧
    (σ.doms r.dom).slotGen r.slot = genRetired ∧ r.gen = genRetired)

/-- The Mover's destination (when a job is active) is a live *memory*
capability. -/
def MoverLiveMem (σ : MachineState) : Prop :=
  ∀ job, σ.mover = some job →
    ∃ e, (σ.doms job.dst.dom).liveCap job.dst.slot job.dst.gen = some e ∧
         e.kind.cls = .mem

/-- The Mover's source (when a job is active) is still live: `sweepMover`
clears the job on any kill touching either watched reference, installs
check both live, and nothing else removes capabilities. -/
def MoverLiveSrc (σ : MachineState) : Prop :=
  ∀ job, σ.mover = some job →
    ∃ e, (σ.doms job.src.dom).liveCap job.src.slot job.src.gen = some e

/-- One-step state evolution: slot generations never decrease, reference
fates and tombstones transport, and the Mover-destination invariant is
preserved. Reflexive and transitive, hence composable along `step`. -/
def Evo (σ σ' : MachineState) : Prop :=
  (∀ d s, ((σ.doms d).slotGen s).toNat ≤ ((σ'.doms d).slotGen s).toNat) ∧
  (∀ r k, RefFate r k σ → RefFate r k σ') ∧
  (∀ d s, Tombstoned d s σ → Tombstoned d s σ') ∧
  (MoverLiveMem σ → MoverLiveMem σ') ∧
  (MoverLiveSrc σ → MoverLiveSrc σ')

theorem Evo.refl (σ : MachineState) : Evo σ σ :=
  ⟨fun _ _ => Nat.le_refl _, fun _ _ h => h, fun _ _ h => h, fun h => h,
   fun h => h⟩

theorem Evo.trans {σ₁ σ₂ σ₃ : MachineState} (h₁ : Evo σ₁ σ₂) (h₂ : Evo σ₂ σ₃) :
    Evo σ₁ σ₃ :=
  ⟨fun d s => le_trans (h₁.1 d s) (h₂.1 d s),
   fun r k h => h₂.2.1 r k (h₁.2.1 r k h),
   fun d s h => h₂.2.2.1 d s (h₁.2.2.1 d s h),
   fun h => h₂.2.2.2.1 (h₁.2.2.2.1 h),
   fun h => h₂.2.2.2.2 (h₁.2.2.2.2 h)⟩

/-- Generations are 8 bits: nothing exceeds `genRetired = 255`. -/
theorem gen_le_retired (g : Gen) : g.toNat ≤ genRetired.toNat := by
  have := g.isLt
  show g.toNat ≤ 255
  omega

@[simp] theorem bumpGen_retired : bumpGen genRetired = genRetired := by
  unfold bumpGen; simp

/-- A dead reference (outlived or tombstoned) is not live. -/
theorem RefFate.liveRef_false {r : CapRef} {k : CapKind} {σ : MachineState}
    (h : RefFate r k σ)
    (hdead : ((σ.doms r.dom).slotGen r.slot = r.gen ∧
        ∃ e, (σ.doms r.dom).caps r.slot = some e ∧ e.kind = k) → False) :
    σ.liveRef r = false := by
  unfold MachineState.liveRef DomainState.liveCap
  rcases h with h1 | h2 | h3
  · exact absurd h1 hdead
  · cases hc : (σ.doms r.dom).caps r.slot with
    | none => simp
    | some e =>
        have hne : (σ.doms r.dom).slotGen r.slot ≠ r.gen := by
          intro heq; rw [heq] at h2; omega
        simp [hne]
  · rw [h3.1]; simp

/-! ## Quiet operations: capability tables and the Mover untouched -/

/-- Both states agree on every domain's `caps`/`lineage`/`slotGen` tables. -/
def TablesEq (σ σ' : MachineState) : Prop :=
  ∀ d, (σ'.doms d).caps = (σ.doms d).caps ∧
       (σ'.doms d).lineage = (σ.doms d).lineage ∧
       (σ'.doms d).slotGen = (σ.doms d).slotGen

/-- A quiet transition: tables and the Mover untouched (registers, memory,
pc, budgets, regions, gates, run states may change freely). -/
def Quiet (σ σ' : MachineState) : Prop :=
  TablesEq σ σ' ∧ σ'.mover = σ.mover

theorem Quiet.refl (σ : MachineState) : Quiet σ σ :=
  ⟨fun _ => ⟨rfl, rfl, rfl⟩, rfl⟩

theorem Quiet.trans {σ₁ σ₂ σ₃ : MachineState} (h₁ : Quiet σ₁ σ₂) (h₂ : Quiet σ₂ σ₃) :
    Quiet σ₁ σ₃ :=
  ⟨fun d => ⟨(h₂.1 d).1.trans (h₁.1 d).1, (h₂.1 d).2.1.trans (h₁.1 d).2.1,
             (h₂.1 d).2.2.trans (h₁.1 d).2.2⟩,
   h₂.2.trans h₁.2⟩

theorem liveCap_congr_of_eq {ds ds' : DomainState} (s : Slot) (g : Gen)
    (hc : ds'.caps = ds.caps) (hg : ds'.slotGen = ds.slotGen) :
    ds'.liveCap s g = ds.liveCap s g := by
  unfold DomainState.liveCap; rw [hc, hg]

/-- The characterization of `liveCap`. -/
theorem liveCap_eq_some (ds : DomainState) (s : Slot) (g : Gen) (e : CapEntry) :
    ds.liveCap s g = some e ↔
      ds.caps s = some e ∧ ds.slotGen s = g ∧ g ≠ 0 := by
  unfold DomainState.liveCap
  cases hc : ds.caps s with
  | none => simp
  | some e0 =>
      constructor
      · intro h
        replace h : (if (decide (ds.slotGen s = g) && (g != 0)) = true
            then some e0 else none) = some e := h
        by_cases hcond : (decide (ds.slotGen s = g) && (g != 0)) = true
        · rw [if_pos hcond] at h
          injection h with h; subst h
          simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hcond
          exact ⟨rfl, hcond.1, hcond.2⟩
        · rw [if_neg hcond] at h; simp at h
      · rintro ⟨h1, h2, h3⟩
        injection h1 with h1; subst h1
        show (if (decide (ds.slotGen s = g) && (g != 0)) = true
            then some e0 else none) = some e0
        rw [if_pos]
        simp only [h2, decide_true, Bool.true_and, bne_iff_ne, ne_eq]
        exact h3

theorem Quiet.evo {σ σ' : MachineState} (h : Quiet σ σ') : Evo σ σ' := by
  obtain ⟨ht, hm⟩ := h
  refine ⟨fun d s => by rw [(ht d).2.2], ?_, ?_, ?_, ?_⟩
  · intro r k hf
    unfold RefFate at hf ⊢
    rw [(ht r.dom).1, (ht r.dom).2.2]; exact hf
  · intro d s hts
    unfold Tombstoned at hts ⊢
    rw [(ht d).1, (ht d).2.2]; exact hts
  · intro hml job hj
    rw [hm] at hj
    obtain ⟨e, he, hcls⟩ := hml job hj
    exact ⟨e, by rw [liveCap_congr_of_eq _ _ (ht job.dst.dom).1 (ht job.dst.dom).2.2]
                 exact he, hcls⟩
  · intro hms job hj
    rw [hm] at hj
    obtain ⟨e, he⟩ := hms job hj
    exact ⟨e, by rw [liveCap_congr_of_eq _ _ (ht job.src.dom).1 (ht job.src.dom).2.2]
                 exact he⟩

/-! ## The `SpecM`-level preservation kits -/

/-- `mm`'s outcomes are quiet transitions. -/
def QuietPres {α : Type} (mm : SpecM α) : Prop :=
  ∀ σ, (∀ a σ', mm σ = .ok a σ' → Quiet σ σ') ∧
       (∀ e σ', mm σ = .err e σ' → Quiet σ σ')

/-- `mm`'s outcomes evolve the state. -/
def EvoPres {α : Type} (mm : SpecM α) : Prop :=
  ∀ σ, (∀ a σ', mm σ = .ok a σ' → Evo σ σ') ∧
       (∀ e σ', mm σ = .err e σ' → Evo σ σ')

theorem EvoPres.of_quiet {α : Type} {mm : SpecM α} (h : QuietPres mm) : EvoPres mm :=
  fun σ => ⟨fun a σ' he => ((h σ).1 a σ' he).evo,
            fun e σ' he => ((h σ).2 e σ' he).evo⟩

theorem QuietPres.of_state_eq {α : Type} (mm : SpecM α)
    (hok : ∀ σ a σ', mm σ = .ok a σ' → σ' = σ)
    (herr : ∀ σ e σ', mm σ = .err e σ' → σ' = σ) : QuietPres mm :=
  fun σ => ⟨fun a σ' he => (hok σ a σ' he) ▸ Quiet.refl σ,
            fun e σ' he => (herr σ e σ' he) ▸ Quiet.refl σ⟩

theorem QuietPres.pure {α : Type} (a : α) : QuietPres (Pure.pure a : SpecM α) :=
  QuietPres.of_state_eq _
    (fun σ a' σ' he => by rw [specM_pure] at he; injection he with _ h2; exact h2.symm)
    (fun σ e σ' he => by rw [specM_pure] at he; simp at he)

theorem QuietPres.bind {α β : Type} {m : SpecM α} {f : α → SpecM β}
    (hm : QuietPres m) (hf : ∀ a, QuietPres (f a)) : QuietPres (m >>= f) := by
  intro σ
  constructor
  · intro b σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he
                 exact Quiet.trans ((hm σ).1 a σ1 hmσ) ((hf a σ1).1 b σ' he)
    | err e σ1 => rw [hmσ] at he; simp at he
    | fault g => rw [hmσ] at he; simp at he
  · intro e σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he
                 exact Quiet.trans ((hm σ).1 a σ1 hmσ) ((hf a σ1).2 e σ' he)
    | err e1 σ1 => rw [hmσ] at he; injection he with h1 h2; subst h2
                   exact (hm σ).2 e1 σ1 hmσ
    | fault g => rw [hmσ] at he; simp at he

theorem EvoPres.bind {α β : Type} {m : SpecM α} {f : α → SpecM β}
    (hm : EvoPres m) (hf : ∀ a, EvoPres (f a)) : EvoPres (m >>= f) := by
  intro σ
  constructor
  · intro b σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he
                 exact Evo.trans ((hm σ).1 a σ1 hmσ) ((hf a σ1).1 b σ' he)
    | err e σ1 => rw [hmσ] at he; simp at he
    | fault g => rw [hmσ] at he; simp at he
  · intro e σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he
                 exact Evo.trans ((hm σ).1 a σ1 hmσ) ((hf a σ1).2 e σ' he)
    | err e1 σ1 => rw [hmσ] at he; injection he with h1 h2; subst h2
                   exact (hm σ).2 e1 σ1 hmσ
    | fault g => rw [hmσ] at he; simp at he

theorem QuietPres.iteBool {α : Type} (b : Bool) {m1 m2 : SpecM α}
    (h1 : QuietPres m1) (h2 : QuietPres m2) : QuietPres (if b then m1 else m2) := by
  cases b
  · simpa using h2
  · simpa using h1

theorem EvoPres.iteBool {α : Type} (b : Bool) {m1 m2 : SpecM α}
    (h1 : EvoPres m1) (h2 : EvoPres m2) : EvoPres (if b then m1 else m2) := by
  cases b
  · simpa using h2
  · simpa using h1

/-! ### Quiet primitives -/

theorem QuietPres.reg (d : DomainId) (r : RegId) : QuietPres (SpecM.reg d r) :=
  QuietPres.of_state_eq _
    (fun σ a σ' he => by unfold SpecM.reg at he; injection he with _ h2; exact h2.symm)
    (fun σ e σ' he => by unfold SpecM.reg at he; simp at he)

theorem QuietPres.get : QuietPres SpecM.get :=
  QuietPres.of_state_eq _
    (fun σ a σ' he => by unfold SpecM.get at he; injection he with _ h2; exact h2.symm)
    (fun σ e σ' he => by unfold SpecM.get at he; simp at he)

theorem QuietPres.raise {α : Type} (e : Errno) : QuietPres (SpecM.raise e : SpecM α) :=
  QuietPres.of_state_eq _
    (fun σ a σ' he => by unfold SpecM.raise at he; simp at he)
    (fun σ e' σ' he => by unfold SpecM.raise at he; injection he with _ h2; exact h2.symm)

theorem QuietPres.require (cond : Bool) (e : Errno) : QuietPres (SpecM.require cond e) :=
  QuietPres.of_state_eq _
    (fun σ a σ' he => (require_ok cond e σ he).symm ▸ rfl)
    (fun σ e' σ' he => (require_err_state cond e σ he).symm ▸ rfl)

theorem QuietPres.demand (cond : Bool) (f : Fault) : QuietPres (SpecM.demand cond f) :=
  QuietPres.of_state_eq _
    (fun σ a σ' he => (demand_ok cond f σ he).symm ▸ rfl)
    (fun σ e σ' he => by
      unfold SpecM.demand at he; split at he
      · simp [specM_pure] at he
      · simp [SpecM.fatal] at he)

theorem QuietPres.load (d : DomainId) (a : Addr) : QuietPres (SpecM.load d a) :=
  QuietPres.of_state_eq _
    (fun σ v σ' he => load_ok d a σ he)
    (fun σ e σ' he => load_err_state d a σ he)

theorem QuietPres.capLive (d : DomainId) (hw : Loom.Word32) :
    QuietPres (Machines.Lnp64u.Isa.capLive d hw) :=
  QuietPres.of_state_eq _
    (fun σ r σ' he => (Machines.Lnp64u.Isa.Wip.capLive_ok d hw σ he).1)
    (fun σ e σ' he => Machines.Lnp64u.Isa.Wip.capLive_err_state d hw σ he)

theorem QuietPres.narrow (base : Addr) (len : BitVec 13) (perms : Perms) (dw : Loom.Word32) :
    QuietPres (Machines.Lnp64u.Isa.narrow base len perms dw) :=
  QuietPres.of_state_eq _
    (fun σ k σ' he => (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms dw σ he).1)
    (fun σ e σ' he => Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms dw σ he)

/-- `setDom` with a tables-preserving update is a quiet transition. -/
theorem quiet_setDom (σ : MachineState) (d : DomainId) (f : DomainState → DomainState)
    (hf : (f (σ.doms d)).caps = (σ.doms d).caps ∧
          (f (σ.doms d)).lineage = (σ.doms d).lineage ∧
          (f (σ.doms d)).slotGen = (σ.doms d).slotGen) :
    Quiet σ (σ.setDom d f) := by
  refine ⟨fun d' => ?_, rfl⟩
  unfold MachineState.setDom
  by_cases h : d' = d
  · subst h; simp only [Loom.Fun.update_same]; exact hf
  · simp [Loom.Fun.update_ne _ _ _ _ h]

theorem QuietPres.updDom (d : DomainId) (f : DomainState → DomainState)
    (hf : ∀ ds : DomainState, (f ds).caps = ds.caps ∧ (f ds).lineage = ds.lineage ∧
          (f ds).slotGen = ds.slotGen) :
    QuietPres (SpecM.updDom d f) := by
  intro σ
  constructor
  · intro a σ' he
    simp only [SpecM.updDom, SpecM.modify] at he; injection he with _ h2; subst h2
    exact quiet_setDom σ d f (hf (σ.doms d))
  · intro e σ' he; simp [SpecM.updDom, SpecM.modify] at he

theorem QuietPres.setReg (d : DomainId) (r : RegId) (v : Loom.Word32) :
    QuietPres (SpecM.setReg d r v) := by
  intro σ
  constructor
  · intro a σ' he
    unfold SpecM.setReg SpecM.modify at he; injection he with _ h2; subst h2
    exact quiet_setDom σ d _ ⟨setReg_caps _ _ _, setReg_lineage _ _ _, setReg_slotGen _ _ _⟩
  · intro e σ' he; simp [SpecM.setReg, SpecM.modify] at he

theorem QuietPres.store (d : DomainId) (a : Addr) (v : Loom.Word32) :
    QuietPres (SpecM.store d a v) := by
  intro σ; unfold SpecM.store
  constructor
  · intro x σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp only [SpecM.demand, hc, if_true, specM_pure, specM_bind, SpecM.set] at he
      injection he with _ h2; subst h2
      exact ⟨fun d' => ⟨rfl, rfl, rfl⟩, rfl⟩
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he
  · intro e σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp [SpecM.demand, hc, specM_pure, specM_bind, SpecM.set] at he
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he

/-- `haltDom` only touches run/serving/cause, gates, and a caller register. -/
theorem quiet_haltDom (σ : MachineState) (d : DomainId) (c : Loom.Word32) :
    Quiet σ (σ.haltDom d c) := by
  unfold MachineState.haltDom
  have hbase : Quiet σ (σ.haltBase d c) := by
    refine ⟨fun d' => ⟨haltBase_caps σ d c d', haltBase_lineage σ d c d', ?_⟩, haltBase_mover σ d c⟩
    exact haltBase_slotGen σ d c d'
  split
  · exact hbase
  · split
    · exact hbase
    · exact Quiet.trans hbase
        ⟨fun d' => ⟨unwindGate_caps _ _ _ _ d', unwindGate_lineage _ _ _ _ d',
                    unwindGate_slotGen _ _ _ _ d'⟩, unwindGate_mover _ _ _ _⟩

/-! ## Kernel-level `Evo` lemmas -/

/-- `Evo` only reads `caps`/`slotGen`/`mover`. -/
theorem evo_of_projs (σ σ' : MachineState)
    (hc : ∀ d, (σ'.doms d).caps = (σ.doms d).caps)
    (hg : ∀ d, (σ'.doms d).slotGen = (σ.doms d).slotGen)
    (hm : σ'.mover = σ.mover) : Evo σ σ' := by
  refine ⟨fun d s => by rw [hg d], ?_, ?_, ?_, ?_⟩
  · intro r k hf; unfold RefFate at hf ⊢; rw [hc r.dom, hg r.dom]; exact hf
  · intro d s hts; unfold Tombstoned at hts ⊢; rw [hc d, hg d]; exact hts
  · intro hml job hj
    rw [hm] at hj
    obtain ⟨e, he, hcls⟩ := hml job hj
    exact ⟨e, by rw [liveCap_congr_of_eq _ _ (hc job.dst.dom) (hg job.dst.dom)]; exact he,
           hcls⟩
  · intro hms job hj
    rw [hm] at hj
    obtain ⟨e, he⟩ := hms job hj
    exact ⟨e, by rw [liveCap_congr_of_eq _ _ (hc job.src.dom) (hg job.src.dom)]; exact he⟩

/-- What `freeSlot` promises about its result: unoccupied and not retired. -/
theorem freeSlot_spec (σ : MachineState) (d : DomainId) (s : Slot)
    (h : σ.freeSlot d = some s) :
    (σ.doms d).caps s = none ∧ (σ.doms d).slotGen s ≠ genRetired := by
  unfold MachineState.freeSlot at h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hp
  exact ⟨hp.1, by simpa using hp.2⟩

/-- Installing an entry into a `freeSlot`-approved slot evolves the state:
the slot was empty and non-retired, so no live reference, tombstone, or
Mover destination is disturbed. -/
theorem evo_capsUpdate (σ : MachineState) (dd : DomainId) (s2 : Slot)
    (enew : Option CapEntry) (f : DomainState → DomainState)
    (hcaps : (f (σ.doms dd)).caps = Loom.Fun.update (σ.doms dd).caps s2 enew)
    (hgen : (f (σ.doms dd)).slotGen = (σ.doms dd).slotGen)
    (hfree : (σ.doms dd).caps s2 = none)
    (hnr : (σ.doms dd).slotGen s2 ≠ genRetired) :
    Evo σ (σ.setDom dd f) := by
  have hcproj : ∀ d' s', ((σ.setDom dd f).doms d').caps s' =
      if d' = dd ∧ s' = s2 then enew else (σ.doms d').caps s' := by
    intro d' s'
    unfold MachineState.setDom
    by_cases hd : d' = dd
    · subst hd
      simp only [Loom.Fun.update_same, hcaps, true_and]
      by_cases hs : s' = s2
      · subst hs; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hs, hs]
    · simp [Loom.Fun.update_ne _ _ _ _ hd, hd]
  have hgproj : ∀ d', ((σ.setDom dd f).doms d').slotGen = (σ.doms d').slotGen := by
    intro d'
    unfold MachineState.setDom
    by_cases hd : d' = dd
    · subst hd; simp only [Loom.Fun.update_same, hgen]
    · simp [Loom.Fun.update_ne _ _ _ _ hd]
  refine ⟨fun d s => by rw [hgproj d], ?_, ?_, ?_, ?_⟩
  · intro r k hf
    unfold RefFate at hf ⊢
    rw [hcproj r.dom r.slot, hgproj r.dom]
    by_cases hrs : r.dom = dd ∧ r.slot = s2
    · rw [if_pos hrs]
      rcases hf with h1 | h2 | h3
      · obtain ⟨_, e, hce, _⟩ := h1
        rw [hrs.1, hrs.2] at hce; rw [hfree] at hce; exact absurd hce (by simp)
      · exact Or.inr (Or.inl h2)
      · rw [hrs.1, hrs.2] at h3; exact absurd h3.2.1 hnr
    · rw [if_neg hrs]; exact hf
  · intro d s hts
    unfold Tombstoned at hts ⊢
    rw [hcproj d s, hgproj d]
    by_cases hrs : d = dd ∧ s = s2
    · rw [hrs.1, hrs.2] at hts; exact absurd hts.2 hnr
    · rw [if_neg hrs]; exact hts
  · intro hml job hj
    rw [show (σ.setDom dd f).mover = σ.mover from rfl] at hj
    obtain ⟨e, he, hcls⟩ := hml job hj
    refine ⟨e, ?_, hcls⟩
    unfold DomainState.liveCap at he ⊢
    rw [hcproj job.dst.dom job.dst.slot, hgproj job.dst.dom]
    have hne : ¬ (job.dst.dom = dd ∧ job.dst.slot = s2) := by
      rintro ⟨h1, h2⟩
      rw [h1, h2, hfree] at he; simp at he
    rw [if_neg hne]; exact he
  · intro hms job hj
    rw [show (σ.setDom dd f).mover = σ.mover from rfl] at hj
    obtain ⟨e, he⟩ := hms job hj
    refine ⟨e, ?_⟩
    unfold DomainState.liveCap at he ⊢
    rw [hcproj job.src.dom job.src.slot, hgproj job.src.dom]
    have hne : ¬ (job.src.dom = dd ∧ job.src.slot = s2) := by
      rintro ⟨h1, h2⟩
      rw [h1, h2, hfree] at he; simp at he
    rw [if_neg hne]; exact he

theorem evo_installDerived (σ : MachineState) (d : DomainId) (s : Slot) (l : LineageId)
    (kind : CapKind) (parent : CapRef) (hfs : σ.freeSlot d = some s) :
    Evo σ (σ.installDerived d s l kind parent).1 := by
  obtain ⟨hfree, hnr⟩ := freeSlot_spec σ d s hfs
  show Evo σ (σ.setDom d fun ds =>
    { ds with
      caps := Loom.Fun.update ds.caps s (some { kind := kind, lineage := some l })
      lineage := Loom.Fun.update ds.lineage l (some { parent := parent }) })
  exact evo_capsUpdate σ d s (some { kind := kind, lineage := some l }) _ rfl rfl hfree hnr

theorem EvoPres.allocDerived (owner : DomainId) (kind : CapKind) (parent : CapRef) :
    EvoPres (Machines.Lnp64u.Isa.allocDerived owner kind parent) := by
  intro σ
  constructor
  · intro hw σ' he
    unfold Machines.Lnp64u.Isa.allocDerived at he
    simp only [SpecM.get, specM_bind] at he
    cases hfs : σ.freeSlot owner with
    | none => rw [hfs] at he; simp [SpecM.raise] at he
    | some sl =>
        rw [hfs] at he
        cases hfc : σ.freeCell owner with
        | none => rw [hfc] at he; simp [SpecM.raise] at he
        | some lc =>
            rw [hfc] at he
            simp only [SpecM.set, specM_bind, specM_pure] at he
            injection he with _ h2
            rw [← h2]
            exact evo_installDerived σ owner sl lc kind parent hfs
  · intro e σ' he
    unfold Machines.Lnp64u.Isa.allocDerived at he
    simp only [SpecM.get, specM_bind] at he
    cases hfs : σ.freeSlot owner with
    | none => rw [hfs] at he; simp only [SpecM.raise] at he
              injection he with _ h2; subst h2; exact Evo.refl _
    | some sl =>
        rw [hfs] at he
        cases hfc : σ.freeCell owner with
        | none => rw [hfc] at he; simp only [SpecM.raise] at he
                  injection he with _ h2; subst h2; exact Evo.refl _
        | some lc => rw [hfc] at he; simp [SpecM.set, specM_bind, specM_pure] at he

theorem evo_reparent (σ : MachineState) (old new : CapRef) :
    Evo σ (σ.reparent old new) :=
  evo_of_projs σ _ (fun _ => rfl) (fun _ => rfl) rfl

/-- `orphanChildren` mutates entries in place (lineage index dropped),
never their kinds, occupancy, or generations. -/
theorem orphanChildren_caps_kind (σ : MachineState) (old : CapRef) (d : DomainId) (s : Slot) :
    (((σ.orphanChildren old).doms d).caps s = none ∧ (σ.doms d).caps s = none) ∨
    (∃ e e', (σ.doms d).caps s = some e ∧
      ((σ.orphanChildren old).doms d).caps s = some e' ∧ e'.kind = e.kind ∧
      (e' = e ∨ e' = { e with lineage := none })) := by
  have h := orphanChildren_caps σ old d s
  cases hc : (σ.doms d).caps s with
  | none => rw [hc] at h; exact Or.inl ⟨h, rfl⟩
  | some e =>
      rw [hc] at h
      replace h : ((σ.orphanChildren old).doms d).caps s
          = (match e.lineage with
             | some l => some (if (match (σ.doms d).lineage l with
                 | some cell => decide (cell.parent = old)
                 | none => false) then { e with lineage := none } else e)
             | none => some e) := h
      cases hl : e.lineage with
      | none =>
          rw [hl] at h
          exact Or.inr ⟨e, e, rfl, h, rfl, Or.inl rfl⟩
      | some l =>
          rw [hl] at h
          replace h : ((σ.orphanChildren old).doms d).caps s
              = some (if (match (σ.doms d).lineage l with
                  | some cell => decide (cell.parent = old)
                  | none => false) then { e with lineage := none } else e) := h
          by_cases hch : (match (σ.doms d).lineage l with
              | some cell => decide (cell.parent = old) | none => false) = true
          · rw [if_pos hch] at h
            exact Or.inr ⟨e, { e with lineage := none }, rfl, h, rfl, Or.inr rfl⟩
          · rw [if_neg hch] at h
            exact Or.inr ⟨e, e, rfl, h, rfl, Or.inl rfl⟩

theorem evo_orphanChildren (σ : MachineState) (old : CapRef) :
    Evo σ (σ.orphanChildren old) := by
  refine ⟨fun d s => by rw [orphanChildren_slotGen], ?_, ?_, ?_, ?_⟩
  · intro r k hf
    unfold RefFate at hf ⊢
    rw [orphanChildren_slotGen]
    rcases hf with h1 | h2 | h3
    · rcases orphanChildren_caps_kind σ old r.dom r.slot with ⟨_, hn⟩ | ⟨e, e', hce, hce', hk, _⟩
      · obtain ⟨_, e, hce, _⟩ := h1; rw [hn] at hce; exact absurd hce (by simp)
      · obtain ⟨hg, e0, hce0, hk0⟩ := h1
        rw [hce] at hce0; injection hce0 with hee; subst hee
        exact Or.inl ⟨hg, e', hce', hk.trans hk0⟩
    · exact Or.inr (Or.inl h2)
    · rcases orphanChildren_caps_kind σ old r.dom r.slot with ⟨hn', _⟩ | ⟨e, e', hce, _, _, _⟩
      · exact Or.inr (Or.inr ⟨hn', h3.2⟩)
      · rw [h3.1] at hce; exact absurd hce (by simp)
  · intro d s hts
    rcases orphanChildren_caps_kind σ old d s with ⟨hn', _⟩ | ⟨e, e', hce, _, _, _⟩
    · exact ⟨hn', by rw [orphanChildren_slotGen]; exact hts.2⟩
    · rw [hts.1] at hce; exact absurd hce (by simp)
  · intro hml job hj
    rw [orphanChildren_mover] at hj
    obtain ⟨e, he, hcls⟩ := hml job hj
    rw [liveCap_eq_some] at he
    obtain ⟨hce, hg, hg0⟩ := he
    rcases orphanChildren_caps_kind σ old job.dst.dom job.dst.slot with
      ⟨_, hn⟩ | ⟨e1, e1', hce1, hce1', hk1, _⟩
    · rw [hn] at hce; exact absurd hce (by simp)
    · rw [hce] at hce1; injection hce1 with hee; subst hee
      refine ⟨e1', ?_, ?_⟩
      · rw [liveCap_eq_some]
        exact ⟨hce1', by rw [orphanChildren_slotGen]; exact hg, hg0⟩
      · rw [show e1'.kind.cls = e.kind.cls from by rw [hk1]]; exact hcls
  · intro hms job hj
    rw [orphanChildren_mover] at hj
    obtain ⟨e, he⟩ := hms job hj
    rw [liveCap_eq_some] at he
    obtain ⟨hce, hg, hg0⟩ := he
    rcases orphanChildren_caps_kind σ old job.src.dom job.src.slot with
      ⟨_, hn⟩ | ⟨e1, e1', hce1, hce1', hk1, _⟩
    · rw [hn] at hce; exact absurd hce (by simp)
    · rw [hce] at hce1; injection hce1 with hee; subst hee
      refine ⟨e1', ?_⟩
      rw [liveCap_eq_some]
      exact ⟨hce1', by rw [orphanChildren_slotGen]; exact hg, hg0⟩

/-- The clear-then-sweep composite (`cap_drop`, `transferCap` tail). -/
theorem evo_clearSweep (σ : MachineState) (d : DomainId) (s : Slot) :
    Evo σ ((((σ.clearSlot d s).sweepRegions).sweepMover)) := by
  have hcaps : ∀ d' s', ((((σ.clearSlot d s).sweepRegions).sweepMover).doms d').caps s' =
      if d' = d ∧ s' = s then none else (σ.doms d').caps s' := by
    intro d' s'; rw [sweepMover_doms, sweepRegions_caps, clearSlot_caps]
  have hgen : ∀ d' s', ((((σ.clearSlot d s).sweepRegions).sweepMover).doms d').slotGen s' =
      if d' = d ∧ s' = s then bumpGen ((σ.doms d).slotGen s)
      else (σ.doms d').slotGen s' := by
    intro d' s'; rw [sweepMover_doms]
    rw [show ((σ.clearSlot d s).sweepRegions.doms d').slotGen s' =
      ((σ.clearSlot d s).doms d').slotGen s' from by rw [sweepRegions_slotGen]]
    exact clearSlot_slotGen σ d s d' s'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d' s'; rw [hgen d' s']
    split
    · rename_i h; rw [h.1, h.2]; exact bumpGen_ge _
    · exact Nat.le_refl _
  · intro r k hf
    unfold RefFate at hf ⊢
    rw [hcaps r.dom r.slot, hgen r.dom r.slot]
    by_cases hrs : r.dom = d ∧ r.slot = s
    · rw [if_pos hrs, if_pos hrs]
      rcases hf with h1 | h2 | h3
      · obtain ⟨hg, _⟩ := h1
        rw [hrs.1, hrs.2] at hg
        by_cases hret : (σ.doms d).slotGen s = genRetired
        · refine Or.inr (Or.inr ⟨rfl, by rw [hret]; exact bumpGen_retired, ?_⟩)
          rw [← hg]; exact hret
        · refine Or.inr (Or.inl ?_)
          rw [← hg]
          exact bumpGen_gt _ hret
      · refine Or.inr (Or.inl (lt_of_lt_of_le ?_ (bumpGen_ge _)))
        rw [hrs.1, hrs.2] at h2; exact h2
      · refine Or.inr (Or.inr ⟨rfl, ?_, h3.2.2⟩)
        rw [hrs.1, hrs.2] at h3
        rw [h3.2.1]; exact bumpGen_retired
    · rw [if_neg hrs, if_neg hrs]; exact hf
  · intro d' s' hts
    unfold Tombstoned at hts ⊢
    rw [hcaps d' s', hgen d' s']
    by_cases hrs : d' = d ∧ s' = s
    · rw [if_pos hrs, if_pos hrs]
      rw [hrs.1, hrs.2] at hts
      exact ⟨rfl, by rw [hts.2]; exact bumpGen_retired⟩
    · rw [if_neg hrs, if_neg hrs]; exact hts
  · intro hml job hj
    obtain ⟨hmv, hsrc, hdst⟩ := sweepMover_mover_some _ job hj
    rw [sweepRegions_mover, clearSlot_mover] at hmv
    obtain ⟨e, he, hcls⟩ := hml job hmv
    rw [liveCap_eq_some] at he
    obtain ⟨hce, hg, hg0⟩ := he
    have hne : ¬ (job.dst.dom = d ∧ job.dst.slot = s) := by
      rintro ⟨h1, h2⟩
      unfold MachineState.liveRef DomainState.liveCap at hdst
      rw [sweepRegions_caps, clearSlot_caps, if_pos ⟨h1, h2⟩] at hdst
      simp at hdst
    refine ⟨e, ?_, hcls⟩
    rw [liveCap_eq_some]
    refine ⟨?_, ?_, hg0⟩
    · rw [hcaps, if_neg hne]; exact hce
    · rw [hgen, if_neg hne]; exact hg
  · intro hms job hj
    obtain ⟨hmv, hsrc, hdst⟩ := sweepMover_mover_some _ job hj
    rw [sweepRegions_mover, clearSlot_mover] at hmv
    obtain ⟨e, he⟩ := hms job hmv
    rw [liveCap_eq_some] at he
    obtain ⟨hce, hg, hg0⟩ := he
    have hne : ¬ (job.src.dom = d ∧ job.src.slot = s) := by
      rintro ⟨h1, h2⟩
      unfold MachineState.liveRef DomainState.liveCap at hsrc
      rw [sweepRegions_caps, clearSlot_caps, if_pos ⟨h1, h2⟩] at hsrc
      simp at hsrc
    refine ⟨e, ?_⟩
    rw [liveCap_eq_some]
    refine ⟨?_, ?_, hg0⟩
    · rw [hcaps, if_neg hne]; exact hce
    · rw [hgen, if_neg hne]; exact hg

/-- The destroy-then-sweep composite (`cap_revoke`). -/
theorem evo_destroySweep (σ : MachineState) (M : DomainId → Slot → Bool) :
    Evo σ ((((σ.destroyMarked M).sweepRegions).sweepMover)) := by
  have hcaps : ∀ d' s', ((((σ.destroyMarked M).sweepRegions).sweepMover).doms d').caps s' =
      if M d' s' then none else (σ.doms d').caps s' := by
    intro d' s'; rw [sweepMover_doms, sweepRegions_caps, destroyMarked_caps]
  have hgen : ∀ d' s', ((((σ.destroyMarked M).sweepRegions).sweepMover).doms d').slotGen s' =
      if M d' s' && ((σ.doms d').caps s').isSome then bumpGen ((σ.doms d').slotGen s')
      else (σ.doms d').slotGen s' := by
    intro d' s'; rw [sweepMover_doms]
    rw [show ((σ.destroyMarked M).sweepRegions.doms d').slotGen s' =
      ((σ.destroyMarked M).doms d').slotGen s' from by rw [sweepRegions_slotGen]]
    exact destroyMarked_slotGen σ M d' s'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d' s'; rw [hgen d' s']
    split
    · exact bumpGen_ge _
    · exact Nat.le_refl _
  · intro r k hf
    unfold RefFate at hf ⊢
    rw [hcaps r.dom r.slot, hgen r.dom r.slot]
    rcases hf with h1 | h2 | h3
    · obtain ⟨hg, e, hce, hk⟩ := h1
      by_cases hM : M r.dom r.slot
      · rw [if_pos hM]
        rw [show (M r.dom r.slot && ((σ.doms r.dom).caps r.slot).isSome) = true from by
          rw [hM, hce]; rfl]
        rw [if_pos rfl]
        by_cases hret : (σ.doms r.dom).slotGen r.slot = genRetired
        · exact Or.inr (Or.inr ⟨rfl, by rw [hret]; exact bumpGen_retired,
            by rw [← hg]; exact hret⟩)
        · exact Or.inr (Or.inl (by rw [← hg]; exact bumpGen_gt _ hret))
      · rw [if_neg hM]
        rw [show (M r.dom r.slot && ((σ.doms r.dom).caps r.slot).isSome) = false from by
          simp only [Bool.not_eq_true] at hM; rw [hM]; simp, if_neg Bool.false_ne_true]
        exact Or.inl ⟨hg, e, hce, hk⟩
    · refine Or.inr (Or.inl ?_)
      split
      · exact lt_of_lt_of_le h2 (bumpGen_ge _)
      · exact h2
    · refine Or.inr (Or.inr ⟨?_, ?_, h3.2.2⟩)
      · split
        · rfl
        · exact h3.1
      · rw [show (M r.dom r.slot && ((σ.doms r.dom).caps r.slot).isSome) = false from by
          rw [h3.1]; simp, if_neg Bool.false_ne_true]
        exact h3.2.1
  · intro d' s' hts
    unfold Tombstoned at hts ⊢
    rw [hcaps d' s', hgen d' s']
    refine ⟨?_, ?_⟩
    · split
      · rfl
      · exact hts.1
    · rw [show (M d' s' && ((σ.doms d').caps s').isSome) = false from by rw [hts.1]; simp,
        if_neg Bool.false_ne_true]
      exact hts.2
  · intro hml job hj
    obtain ⟨hmv, hsrc, hdst⟩ := sweepMover_mover_some _ job hj
    rw [sweepRegions_mover, destroyMarked_mover] at hmv
    obtain ⟨e, he, hcls⟩ := hml job hmv
    rw [liveCap_eq_some] at he
    obtain ⟨hce, hg, hg0⟩ := he
    have hnm : ¬ (M job.dst.dom job.dst.slot = true) := by
      intro hMt
      unfold MachineState.liveRef DomainState.liveCap at hdst
      rw [sweepRegions_caps, destroyMarked_caps, if_pos hMt] at hdst
      simp at hdst
    refine ⟨e, ?_, hcls⟩
    rw [liveCap_eq_some]
    refine ⟨?_, ?_, hg0⟩
    · rw [hcaps, if_neg hnm]; exact hce
    · rw [hgen]
      rw [show (M job.dst.dom job.dst.slot &&
          ((σ.doms job.dst.dom).caps job.dst.slot).isSome) = false from by
        simp only [Bool.not_eq_true] at hnm; rw [hnm]; simp, if_neg Bool.false_ne_true]
      exact hg
  · intro hms job hj
    obtain ⟨hmv, hsrc, hdst⟩ := sweepMover_mover_some _ job hj
    rw [sweepRegions_mover, destroyMarked_mover] at hmv
    obtain ⟨e, he⟩ := hms job hmv
    rw [liveCap_eq_some] at he
    obtain ⟨hce, hg, hg0⟩ := he
    have hnm : ¬ (M job.src.dom job.src.slot = true) := by
      intro hMt
      unfold MachineState.liveRef DomainState.liveCap at hsrc
      rw [sweepRegions_caps, destroyMarked_caps, if_pos hMt] at hsrc
      simp at hsrc
    refine ⟨e, ?_⟩
    rw [liveCap_eq_some]
    refine ⟨?_, ?_, hg0⟩
    · rw [hcaps, if_neg hnm]; exact hce
    · rw [hgen]
      rw [show (M job.src.dom job.src.slot &&
          ((σ.doms job.src.dom).caps job.src.slot).isSome) = false from by
        simp only [Bool.not_eq_true] at hnm; rw [hnm]; simp, if_neg Bool.false_ne_true]
      exact hg

/-- `transferCap` evolves the state: install at a `freeSlot`, reparent
(lineage only), clear-and-sweep the source. -/
theorem evo_transferCap (σ : MachineState) (from_ : DomainId) (s : Slot) (to_ : DomainId)
    (τ : MachineState) (ref : CapRef) (h : σ.transferCap from_ s to_ = some (τ, ref)) :
    Evo σ τ := by
  unfold MachineState.transferCap at h
  cases he : (σ.doms from_).caps s with
  | none => rw [he] at h; simp at h
  | some e =>
      rw [he] at h; simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hfs : σ.freeSlot to_ with
      | none => rw [hfs] at h; simp at h
      | some s2 =>
          rw [hfs] at h; simp only [Option.bind_some] at h
          obtain ⟨hfree, hnr⟩ := freeSlot_spec σ to_ s2 hfs
          have key : ∀ (σ₁ : MachineState), Evo σ σ₁ →
              some (((((σ₁.reparent ⟨from_, s, (σ.doms from_).slotGen s⟩
                ⟨to_, s2, (σ.doms to_).slotGen s2⟩).clearSlot from_ s).sweepRegions).sweepMover),
                (⟨to_, s2, (σ.doms to_).slotGen s2⟩ : CapRef))
                = some (τ, ref) →
              Evo σ τ := by
            intro σ₁ hpre heq
            injection heq with heq; injection heq with hτ _; subst hτ
            exact hpre.trans ((evo_reparent σ₁ _ _).trans (evo_clearSweep _ from_ s))
          cases hl : e.lineage with
          | none =>
              rw [hl] at h; simp only [Option.pure_def, Option.bind_some] at h
              exact key _ (evo_capsUpdate σ to_ s2 _ _ rfl rfl hfree hnr) h
          | some l =>
              rw [hl] at h; simp only [Option.bind_eq_bind, Option.bind_some] at h
              cases hc : (σ.doms from_).lineage l with
              | none => rw [hc] at h; simp at h
              | some cell =>
                  rw [hc] at h; simp only [Option.bind_some] at h
                  cases hfc : σ.freeCell to_ with
                  | none => rw [hfc] at h; simp at h
                  | some l' =>
                      rw [hfc] at h; simp only [Option.pure_def, Option.bind_some] at h
                      exact key _ (evo_capsUpdate σ to_ s2 _ _ rfl rfl hfree hnr) h

/-- `transferByHandle` evolves the state. -/
theorem EvoPres.transferByHandle (d to_ : DomainId) (hw : Loom.Word32) :
    EvoPres (Machines.Lnp64u.Isa.transferByHandle d to_ hw) := by
  unfold Machines.Lnp64u.Isa.transferByHandle
  by_cases hz : hw = 0
  · rw [if_pos hz]
    exact EvoPres.of_quiet (QuietPres.pure 0)
  · rw [if_neg hz]
    intro σ
    constructor
    · intro a σ' he
      simp only [specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive d hw σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, ee⟩ := r
          simp only [SpecM.get, specM_bind] at he
          cases htc : σ.transferCap d sl to_ with
          | none => rw [htc] at he; simp [SpecM.raise] at he
          | some pr =>
              obtain ⟨σ2, ref⟩ := pr
              rw [htc] at he; simp only [SpecM.set, specM_bind, specM_pure] at he
              injection he with _ h2; subst h2
              exact evo_transferCap σ d sl to_ σ2 ref htc
    · intro er σ' he
      simp only [specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive d hw σ with
      | err e0 σ0 =>
          have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state d _ σ hcl; rw [hcl] at he
          injection he with _ h2; subst h2; subst hs; exact Evo.refl _
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, ee⟩ := r
          simp only [SpecM.get, specM_bind] at he
          cases htc : σ.transferCap d sl to_ with
          | none =>
              rw [htc] at he; simp only [SpecM.raise] at he
              injection he with _ h2; subst h2; exact Evo.refl _
          | some pr =>
              obtain ⟨σ2, ref⟩ := pr
              rw [htc] at he; simp [SpecM.set, specM_bind, specM_pure] at he

/-! ## Relative evolution: `EvoFrom` (for `get`-dependent `set`s) -/

/-- `mm`, run at `σ0`, evolves from `σ0`. `EvoPres mm ↔ ∀ σ0, EvoFrom σ0 mm`. -/
def EvoFrom (σ0 : MachineState) {α : Type} (mm : SpecM α) : Prop :=
  (∀ a σ', mm σ0 = .ok a σ' → Evo σ0 σ') ∧
  (∀ e σ', mm σ0 = .err e σ' → Evo σ0 σ')

theorem EvoFrom.of_evoPres {α : Type} {mm : SpecM α} (h : EvoPres mm)
    (σ0 : MachineState) : EvoFrom σ0 mm := h σ0

theorem EvoPres.of_from {α : Type} {mm : SpecM α} (h : ∀ σ0, EvoFrom σ0 mm) :
    EvoPres mm := h

theorem EvoFrom.bind {σ0 : MachineState} {α β : Type} {m : SpecM α} {f : α → SpecM β}
    (hm : EvoFrom σ0 m)
    (hf : ∀ a σ1, m σ0 = .ok a σ1 → EvoFrom σ1 (f a)) :
    EvoFrom σ0 (m >>= f) := by
  constructor
  · intro b σ' he
    rw [specM_bind] at he
    cases hm2 : m σ0 with
    | ok a σ1 => rw [hm2] at he
                 exact (hm.1 a σ1 hm2).trans ((hf a σ1 hm2).1 b σ' he)
    | err e σ1 => rw [hm2] at he; simp at he
    | fault g => rw [hm2] at he; simp at he
  · intro e σ' he
    rw [specM_bind] at he
    cases hm2 : m σ0 with
    | ok a σ1 => rw [hm2] at he
                 exact (hm.1 a σ1 hm2).trans ((hf a σ1 hm2).2 e σ' he)
    | err e1 σ1 => rw [hm2] at he; injection he with h1 h2; subst h2
                   exact hm.2 e1 σ1 hm2
    | fault g => rw [hm2] at he; simp at he

theorem EvoFrom.get_bind {σ0 : MachineState} {β : Type} {f : MachineState → SpecM β}
    (h : EvoFrom σ0 (f σ0)) : EvoFrom σ0 (SpecM.get >>= f) := by
  constructor
  · intro b σ' he
    rw [specM_bind] at he
    exact h.1 b σ' he
  · intro e σ' he
    rw [specM_bind] at he
    exact h.2 e σ' he

theorem EvoFrom.set {σ0 X : MachineState} (h : Evo σ0 X) :
    EvoFrom σ0 (SpecM.set X) := by
  constructor
  · intro a σ' he
    unfold SpecM.set at he; injection he with _ h2; subst h2; exact h
  · intro e σ' he; unfold SpecM.set at he; simp at he

theorem EvoFrom.fatal {σ0 : MachineState} {α : Type} (f : Fault) :
    EvoFrom σ0 (SpecM.fatal f : SpecM α) := by
  constructor
  · intro a σ' he; unfold SpecM.fatal at he; simp at he
  · intro e σ' he; unfold SpecM.fatal at he; simp at he

theorem EvoFrom.quiet {σ0 : MachineState} {α : Type} {mm : SpecM α}
    (h : QuietPres mm) : EvoFrom σ0 mm := (EvoPres.of_quiet h) σ0

/-! ## The eleven system opcodes evolve the state -/

/-- `cap_dup`'s exec evolves the state. -/
theorem capdup_evo (c : Ctx) :
    EvoPres ((do
      let hw ← SpecM.reg c.d c.op.rs1
      let dw ← SpecM.reg c.d c.op.rs2
      let (s, g, e) ← capLive c.d hw
      let kind ←
        match e.kind with
        | .mem base len perms => narrow base len perms dw
        | .gate gid => pure (.gate gid)
      let h ← allocDerived c.d kind ⟨c.d, s, g⟩
      SpecM.setReg c.d c.op.rd h) : SpecM Unit) := by
  refine EvoPres.bind (EvoPres.of_quiet (QuietPres.reg _ _)) fun hw => ?_
  refine EvoPres.bind (EvoPres.of_quiet (QuietPres.reg _ _)) fun dw => ?_
  refine EvoPres.bind (EvoPres.of_quiet (QuietPres.capLive _ _)) fun r => ?_
  obtain ⟨s, g, e⟩ := r
  simp only []
  cases e.kind with
  | mem base len perms =>
      exact EvoPres.bind (EvoPres.of_quiet (QuietPres.narrow _ _ _ _)) fun kind =>
        EvoPres.bind (EvoPres.allocDerived _ _ _)
          fun h => EvoPres.of_quiet (QuietPres.setReg _ _ _)
  | gate gid =>
      exact EvoPres.bind (EvoPres.of_quiet (QuietPres.pure _)) fun kind =>
        EvoPres.bind (EvoPres.allocDerived _ _ _)
          fun h => EvoPres.of_quiet (QuietPres.setReg _ _ _)

/-- `mem_grant`'s exec evolves the state. -/
theorem memgrant_evo (c : Ctx) :
    EvoPres ((do
      let hw ← SpecM.reg c.d c.op.rs1
      let dw ← SpecM.reg c.d c.op.rs2
      let (s, g, e) ← capLive c.d hw
      match e.kind with
      | .gate _ => SpecM.raise .badCap
      | .mem base len perms => do
          let kind ← narrow base len perms dw
          let h ← allocDerived (descDom dw) kind ⟨c.d, s, g⟩
          SpecM.setReg c.d c.op.rd h) : SpecM Unit) := by
  refine EvoPres.bind (EvoPres.of_quiet (QuietPres.reg _ _)) fun hw => ?_
  refine EvoPres.bind (EvoPres.of_quiet (QuietPres.reg _ _)) fun dw => ?_
  refine EvoPres.bind (EvoPres.of_quiet (QuietPres.capLive _ _)) fun r => ?_
  obtain ⟨s, g, e⟩ := r
  simp only []
  cases e.kind with
  | gate gid => exact EvoPres.of_quiet (QuietPres.raise _)
  | mem base len perms =>
      exact EvoPres.bind (EvoPres.of_quiet (QuietPres.narrow _ _ _ _)) fun kind =>
        EvoPres.bind (EvoPres.allocDerived _ _ _)
          fun h => EvoPres.of_quiet (QuietPres.setReg _ _ _)

/-- `cap_drop`'s exec evolves the state. -/
theorem capdrop_evo (c : Ctx) :
    EvoPres ((do
      let hw ← SpecM.reg c.d c.op.rs1
      let (s, g, _) ← capLive c.d hw
      let ref : CapRef := ⟨c.d, s, g⟩
      let σ ← SpecM.get
      let σ' :=
        match σ.parentOf c.d s with
        | some p => σ.reparent ref p
        | none => σ.orphanChildren ref
      SpecM.set (((σ'.clearSlot c.d s).sweepRegions).sweepMover)
      SpecM.setReg c.d c.op.rd 0) : SpecM Unit) := by
  refine EvoPres.bind (EvoPres.of_quiet (QuietPres.reg _ _)) fun hw => ?_
  refine EvoPres.bind (EvoPres.of_quiet (QuietPres.capLive _ _)) fun r => ?_
  obtain ⟨s, g, e⟩ := r
  simp only []
  refine EvoPres.of_from fun σ0 => EvoFrom.get_bind ?_
  refine EvoFrom.bind (EvoFrom.set ?_) fun _ σ1 hset => EvoFrom.quiet (QuietPres.setReg _ _ _)
  cases hp : σ0.parentOf c.d s with
  | some p => exact (evo_reparent σ0 _ _).trans (evo_clearSweep _ c.d s)
  | none => exact (evo_orphanChildren σ0 _).trans (evo_clearSweep _ c.d s)

/-- `cap_revoke`'s exec evolves the state. -/
theorem caprevoke_evo (c : Ctx) :
    EvoPres ((do
      let hw ← SpecM.reg c.d c.op.rs1
      let (s, g, e) ← capLive c.d hw
      SpecM.require (e.kind.cls = .mem) .badCap
      let σ ← SpecM.get
      let m := σ.marks ⟨c.d, s, g⟩
      SpecM.set (((σ.destroyMarked m).sweepRegions).sweepMover)
      SpecM.setReg c.d c.op.rd 0) : SpecM Unit) := by
  refine EvoPres.bind (EvoPres.of_quiet (QuietPres.reg _ _)) fun hw => ?_
  refine EvoPres.bind (EvoPres.of_quiet (QuietPres.capLive _ _)) fun r => ?_
  obtain ⟨s, g, e⟩ := r
  simp only []
  refine EvoPres.bind (EvoPres.of_quiet (QuietPres.require _ _)) fun _ => ?_
  refine EvoPres.of_from fun σ0 => EvoFrom.get_bind ?_
  exact EvoFrom.bind (EvoFrom.set (evo_destroySweep σ0 _))
    fun _ σ1 hset => EvoFrom.quiet (QuietPres.setReg _ _ _)

/-- `map`'s exec is quiet. -/
theorem map_quiet (c : Ctx) :
    QuietPres ((do
      let hw ← SpecM.reg c.d c.op.rs1
      let (s, g, e) ← capLive c.d hw
      match e.kind with
      | .gate _ => SpecM.raise .badCap
      | .mem base len perms => do
          let ri : RegionId :=
            ⟨(c.op.imm.extractLsb' 0 2).toNat, (c.op.imm.extractLsb' 0 2).isLt⟩
          let rgn : Region := { base := base, len := len, perms := perms
                                backing := ⟨c.d, s, g⟩ }
          SpecM.updDom c.d fun ds =>
            { ds with regions := Loom.Fun.update ds.regions ri (some rgn) }
          SpecM.setReg c.d c.op.rd 0) : SpecM Unit) := by
  refine QuietPres.bind (QuietPres.reg _ _) fun hw => ?_
  refine QuietPres.bind (QuietPres.capLive _ _) fun r => ?_
  obtain ⟨s, g, e⟩ := r
  simp only []
  cases e.kind with
  | gate gid => exact QuietPres.raise _
  | mem base len perms =>
      exact QuietPres.bind (QuietPres.updDom _ _ (fun ds => ⟨rfl, rfl, rfl⟩))
        fun _ => QuietPres.setReg _ _ _

/-- `gate_call`'s exec evolves the state. -/
theorem gatecall_evo (c : Ctx) :
    EvoPres (Machines.Lnp64u.Isa.Wip.gateCallExec c) := by
  unfold Machines.Lnp64u.Isa.Wip.gateCallExec
  refine EvoPres.bind (EvoPres.of_quiet (QuietPres.reg _ _)) fun hw => ?_
  refine EvoPres.bind (EvoPres.of_quiet (QuietPres.capLive _ _)) fun r => ?_
  obtain ⟨s0, g0, e⟩ := r
  simp only []
  cases e.kind with
  | mem base len perms => exact EvoPres.of_quiet (QuietPres.raise _)
  | gate gid =>
      refine EvoPres.of_from fun σ0 => EvoFrom.get_bind ?_
      refine EvoFrom.bind (EvoFrom.quiet (QuietPres.require _ _)) fun _ σ1 h1 => ?_
      refine EvoFrom.bind (EvoFrom.quiet (QuietPres.require _ _)) fun _ σ2 h2 => ?_
      refine EvoFrom.bind (EvoFrom.quiet (QuietPres.require _ _)) fun _ σ3 h3 => ?_
      refine EvoFrom.bind (EvoFrom.quiet (QuietPres.require _ _)) fun _ σ4 h4 => ?_
      refine EvoFrom.bind (EvoFrom.quiet (QuietPres.require _ _)) fun _ σ5 h5 => ?_
      refine EvoFrom.bind (EvoFrom.quiet (QuietPres.reg _ _)) fun argw σ6 h6 => ?_
      refine EvoFrom.bind (EvoFrom.of_evoPres (EvoPres.transferByHandle _ _ _) _)
        fun argHandle τ htbh => ?_
      refine EvoFrom.get_bind ?_
      refine EvoFrom.bind (EvoFrom.set (evo_of_projs _ _ (fun _ => rfl) (fun _ => rfl) rfl))
        fun _ τ2 hset => ?_
      refine EvoFrom.bind (EvoFrom.quiet (QuietPres.updDom _ _ (fun ds => ⟨rfl, rfl, rfl⟩)))
        fun _ τ3 hupd => ?_
      exact EvoFrom.quiet (QuietPres.updDom _ _ (fun ds => ⟨rfl, rfl, rfl⟩))

/-- `gate_return`'s exec evolves the state. -/
theorem gatereturn_evo (c : Ctx) :
    EvoPres ((do
      let σ0 ← SpecM.get
      match (σ0.doms c.d).serving with
      | none => SpecM.fatal .protocol
      | some gid =>
          match (σ0.gates gid).act with
          | none => SpecM.fatal .protocol
          | some act => do
              let rw ← SpecM.reg c.d c.op.rs1
              let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
              let σ1 ← SpecM.get
              SpecM.set ({ σ1 with
                gates := Loom.Fun.update σ1.gates gid
                  { (σ1.gates gid) with act := none } })
              SpecM.updDom c.d (fun ds =>
                { ds with regs := act.savedRegs, pc := act.savedPc,
                          serving := act.savedServing })
              SpecM.updDom act.caller (fun ds => { ds with run := .running })
              SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) := by
  refine EvoPres.of_from fun σ0 => EvoFrom.get_bind ?_
  cases (σ0.doms c.d).serving with
  | none => exact EvoFrom.fatal _
  | some gid =>
      simp only []
      cases (σ0.gates gid).act with
      | none => exact EvoFrom.fatal _
      | some act =>
          simp only []
          refine EvoFrom.bind (EvoFrom.quiet (QuietPres.reg _ _)) fun rw σ1 h1 => ?_
          refine EvoFrom.bind (EvoFrom.of_evoPres (EvoPres.transferByHandle _ _ _) _)
            fun reply τ htbh => ?_
          refine EvoFrom.get_bind ?_
          refine EvoFrom.bind (EvoFrom.set (evo_of_projs _ _ (fun _ => rfl) (fun _ => rfl) rfl))
            fun _ τ2 hset => ?_
          refine EvoFrom.bind (EvoFrom.quiet (QuietPres.updDom _ _ (fun ds => ⟨rfl, rfl, rfl⟩)))
            fun _ τ3 h3 => ?_
          refine EvoFrom.bind (EvoFrom.quiet (QuietPres.updDom _ _ (fun ds => ⟨rfl, rfl, rfl⟩)))
            fun _ τ4 h4 => ?_
          exact EvoFrom.quiet (QuietPres.setReg _ _ _)

/-- `move`'s exec evolves the state (the fresh Mover job's destination is a
live memory capability, checked at issue). -/
theorem move_evo (c : Ctx) : EvoPres (Machines.Lnp64u.Isa.Wip.moveExec c) := by
  unfold Machines.Lnp64u.Isa.Wip.moveExec
  refine EvoPres.of_from fun σ0 => EvoFrom.get_bind ?_
  refine EvoFrom.bind (EvoFrom.quiet (QuietPres.require _ _)) fun _ σ1 h1 => ?_
  obtain rfl : σ0 = σ1 := (require_ok _ _ _ h1).symm
  refine EvoFrom.bind (EvoFrom.quiet (QuietPres.reg _ _)) fun aw σ2 h2 => ?_
  obtain rfl : σ0 = σ2 := by unfold SpecM.reg at h2; injection h2
  refine EvoFrom.bind (EvoFrom.quiet (QuietPres.load _ _)) fun srcH σ3 h3 => ?_
  obtain rfl : σ0 = σ3 := (load_ok _ _ _ h3).symm
  refine EvoFrom.bind (EvoFrom.quiet (QuietPres.load _ _)) fun dstH σ4 h4 => ?_
  obtain rfl : σ0 = σ4 := (load_ok _ _ _ h4).symm
  refine EvoFrom.bind (EvoFrom.quiet (QuietPres.load _ _)) fun lenW σ5 h5 => ?_
  obtain rfl : σ0 = σ5 := (load_ok _ _ _ h5).symm
  refine EvoFrom.bind (EvoFrom.quiet (QuietPres.load _ _)) fun stW σ6 h6 => ?_
  obtain rfl : σ0 = σ6 := (load_ok _ _ _ h6).symm
  refine EvoFrom.bind (EvoFrom.quiet (QuietPres.capLive _ _)) fun rs σ7 h7 => ?_
  obtain ⟨hσ7, hslive⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok _ _ _ h7
  obtain rfl : σ0 = σ7 := hσ7.symm
  obtain ⟨ss, gs_, es⟩ := rs
  simp only [] at hslive
  simp only []
  refine EvoFrom.bind (EvoFrom.quiet (QuietPres.capLive _ _)) fun rd σ8 h8 => ?_
  obtain ⟨hσ8, hdlive⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok _ _ _ h8
  obtain rfl := hσ8.symm
  obtain ⟨sd, gd, ed⟩ := rd
  simp only [] at hdlive ⊢
  cases hks : es.kind with
  | gate gg =>
      cases hkd : ed.kind with
      | gate _ => exact EvoFrom.quiet (QuietPres.raise _)
      | mem _ _ _ => exact EvoFrom.quiet (QuietPres.raise _)
  | mem sb sl sp =>
      cases hkd : ed.kind with
      | gate _ => exact EvoFrom.quiet (QuietPres.raise _)
      | mem db dl dp =>
          refine EvoFrom.bind (EvoFrom.quiet (QuietPres.require _ _)) fun _ σa ha => ?_
          obtain rfl := (require_ok _ _ _ ha).symm
          refine EvoFrom.bind (EvoFrom.quiet (QuietPres.require _ _)) fun _ σb hb => ?_
          obtain rfl := (require_ok _ _ _ hb).symm
          refine EvoFrom.bind (EvoFrom.quiet (QuietPres.require _ _)) fun _ σc hc => ?_
          obtain rfl := (require_ok _ _ _ hc).symm
          refine EvoFrom.get_bind ?_
          refine EvoFrom.bind (EvoFrom.quiet (QuietPres.demand _ _)) fun _ σd hd => ?_
          obtain rfl := (demand_ok _ _ _ hd).symm
          refine EvoFrom.bind (EvoFrom.set ?_) fun _ σe hset =>
            EvoFrom.quiet (QuietPres.setReg _ _ _)
          -- the fresh job: doms untouched, destination checked live-memory
          refine ⟨fun d s => Nat.le_refl _, fun r k hf => hf, fun d s hts => hts,
            ?_, ?_⟩
          · intro _ job hj
            simp only at hj
            injection hj with hj; subst hj
            exact ⟨ed, hdlive, by rw [hkd]; rfl⟩
          · intro _ job hj
            simp only at hj
            injection hj with hj; subst hj
            exact ⟨es, hslive⟩

/-! ## Dispatch: every instruction evolves the state -/

theorem QuietPres.modify (f : MachineState → MachineState)
    (hf : ∀ σ, Quiet σ (f σ)) : QuietPres (SpecM.modify f) := by
  intro σ
  constructor
  · intro a σ' he
    unfold SpecM.modify at he; injection he with _ h2; subst h2; exact hf σ
  · intro e σ' he; simp [SpecM.modify] at he

theorem QuietPres.updDomPc (d : DomainId) (k : DomainState → Addr) :
    QuietPres (SpecM.updDom d (fun ds => { ds with pc := k ds })) :=
  QuietPres.updDom d _ (fun ds => ⟨rfl, rfl, rfl⟩)

/-- The fourteen base opcodes are quiet (registers, memory, pc only). -/
theorem base_quiet : ∀ instr ∈ Machines.Lnp64u.Isa.base, ∀ c : Ctx,
    QuietPres (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  · exact QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.setReg _ _ _))
  · exact QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.setReg _ _ _))
  · exact QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.setReg _ _ _))
  · exact QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.setReg _ _ _))
  · exact QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.setReg _ _ _))
  · exact QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.setReg _ _ _))
  · exact QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.setReg _ _ _))
  · exact QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.setReg _ _ _)
  · exact QuietPres.setReg _ _ _
  · exact QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.bind (QuietPres.load _ _) (fun _ => QuietPres.setReg _ _ _))
  · exact QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.store _ _ _))
  · exact QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.iteBool _ (QuietPres.updDomPc _ _) (QuietPres.pure ())))
  · exact QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.bind (QuietPres.reg _ _) (fun _ => QuietPres.iteBool _ (QuietPres.updDomPc _ _) (QuietPres.pure ())))
  · exact QuietPres.bind (QuietPres.reg _ _)
      (fun _ => QuietPres.bind (QuietPres.setReg _ _ _) (fun _ => QuietPres.updDomPc _ _))

/-- The eleven system opcodes evolve the state. -/
theorem system_evo : ∀ instr ∈ Machines.Lnp64u.Isa.system, ∀ c : Ctx,
    EvoPres (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  case _ => exact capdup_evo c
  case _ => exact capdrop_evo c
  case _ => exact caprevoke_evo c
  case _ => exact memgrant_evo c
  case _ => exact EvoPres.of_quiet (map_quiet c)
  case _ => exact EvoPres.of_quiet (QuietPres.bind
      (QuietPres.updDom _ _ (fun ds => ⟨rfl, rfl, rfl⟩)) (fun _ => QuietPres.setReg _ _ _))
  case _ => exact gatecall_evo c
  case _ => exact gatereturn_evo c
  case _ => exact move_evo c
  case _ => exact EvoPres.of_quiet (QuietPres.bind
      (QuietPres.updDom _ _ (fun ds => ⟨rfl, rfl, rfl⟩)) (fun _ => QuietPres.setReg _ _ _))
  case _ => exact EvoPres.of_quiet (QuietPres.modify _ (fun σ => quiet_haltDom σ c.d 0))

/-- Every ISA instruction's exec evolves the state. -/
theorem exec_evo : ∀ instr ∈ isa, ∀ c : Ctx, EvoPres (instr.sem.exec c) := by
  intro instr hmem c
  have hmem' : instr ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
    have hiseq : Machines.Lnp64u.isa =
      (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray := rfl
    rw [hiseq, Array.mem_toArray] at hmem; exact hmem
  rcases List.mem_append.mp hmem' with hb | hs
  · exact EvoPres.of_quiet (base_quiet instr hb c)
  · exact system_evo instr hs c

/-! ## The phase and step lifts -/

theorem evo_haltWith (σ : MachineState) (d : DomainId) (f : Fault) :
    Evo σ (haltWith σ d f) := (quiet_haltDom σ d _).evo

theorem retire_evo (σ : MachineState) (d : DomainId) (w : Loom.Word32) :
    Evo σ (retire σ d w) := by
  unfold retire
  split
  · exact evo_haltWith σ d _
  · rename_i instr hdec
    have hpc : Evo σ (σ.setDom d fun ds => { ds with pc := ds.pc + 1 }) :=
      (quiet_setDom σ d _ ⟨rfl, rfl, rfl⟩).evo
    have hexec := exec_evo instr (Loom.Isa.decode_mem isa hdec)
      { d := d, pc := (σ.doms d).pc, op := operandsOf w }
      (σ.setDom d fun ds => { ds with pc := ds.pc + 1 })
    cases hexr : instr.sem.exec { d := d, pc := (σ.doms d).pc, op := operandsOf w }
        (σ.setDom d fun ds => { ds with pc := ds.pc + 1 }) with
    | ok a σ' =>
        simp only [hexr]
        exact hpc.trans (hexec.1 a σ' hexr)
    | err e σ' =>
        simp only [hexr]
        exact (hpc.trans (hexec.2 e σ' hexr)).trans
          (quiet_setDom σ' d _ ⟨setReg_caps _ _ _, setReg_lineage _ _ _, setReg_slotGen _ _ _⟩).evo
    | fault f =>
        simp only [hexr]
        exact evo_haltWith σ d f

theorem corePhase_evo (m : Manifest) (σ : MachineState) : Evo σ (corePhase m σ) := by
  unfold corePhase
  cases hinf : σ.inflight with
  | some fl =>
      by_cases hcy : fl.cyclesLeft ≤ 1
      · simp only [hcy, if_true]
        exact (evo_of_projs σ { σ with inflight := none }
          (fun _ => rfl) (fun _ => rfl) rfl).trans (retire_evo _ fl.dom fl.word)
      · simp only [hcy, if_false]
        exact evo_of_projs σ _ (fun _ => rfl) (fun _ => rfl) rfl
  | none =>
      simp only []
      split
      · exact Evo.refl σ
      · rename_i d hsched
        split
        · exact evo_haltWith σ _ _
        · rename_i w hfetch
          split
          · exact evo_haltWith σ _ _
          · rename_i instr hdec
            by_cases hbud : instr.cost.cost ≤ (σ.doms (σ.payer d)).budget
            · simp only [hbud, if_true]
              obtain ⟨pc, pl, pg, pr, pru, ps, pgates, pmov⟩ :=
                setBudget_proj σ (σ.payer d) (fun ds => ds.budget - instr.cost.cost)
              have hbudEvo : Evo σ (σ.setDom (σ.payer d)
                  (fun ds => { ds with budget := ds.budget - instr.cost.cost })) :=
                evo_of_projs _ _ pc pg pmov
              cases hserv : (σ.doms d).serving with
              | none =>
                  simp only [hserv]
                  exact hbudEvo.trans (evo_of_projs _ _ (fun _ => rfl) (fun _ => rfl) rfl)
              | some g =>
                  simp only [hserv]
                  cases hact : (σ.gates g).act with
                  | none => exact evo_haltWith σ d _
                  | some a =>
                      simp only [hact]
                      by_cases hdon : instr.cost.cost ≤ a.donated
                      · simp only [hdon, if_true]
                        exact hbudEvo.trans ((evo_of_projs _ _ (fun _ => rfl) (fun _ => rfl) rfl).trans
                          (evo_of_projs _ _ (fun _ => rfl) (fun _ => rfl) rfl))
                      · simp only [hdon, if_false]
                        exact evo_haltWith σ d _
            · simp only [hbud, if_false]
              cases hserv : (σ.doms d).serving with
              | some g =>
                  simp only [hserv]
                  exact evo_haltWith σ d _
              | none =>
                  simp only [hserv]
                  exact (quiet_setDom σ (σ.payer d)
                    (fun ds => { ds with budget := 0 }) ⟨rfl, rfl, rfl⟩).evo

theorem evo_refillPhase (m : Manifest) (σ : MachineState) : Evo σ (refillPhase m σ) :=
  evo_of_projs σ _ (fun d => refillPhase_caps m σ d) (fun d => refillPhase_slotGen m σ d)
    (refillPhase_mover m σ)

theorem evo_moverPhase (σ : MachineState) : Evo σ (moverPhase σ) := by
  refine ⟨fun d s => by rw [moverPhase_doms], ?_, ?_, ?_, ?_⟩
  · intro r k hf; unfold RefFate at hf ⊢; rw [moverPhase_doms]; exact hf
  · intro d s hts; unfold Tombstoned at hts ⊢; rw [moverPhase_doms]; exact hts
  · intro hml job hj
    rcases moverPhase_mover σ with hnone | ⟨job0, job', hm0, hm', ho, hs, hdst⟩
    · rw [hnone] at hj; exact absurd hj (by simp)
    · rw [hm'] at hj; injection hj with hj; subst hj
      obtain ⟨e, he, hcls⟩ := hml job0 hm0
      refine ⟨e, ?_, hcls⟩
      rw [hdst, moverPhase_doms]
      exact he
  · intro hms job hj
    rcases moverPhase_mover σ with hnone | ⟨job0, job', hm0, hm', ho, hs, hdst⟩
    · rw [hnone] at hj; exact absurd hj (by simp)
    · rw [hm'] at hj; injection hj with hj; subst hj
      obtain ⟨e, he⟩ := hms job0 hm0
      refine ⟨e, ?_⟩
      rw [hs, moverPhase_doms]
      exact he

/-- **One machine cycle evolves the state.** -/
theorem step_evo (m : Manifest) (σ : MachineState) : Evo σ (step m σ) := by
  unfold step
  exact ((evo_refillPhase m σ).trans (corePhase_evo m _)).trans
    ((evo_moverPhase _).trans (evo_of_projs _ _ (fun _ => rfl) (fun _ => rfl) rfl))

theorem stepN_evo (m : Manifest) (n : Nat) (σ : MachineState) :
    Evo σ (stepN m n σ) := by
  induction n generalizing σ with
  | zero => exact Evo.refl σ
  | succ k ih => exact (step_evo m σ).trans (ih (step m σ))

/-! ## The Mover-destination invariant -/

/-- Every reachable state\'s Mover destination (when a job is active) is a
live memory capability. -/
theorem moverLiveMem_invariant (m : Manifest) :
    (machine m).Invariant MoverLiveMem :=
  Loom.TSys.Inductive.invariant
    { init := fun σ hi => by
        subst hi
        intro job hj
        exact absurd hj (by simp [Manifest.initState])
      step := fun σ σ2 hP hstep => by
        have hst : step m σ = σ2 := hstep
        exact hst ▸ (step_evo m σ).2.2.2.1 hP }

/-- Every reachable state's Mover source (when a job is active) is still
live. -/
theorem moverLiveSrc_invariant (m : Manifest) :
    (machine m).Invariant MoverLiveSrc :=
  Loom.TSys.Inductive.invariant
    { init := fun σ hi => by
        subst hi
        intro job hj
        exact absurd hj (by simp [Manifest.initState])
      step := fun σ σ2 hP hstep => by
        have hst : step m σ = σ2 := hstep
        exact hst ▸ (step_evo m σ).2.2.2.2 hP }

/-- Reachability is closed under `stepN`. -/
theorem reachable_stepN (m : Manifest) (σ : MachineState)
    (h : (machine m).Reachable σ) (n : Nat) :
    (machine m).Reachable (stepN m n σ) := by
  induction n generalizing σ with
  | zero => exact h
  | succ k ih => exact ih (step m σ) (.step h rfl)

/-! ## Class lineage: derived capabilities share their live parent's class -/

/-- A derived capability has the same class as its (live) parent. Together
with `marks`' parent-chain structure, every marked descendant of a root has
the root's class — the fact that makes gate-class roots harmless to revoke
lazily (their descendants can never back regions or Mover jobs). -/
def ClassLineage (σ : MachineState) : Prop :=
  ∀ d s e p ep, (σ.doms d).caps s = some e → σ.parentOf d s = some p →
    (σ.doms p.dom).liveCap p.slot p.gen = some ep → e.kind.cls = ep.kind.cls

theorem parentOf_some_iff (σ : MachineState) (d : DomainId) (s : Slot) (p : CapRef) :
    σ.parentOf d s = some p ↔
      ∃ e l cell, (σ.doms d).caps s = some e ∧ e.lineage = some l ∧
        (σ.doms d).lineage l = some cell ∧ cell.parent = p := by
  constructor
  · intro h
    unfold MachineState.parentOf at h
    simp only [Option.bind_eq_bind] at h
    cases hc : (σ.doms d).caps s with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some e =>
        rw [hc, Option.bind_some] at h
        cases hl : e.lineage with
        | none => rw [hl] at h; exact absurd h (by simp)
        | some l =>
            rw [hl, Option.bind_some] at h
            cases hcell : (σ.doms d).lineage l with
            | none => rw [hcell] at h; exact absurd h (by simp)
            | some cell =>
                rw [hcell, Option.bind_some] at h
                refine ⟨e, l, cell, rfl, hl, hcell, ?_⟩
                exact Option.some.inj h
  · rintro ⟨e, l, cell, hc, hl, hcell, rfl⟩
    unfold MachineState.parentOf
    simp only [Option.bind_eq_bind]
    rw [hc, Option.bind_some, hl, Option.bind_some, hcell, Option.bind_some]
    rfl

theorem parentOf_congr (σ σ' : MachineState) (ht : TablesEq σ σ') (d : DomainId) (s : Slot) :
    σ'.parentOf d s = σ.parentOf d s := by
  unfold MachineState.parentOf
  rw [(ht d).1, (ht d).2.1]

theorem classLineage_of_tablesEq {σ σ' : MachineState} (ht : TablesEq σ σ')
    (h : ClassLineage σ) : ClassLineage σ' := by
  intro d s e p ep hce hpar hlive
  rw [(ht d).1] at hce
  rw [parentOf_congr σ σ' ht] at hpar
  rw [liveCap_congr_of_eq _ _ (ht p.dom).1 (ht p.dom).2.2] at hlive
  exact h d s e p ep hce hpar hlive

/-- What `freeCell` promises about its result: the cell is unoccupied. -/
theorem freeCell_spec (σ : MachineState) (d : DomainId) (l : LineageId)
    (h : σ.freeCell d = some l) : (σ.doms d).lineage l = none := by
  unfold MachineState.freeCell at h
  have hp := List.find?_some h
  simpa using hp

theorem reparent_lineage (σ : MachineState) (old new : CapRef) (d : DomainId) (l : LineageId) :
    ((σ.reparent old new).doms d).lineage l =
      match (σ.doms d).lineage l with
      | some cell => some (if cell.parent = old then { parent := new } else cell)
      | none => none := rfl

@[simp] theorem reparent_caps (σ : MachineState) (old new : CapRef) (d : DomainId) :
    ((σ.reparent old new).doms d).caps = (σ.doms d).caps := rfl

/-- A surviving lineage cell of `destroyMarked` was already there. -/
theorem destroyMarked_lineage_some (σ : MachineState) (M : DomainId → Slot → Bool)
    (d : DomainId) (l : LineageId) (cell : LineageCell)
    (h : ((σ.destroyMarked M).doms d).lineage l = some cell) :
    (σ.doms d).lineage l = some cell := by
  replace h : (if ((List.finRange numSlots).any fun s =>
        M d s &&
        match (σ.doms d).caps s with
        | some e => e.lineage == some l
        | none => false)
      then none else (σ.doms d).lineage l) = some cell := h
  split at h
  · exact absurd h (by simp)
  · exact h

/-! ### Kernel class-lineage lemmas -/

/-- Installing a fresh derived capability with a live parent of the same
class preserves `ClassLineage`. -/
theorem cl_installDerived (σ : MachineState) (dd : DomainId) (s : Slot) (l : LineageId)
    (kind : CapKind) (parent : CapRef)
    (hwf : Wf σ) (hcl : ClassLineage σ)
    (hfs : σ.freeSlot dd = some s) (hfc : σ.freeCell dd = some l)
    (pe : CapEntry)
    (hplive : (σ.doms parent.dom).liveCap parent.slot parent.gen = some pe)
    (hkcls : kind.cls = pe.kind.cls) :
    ClassLineage (σ.installDerived dd s l kind parent).1 := by
  obtain ⟨hfree, hnr⟩ := freeSlot_spec σ dd s hfs
  have hcellfree := freeCell_spec σ dd l hfc
  obtain ⟨hpc, hpg, hpg0⟩ := (liveCap_eq_some _ _ _ _).mp hplive
  have hinst : (σ.installDerived dd s l kind parent).1 = σ.setDom dd (fun ds =>
      { ds with
        caps := Loom.Fun.update ds.caps s (some { kind := kind, lineage := some l })
        lineage := Loom.Fun.update ds.lineage l (some { parent := parent }) }) := rfl
  rw [hinst]
  set σ' := σ.setDom dd (fun ds =>
      { ds with
        caps := Loom.Fun.update ds.caps s (some { kind := kind, lineage := some l })
        lineage := Loom.Fun.update ds.lineage l (some { parent := parent }) }) with hσ'
  have hcaps : ∀ d₂ s₂, ((σ'.doms d₂)).caps s₂ =
      if d₂ = dd ∧ s₂ = s then some { kind := kind, lineage := some l }
      else (σ.doms d₂).caps s₂ := by
    intro d₂ s₂
    rw [hσ']
    unfold MachineState.setDom
    by_cases hd : d₂ = dd
    · subst hd
      simp only [Loom.Fun.update_same, true_and]
      by_cases hs : s₂ = s
      · subst hs; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hs, hs]
    · simp [Loom.Fun.update_ne _ _ _ _ hd, hd]
  have hlin : ∀ d₂ l₂, ((σ'.doms d₂)).lineage l₂ =
      if d₂ = dd ∧ l₂ = l then some { parent := parent }
      else (σ.doms d₂).lineage l₂ := by
    intro d₂ l₂
    rw [hσ']
    unfold MachineState.setDom
    by_cases hd : d₂ = dd
    · subst hd
      simp only [Loom.Fun.update_same, true_and]
      by_cases hs : l₂ = l
      · subst hs; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hs, hs]
    · simp [Loom.Fun.update_ne _ _ _ _ hd, hd]
  have hgen : ∀ d₂, ((σ'.doms d₂)).slotGen = (σ.doms d₂).slotGen := by
    intro d₂
    rw [hσ']
    unfold MachineState.setDom
    by_cases hd : d₂ = dd
    · subst hd; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ hd]
  intro d₂ s₂ e₂ p₂ ep₂ hce hpar hlive
  obtain ⟨e₂', l₂, cell₂, hce', hl₂, hcell₂, hp₂⟩ := (parentOf_some_iff σ' d₂ s₂ p₂).mp hpar
  rw [hce] at hce'; injection hce' with hee; subst hee
  obtain ⟨hcep, hgenp, hg0p⟩ := (liveCap_eq_some _ _ _ _).mp hlive
  rw [hcaps] at hcep
  rw [hgen] at hgenp
  -- the parent's slot cannot be the freshly installed one unless it is `parent`
  rw [hcaps] at hce
  rw [hlin] at hcell₂
  by_cases hA : d₂ = dd ∧ s₂ = s
  · -- the fresh entry: its parent is `parent`
    rw [if_pos hA] at hce
    injection hce with hce; subst hce
    simp only at hl₂
    injection hl₂ with hl₂; subst hl₂
    rw [if_pos ⟨hA.1, rfl⟩] at hcell₂
    injection hcell₂ with hcell₂; subst hcell₂
    simp only at hp₂; subst hp₂
    have hne : ¬ (parent.dom = dd ∧ parent.slot = s) := by
      rintro ⟨h1, h2⟩
      rw [h1, h2] at hpc; rw [hfree] at hpc; exact absurd hpc (by simp)
    rw [if_neg hne] at hcep
    rw [hpc] at hcep; injection hcep with hcep; subst hcep
    exact hkcls
  · rw [if_neg hA] at hce
    have hl2ne : ¬ (d₂ = dd ∧ l₂ = l) := by
      rintro ⟨h1, h2⟩
      subst h1; subst h2
      have := hwf.doms d₂ |>.cell_backed s₂ e₂ l₂ hce hl₂
      rw [hcellfree] at this; exact absurd this (by simp)
    rw [if_neg hl2ne] at hcell₂
    have hparσ : σ.parentOf d₂ s₂ = some p₂ :=
      (parentOf_some_iff σ d₂ s₂ p₂).mpr ⟨e₂, l₂, cell₂, hce, hl₂, hcell₂, hp₂⟩
    have hnep : ¬ (p₂.dom = dd ∧ p₂.slot = s) := by
      rintro ⟨h1, h2⟩
      have hlr := hwf.parent_live d₂ s₂ p₂ hparσ
      unfold MachineState.liveRef DomainState.liveCap at hlr
      rw [h1, h2, hfree] at hlr
      simp at hlr
    rw [if_neg hnep] at hcep
    have hliveσ : (σ.doms p₂.dom).liveCap p₂.slot p₂.gen = some ep₂ :=
      (liveCap_eq_some _ _ _ _).mpr ⟨hcep, hgenp, hg0p⟩
    exact hcl d₂ s₂ e₂ p₂ ep₂ hce hparσ hliveσ

/-- Destroying a marked set and sweeping preserves `ClassLineage` (dead
parents vacuate the obligation; survivors are untouched). -/
theorem cl_destroySweep (σ : MachineState) (M : DomainId → Slot → Bool)
    (hcl : ClassLineage σ) :
    ClassLineage ((((σ.destroyMarked M).sweepRegions).sweepMover)) := by
  set τ := (((σ.destroyMarked M).sweepRegions).sweepMover) with hτ
  have hcaps : ∀ d₂ s₂, ((τ.doms d₂)).caps s₂ =
      if M d₂ s₂ then none else (σ.doms d₂).caps s₂ := by
    intro d₂ s₂; rw [hτ, sweepMover_doms, sweepRegions_caps, destroyMarked_caps]
  have hgen : ∀ d₂ s₂, ((τ.doms d₂)).slotGen s₂ =
      if M d₂ s₂ && ((σ.doms d₂).caps s₂).isSome then bumpGen ((σ.doms d₂).slotGen s₂)
      else (σ.doms d₂).slotGen s₂ := by
    intro d₂ s₂; rw [hτ, sweepMover_doms]
    rw [show ((σ.destroyMarked M).sweepRegions.doms d₂).slotGen s₂ =
      ((σ.destroyMarked M).doms d₂).slotGen s₂ from by rw [sweepRegions_slotGen]]
    exact destroyMarked_slotGen σ M d₂ s₂
  have hlins : ∀ d₂ l₂ cell, ((τ.doms d₂)).lineage l₂ = some cell →
      (σ.doms d₂).lineage l₂ = some cell := by
    intro d₂ l₂ cell h
    rw [hτ, sweepMover_doms, sweepRegions_lineage] at h
    exact destroyMarked_lineage_some σ M d₂ l₂ cell h
  intro d₂ s₂ e₂ p₂ ep₂ hce hpar hlive
  obtain ⟨e₂', l₂, cell₂, hce', hl₂, hcell₂, hp₂⟩ := (parentOf_some_iff τ d₂ s₂ p₂).mp hpar
  rw [hce] at hce'; injection hce' with hee; subst hee
  rw [hcaps] at hce
  have hM2 : ¬ (M d₂ s₂ = true) := by
    intro hM; rw [if_pos hM] at hce; exact absurd hce (by simp)
  rw [if_neg hM2] at hce
  have hcellσ := hlins d₂ l₂ cell₂ hcell₂
  have hparσ : σ.parentOf d₂ s₂ = some p₂ :=
    (parentOf_some_iff σ d₂ s₂ p₂).mpr ⟨e₂, l₂, cell₂, hce, hl₂, hcellσ, hp₂⟩
  obtain ⟨hcep, hgenp, hg0p⟩ := (liveCap_eq_some _ _ _ _).mp hlive
  rw [hcaps] at hcep
  have hMp : ¬ (M p₂.dom p₂.slot = true) := by
    intro hM; rw [if_pos hM] at hcep; exact absurd hcep (by simp)
  rw [if_neg hMp] at hcep
  rw [hgen] at hgenp
  rw [show (M p₂.dom p₂.slot && ((σ.doms p₂.dom).caps p₂.slot).isSome) = false from by
    simp only [Bool.not_eq_true] at hMp; rw [hMp]; simp] at hgenp
  rw [if_neg Bool.false_ne_true] at hgenp
  have hliveσ : (σ.doms p₂.dom).liveCap p₂.slot p₂.gen = some ep₂ :=
    (liveCap_eq_some _ _ _ _).mpr ⟨hcep, hgenp, hg0p⟩
  exact hcl d₂ s₂ e₂ p₂ ep₂ hce hparσ hliveσ


theorem gen_ne_zero_of_pos {g : Gen} (h : 1 ≤ g.toNat) : g ≠ 0 := by
  intro h0; subst h0; simp at h

/-- `cap_drop`'s reparent-splice core preserves `ClassLineage`: children of
the dropped capability inherit its parent, whose class matches by two
applications of the invariant. -/
theorem cl_dropCore (σ : MachineState) (cd : DomainId) (sl : Slot) (gg : Gen)
    (e₀ : CapEntry) (p : CapRef)
    (hwf : Wf σ) (hac : Acyclic σ) (hcl : ClassLineage σ)
    (hlive : (σ.doms cd).liveCap sl gg = some e₀)
    (hpar : σ.parentOf cd sl = some p) :
    ClassLineage ((((σ.reparent ⟨cd, sl, gg⟩ p).clearSlot cd sl).sweepRegions).sweepMover) := by
  obtain ⟨hce₀, hg₀, hg0₀⟩ := (liveCap_eq_some _ _ _ _).mp hlive
  have hpne : p ≠ (⟨cd, sl, gg⟩ : CapRef) := hac.parentRef_ne σ ⟨cd, sl, gg⟩ p hpar
  set τ := (((σ.reparent ⟨cd, sl, gg⟩ p).clearSlot cd sl).sweepRegions).sweepMover with hτ
  have hcapsτ : ∀ d₂ s₂, ((τ.doms d₂)).caps s₂ =
      if d₂ = cd ∧ s₂ = sl then none else (σ.doms d₂).caps s₂ := by
    intro d₂ s₂
    rw [hτ, sweepMover_doms, sweepRegions_caps, clearSlot_caps, reparent_caps]
  have hgenτ : ∀ d₂ s₂, ((τ.doms d₂)).slotGen s₂ =
      if d₂ = cd ∧ s₂ = sl then bumpGen ((σ.doms cd).slotGen sl)
      else (σ.doms d₂).slotGen s₂ := by
    intro d₂ s₂
    rw [hτ, sweepMover_doms]
    rw [show (((σ.reparent ⟨cd, sl, gg⟩ p).clearSlot cd sl).sweepRegions.doms d₂).slotGen s₂ =
      (((σ.reparent ⟨cd, sl, gg⟩ p).clearSlot cd sl).doms d₂).slotGen s₂ from by
        rw [sweepRegions_slotGen]]
    rw [clearSlot_slotGen]
    rfl
  have hlinτ : ∀ d₂ l₂ cell₂, ((τ.doms d₂)).lineage l₂ = some cell₂ →
      ∃ cell, (σ.doms d₂).lineage l₂ = some cell ∧
        cell₂ = (if cell.parent = (⟨cd, sl, gg⟩ : CapRef) then { parent := p } else cell) := by
    intro d₂ l₂ cell₂ h
    rw [hτ, sweepMover_doms, sweepRegions_lineage, clearSlot_lineage] at h
    split at h
    · exact absurd h (by simp)
    · rw [reparent_lineage] at h
      cases hc : ((σ.doms d₂)).lineage l₂ with
      | none => rw [hc] at h; exact absurd h (by simp)
      | some cell =>
          rw [hc] at h
          replace h : some (if cell.parent = (⟨cd, sl, gg⟩ : CapRef)
              then ({ parent := p } : LineageCell) else cell) = some cell₂ := h
          exact ⟨cell, rfl, (Option.some.inj h).symm⟩
  intro d₂ s₂ e₂ p₂ ep₂ hce hparτ hliveτ
  obtain ⟨e₂', l₂, cell₂, hce', hl₂, hcellτ, hp₂⟩ := (parentOf_some_iff τ d₂ s₂ p₂).mp hparτ
  rw [hce] at hce'; injection hce' with hee; subst hee
  rw [hcapsτ] at hce
  have hA : ¬ (d₂ = cd ∧ s₂ = sl) := by
    intro hA; rw [if_pos hA] at hce; exact absurd hce (by simp)
  rw [if_neg hA] at hce
  obtain ⟨hcep, hgenp, hg0p⟩ := (liveCap_eq_some _ _ _ _).mp hliveτ
  rw [hcapsτ] at hcep
  have hB : ¬ (p₂.dom = cd ∧ p₂.slot = sl) := by
    intro hB; rw [if_pos hB] at hcep; exact absurd hcep (by simp)
  rw [if_neg hB] at hcep
  rw [hgenτ, if_neg hB] at hgenp
  have hlivep₂ : (σ.doms p₂.dom).liveCap p₂.slot p₂.gen = some ep₂ :=
    (liveCap_eq_some _ _ _ _).mpr ⟨hcep, hgenp, hg0p⟩
  obtain ⟨cell, hcellσ, hcell₂⟩ := hlinτ d₂ l₂ cell₂ hcellτ
  by_cases hcp : cell.parent = (⟨cd, sl, gg⟩ : CapRef)
  · -- child of the dropped capability, spliced to `p`
    rw [if_pos hcp] at hcell₂
    subst hcell₂
    simp only at hp₂; subst hp₂
    have hparσ : σ.parentOf d₂ s₂ = some ⟨cd, sl, gg⟩ :=
      (parentOf_some_iff σ d₂ s₂ _).mpr ⟨e₂, l₂, cell, hce, hl₂, hcellσ, hcp⟩
    have h1 : e₂.kind.cls = e₀.kind.cls := hcl d₂ s₂ e₂ ⟨cd, sl, gg⟩ e₀ hce hparσ hlive
    have h2 : e₀.kind.cls = ep₂.kind.cls := hcl cd sl e₀ p ep₂ hce₀ hpar hlivep₂
    exact h1.trans h2
  · rw [if_neg hcp] at hcell₂
    rw [hcell₂] at hp₂
    have hparσ : σ.parentOf d₂ s₂ = some p₂ :=
      (parentOf_some_iff σ d₂ s₂ _).mpr ⟨e₂, l₂, cell, hce, hl₂, hcellσ, hp₂⟩
    exact hcl d₂ s₂ e₂ p₂ ep₂ hce hparσ hlivep₂

/-- `cap_drop`'s orphan core preserves `ClassLineage`: children become
roots (vacuous), everyone else keeps parent and class. -/
theorem cl_dropOrphan (σ : MachineState) (cd : DomainId) (sl : Slot) (gg : Gen)
    (hwf : Wf σ) (hcl : ClassLineage σ) :
    ClassLineage ((((σ.orphanChildren ⟨cd, sl, gg⟩).clearSlot cd sl).sweepRegions).sweepMover) := by
  set ref : CapRef := ⟨cd, sl, gg⟩ with href
  set τ := (((σ.orphanChildren ref).clearSlot cd sl).sweepRegions).sweepMover with hτ
  have hcapsτ : ∀ d₂ s₂, ((τ.doms d₂)).caps s₂ =
      if d₂ = cd ∧ s₂ = sl then none else ((σ.orphanChildren ref).doms d₂).caps s₂ := by
    intro d₂ s₂
    rw [hτ, sweepMover_doms, sweepRegions_caps, clearSlot_caps]
  have hgenτ : ∀ d₂ s₂, ¬ (d₂ = cd ∧ s₂ = sl) →
      ((τ.doms d₂)).slotGen s₂ = (σ.doms d₂).slotGen s₂ := by
    intro d₂ s₂ hne
    rw [hτ, sweepMover_doms]
    rw [show (((σ.orphanChildren ref).clearSlot cd sl).sweepRegions.doms d₂).slotGen s₂ =
      (((σ.orphanChildren ref).clearSlot cd sl).doms d₂).slotGen s₂ from by
        rw [sweepRegions_slotGen]]
    rw [clearSlot_slotGen, if_neg hne, orphanChildren_slotGen]
  have hlinτ : ∀ d₂ l₂ cell₂, ((τ.doms d₂)).lineage l₂ = some cell₂ →
      (σ.doms d₂).lineage l₂ = some cell₂ ∧ cell₂.parent ≠ ref := by
    intro d₂ l₂ cell₂ h
    rw [hτ, sweepMover_doms, sweepRegions_lineage, clearSlot_lineage] at h
    split at h
    · exact absurd h (by simp)
    · rw [orphanChildren_lineage] at h
      split at h
      next cell heq =>
        by_cases hcp : cell.parent = ref
        · rw [if_pos (by simpa using hcp)] at h
          exact absurd h (by simp)
        · rw [if_neg (by simpa using hcp)] at h
          rw [heq] at h
          have hc2 := Option.some.inj h
          subst hc2
          exact ⟨heq, hcp⟩
      next heq =>
        rw [if_neg Bool.false_ne_true] at h
        rw [heq] at h
        exact absurd h (by simp)
  -- entries surviving with a lineage index are unmutated
  have hcaps_of : ∀ d₂ s₂ e₂ l₂, ((σ.orphanChildren ref).doms d₂).caps s₂ = some e₂ →
      e₂.lineage = some l₂ → (σ.doms d₂).caps s₂ = some e₂ := by
    intro d₂ s₂ e₂ l₂ hce hl₂
    rcases orphanChildren_caps_kind σ ref d₂ s₂ with ⟨hn, _⟩ | ⟨e₁, e₁', hc₁, hc₁', _, hmut⟩
    · rw [hn] at hce; exact absurd hce (by simp)
    · rw [hce] at hc₁'; injection hc₁' with hh; subst hh
      rcases hmut with rfl | rfl
      · exact hc₁
      · simp at hl₂
  -- surviving entries keep their kind even when mutated
  have hcaps_kind : ∀ d₂ s₂ e₂, ((σ.orphanChildren ref).doms d₂).caps s₂ = some e₂ →
      ∃ e₁, (σ.doms d₂).caps s₂ = some e₁ ∧ e₂.kind = e₁.kind := by
    intro d₂ s₂ e₂ hce
    rcases orphanChildren_caps_kind σ ref d₂ s₂ with ⟨hn, _⟩ | ⟨e₁, e₁', hc₁, hc₁', hk₁, _⟩
    · rw [hn] at hce; exact absurd hce (by simp)
    · rw [hce] at hc₁'; injection hc₁' with hh; subst hh
      exact ⟨e₁, hc₁, hk₁⟩
  intro d₂ s₂ e₂ p₂ ep₂ hce hparτ hliveτ
  obtain ⟨e₂', l₂, cell₂, hce', hl₂, hcellτ, hp₂⟩ := (parentOf_some_iff τ d₂ s₂ p₂).mp hparτ
  rw [hce] at hce'; injection hce' with hee; subst hee
  rw [hcapsτ] at hce
  have hA : ¬ (d₂ = cd ∧ s₂ = sl) := by
    intro hA; rw [if_pos hA] at hce; exact absurd hce (by simp)
  rw [if_neg hA] at hce
  have hceσ : (σ.doms d₂).caps s₂ = some e₂ := hcaps_of d₂ s₂ e₂ l₂ hce hl₂
  obtain ⟨hcellσ, hcpne⟩ := hlinτ d₂ l₂ cell₂ hcellτ
  have hparσ : σ.parentOf d₂ s₂ = some p₂ :=
    (parentOf_some_iff σ d₂ s₂ _).mpr ⟨e₂, l₂, cell₂, hceσ, hl₂, hcellσ, hp₂⟩
  obtain ⟨hcep, hgenp, hg0p⟩ := (liveCap_eq_some _ _ _ _).mp hliveτ
  rw [hcapsτ] at hcep
  have hB : ¬ (p₂.dom = cd ∧ p₂.slot = sl) := by
    intro hB; rw [if_pos hB] at hcep; exact absurd hcep (by simp)
  rw [if_neg hB] at hcep
  obtain ⟨ep₁, hcep₁, hkp⟩ := hcaps_kind p₂.dom p₂.slot ep₂ hcep
  rw [hgenτ _ _ hB] at hgenp
  have hlivep₂ : (σ.doms p₂.dom).liveCap p₂.slot p₂.gen = some ep₁ :=
    (liveCap_eq_some _ _ _ _).mpr ⟨hcep₁, hgenp, hg0p⟩
  have := hcl d₂ s₂ e₂ p₂ ep₁ hceσ hparσ hlivep₂
  rw [this, show ep₂.kind.cls = ep₁.kind.cls from by rw [hkp]]


/-- The shared core of `cl_transferCap`: install at the recipient's free
slot, reparent children of the moved reference, clear and sweep the source.
`σI` is the install state, abstracted over the two lineage shapes. -/
theorem cl_transfer_core (σ σI : MachineState) (from_ : DomainId) (s : Slot)
    (to_ : DomainId) (s2 : Slot) (e : CapEntry) (lin' : Option LineageId)
    (hwf : Wf σ) (hac : Acyclic σ) (hcl : ClassLineage σ)
    (he : (σ.doms from_).caps s = some e)
    (hfree : (σ.doms to_).caps s2 = none)
    (hIcaps : ∀ d₂ s₂', (σI.doms d₂).caps s₂' =
      if d₂ = to_ ∧ s₂' = s2 then some { kind := e.kind, lineage := lin' }
      else (σ.doms d₂).caps s₂')
    (hIgen : ∀ d₂, (σI.doms d₂).slotGen = (σ.doms d₂).slotGen)
    (hlin'free : ∀ l₂, lin' = some l₂ → (σ.doms to_).lineage l₂ = none)
    (hIlin_some : ∀ d₂ l₂ cellI, (σI.doms d₂).lineage l₂ = some cellI →
      ((σ.doms d₂).lineage l₂ = some cellI ∨
      (d₂ = to_ ∧ lin' = some l₂ ∧ σ.parentOf from_ s = some cellI.parent))) :
    ClassLineage ((((σI.reparent ⟨from_, s, (σ.doms from_).slotGen s⟩
      ⟨to_, s2, (σ.doms to_).slotGen s2⟩).clearSlot from_ s).sweepRegions).sweepMover) := by
  set old : CapRef := ⟨from_, s, (σ.doms from_).slotGen s⟩ with hold
  set new : CapRef := ⟨to_, s2, (σ.doms to_).slotGen s2⟩ with hnew
  set τ := (((σI.reparent old new).clearSlot from_ s).sweepRegions).sweepMover with hτ
  have hcapsτ : ∀ d₂ s₂', ((τ.doms d₂)).caps s₂' =
      if d₂ = from_ ∧ s₂' = s then none else (σI.doms d₂).caps s₂' := by
    intro d₂ s₂'
    rw [hτ, sweepMover_doms, sweepRegions_caps, clearSlot_caps, reparent_caps]
  have hgenτ : ∀ d₂ s₂', ¬ (d₂ = from_ ∧ s₂' = s) →
      ((τ.doms d₂)).slotGen s₂' = (σ.doms d₂).slotGen s₂' := by
    intro d₂ s₂' hne
    rw [hτ, sweepMover_doms]
    rw [show (((σI.reparent old new).clearSlot from_ s).sweepRegions.doms d₂).slotGen s₂' =
      (((σI.reparent old new).clearSlot from_ s).doms d₂).slotGen s₂' from by
        rw [sweepRegions_slotGen]]
    rw [clearSlot_slotGen, if_neg hne]
    show ((σI.doms d₂)).slotGen s₂' = _
    rw [hIgen]
  have hlinτ : ∀ d₂ l₂ cell₂, ((τ.doms d₂)).lineage l₂ = some cell₂ →
      ∃ cellI, (σI.doms d₂).lineage l₂ = some cellI ∧
        cell₂ = (if cellI.parent = old then { parent := new } else cellI) := by
    intro d₂ l₂ cell₂ h
    rw [hτ, sweepMover_doms, sweepRegions_lineage, clearSlot_lineage] at h
    split at h
    · exact absurd h (by simp)
    · rw [reparent_lineage] at h
      cases hc : ((σI.doms d₂)).lineage l₂ with
      | none => rw [hc] at h; exact absurd h (by simp)
      | some cellI =>
          rw [hc] at h
          replace h : some (if cellI.parent = old then ({ parent := new } : LineageCell)
              else cellI) = some cell₂ := h
          exact ⟨cellI, rfl, (Option.some.inj h).symm⟩
  have holdlive : (σ.doms from_).liveCap s ((σ.doms from_).slotGen s) = some e :=
    (liveCap_eq_some _ _ _ _).mpr
      ⟨he, rfl, gen_ne_zero_of_pos ((hwf.doms from_).gen_pos s)⟩
  intro d₂ s₂' e₂ p₂ ep₂ hce hparτ hliveτ
  obtain ⟨e₂', l₂, cell₂, hce', hl₂, hcellτ, hp₂⟩ := (parentOf_some_iff τ d₂ s₂' p₂).mp hparτ
  rw [hce] at hce'; injection hce' with hee; subst hee
  rw [hcapsτ] at hce
  have hA : ¬ (d₂ = from_ ∧ s₂' = s) := by
    intro hA; rw [if_pos hA] at hce; exact absurd hce (by simp)
  rw [if_neg hA, hIcaps] at hce
  obtain ⟨hcep, hgenp, hg0p⟩ := (liveCap_eq_some _ _ _ _).mp hliveτ
  rw [hcapsτ] at hcep
  have hB : ¬ (p₂.dom = from_ ∧ p₂.slot = s) := by
    intro hB; rw [if_pos hB] at hcep; exact absurd hcep (by simp)
  rw [if_neg hB, hIcaps] at hcep
  rw [hgenτ _ _ hB] at hgenp
  have hp₂live : ¬ (p₂.dom = to_ ∧ p₂.slot = s2) →
      (σ.doms p₂.dom).liveCap p₂.slot p₂.gen = some ep₂ := by
    intro hne
    rw [if_neg hne] at hcep
    exact (liveCap_eq_some _ _ _ _).mpr ⟨hcep, hgenp, hg0p⟩
  obtain ⟨cellI, hcellI, hcell₂⟩ := hlinτ d₂ l₂ cell₂ hcellτ
  rcases hIlin_some d₂ l₂ cellI hcellI with hcellσ | ⟨hdto, hlin', hqpar⟩
  · -- the parent cell is an old σ-cell; its owner e₂ is an old entry
    have hBentry : ¬ (d₂ = to_ ∧ s₂' = s2) := by
      rintro ⟨h1, h2⟩
      rw [if_pos ⟨h1, h2⟩] at hce
      injection hce with hce; subst hce
      simp only at hl₂
      have := hlin'free l₂ hl₂
      rw [h1] at hcellσ
      rw [this] at hcellσ
      exact absurd hcellσ (by simp)
    rw [if_neg hBentry] at hce
    by_cases hcp : cellI.parent = old
    · -- a child of the moved capability, reparented to `new`
      rw [if_pos hcp] at hcell₂
      subst hcell₂
      simp only at hp₂; subst hp₂
      have hparσ : σ.parentOf d₂ s₂' = some old :=
        (parentOf_some_iff σ d₂ s₂' _).mpr ⟨e₂, l₂, cellI, hce, hl₂, hcellσ, hcp⟩
      have h1 : e₂.kind.cls = e.kind.cls := hcl d₂ s₂' e₂ old e hce hparσ holdlive
      rw [if_pos ⟨rfl, rfl⟩] at hcep
      injection hcep with hcep; subst hcep
      exact h1
    · rw [if_neg hcp] at hcell₂
      rw [hcell₂] at hp₂
      have hparσ : σ.parentOf d₂ s₂' = some p₂ :=
        (parentOf_some_iff σ d₂ s₂' _).mpr ⟨e₂, l₂, cellI, hce, hl₂, hcellσ, hp₂⟩
      have hne : ¬ (p₂.dom = to_ ∧ p₂.slot = s2) := by
        rintro ⟨h1, h2⟩
        have hlr := hwf.parent_live d₂ s₂' p₂ hparσ
        unfold MachineState.liveRef DomainState.liveCap at hlr
        rw [h1, h2, hfree] at hlr
        simp at hlr
      exact hcl d₂ s₂' e₂ p₂ ep₂ hce hparσ (hp₂live hne)
  · -- the parent cell is the freshly installed one: e₂ is the moved entry
    have hq : σ.parentOf from_ s = some cellI.parent := hqpar
    have hqne : cellI.parent ≠ old := by
      have := hac.parentRef_ne σ old cellI.parent
        (show σ.parentRef old = some cellI.parent from hq)
      exact this
    rw [if_neg hqne] at hcell₂
    rw [hcell₂] at hp₂
    -- e₂ must be the fresh entry: an old entry cannot use the fresh cell
    have hEfresh : d₂ = to_ ∧ s₂' = s2 := by
      by_contra hcon
      rw [if_neg hcon] at hce
      have hbacked := (hwf.doms d₂).cell_backed s₂' e₂ l₂ hce hl₂
      rw [hdto, hlin'free l₂ hlin'] at hbacked
      exact absurd hbacked (by simp)
    rw [if_pos hEfresh] at hce
    injection hce with hce; subst hce
    have hne : ¬ (p₂.dom = to_ ∧ p₂.slot = s2) := by
      rintro ⟨h1, h2⟩
      have hlr := hwf.parent_live from_ s p₂ (hp₂ ▸ hq)
      unfold MachineState.liveRef DomainState.liveCap at hlr
      rw [h1, h2, hfree] at hlr
      simp at hlr
    have h2 : e.kind.cls = ep₂.kind.cls :=
      hcl from_ s e p₂ ep₂ he (hp₂ ▸ hq) (hp₂live hne)
    exact h2

/-- `transferCap` preserves `ClassLineage`. -/
theorem cl_transferCap (σ : MachineState) (from_ : DomainId) (s : Slot) (to_ : DomainId)
    (τ : MachineState) (ref : CapRef)
    (hwf : Wf σ) (hac : Acyclic σ) (hcl : ClassLineage σ)
    (h : σ.transferCap from_ s to_ = some (τ, ref)) :
    ClassLineage τ := by
  unfold MachineState.transferCap at h
  cases he : (σ.doms from_).caps s with
  | none => rw [he] at h; simp at h
  | some e =>
      rw [he] at h; simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hfs : σ.freeSlot to_ with
      | none => rw [hfs] at h; simp at h
      | some s2 =>
          rw [hfs] at h; simp only [Option.bind_some] at h
          obtain ⟨hfree, hnr⟩ := freeSlot_spec σ to_ s2 hfs
          cases hl : e.lineage with
          | none =>
              rw [hl] at h; simp only [Option.pure_def, Option.bind_some] at h
              injection h with h; injection h with hτ _; subst hτ
              refine cl_transfer_core σ _ from_ s to_ s2 e none hwf hac hcl he hfree
                ?_ ?_ (by intro l₂ hll; exact absurd hll (by simp)) ?_
              · intro d₂ s₂'
                show ((σ.setDom to_ _).doms d₂).caps s₂' = _
                unfold MachineState.setDom
                by_cases hd : d₂ = to_
                · subst hd
                  simp only [Loom.Fun.update_same, true_and]
                  by_cases hs2 : s₂' = s2
                  · subst hs2; simp [Loom.Fun.update_same]
                  · simp [Loom.Fun.update_ne _ _ _ _ hs2, hs2]
                · simp [Loom.Fun.update_ne _ _ _ _ hd, hd]
              · intro d₂
                show ((σ.setDom to_ _).doms d₂).slotGen = _
                unfold MachineState.setDom
                by_cases hd : d₂ = to_
                · subst hd; simp [Loom.Fun.update_same]
                · simp [Loom.Fun.update_ne _ _ _ _ hd]
              · intro d₂ l₂ cellI hcellI
                left
                revert hcellI
                show ((σ.setDom to_ _).doms d₂).lineage l₂ = some cellI → _
                unfold MachineState.setDom
                by_cases hd : d₂ = to_
                · subst hd; simp [Loom.Fun.update_same]
                · simp [Loom.Fun.update_ne _ _ _ _ hd]
          | some l =>
              rw [hl] at h; simp only [Option.bind_eq_bind, Option.bind_some] at h
              cases hcell : (σ.doms from_).lineage l with
              | none => rw [hcell] at h; simp at h
              | some cell₀ =>
                  rw [hcell] at h; simp only [Option.bind_some] at h
                  cases hfc : σ.freeCell to_ with
                  | none => rw [hfc] at h; simp at h
                  | some l' =>
                      rw [hfc] at h; simp only [Option.pure_def, Option.bind_some] at h
                      injection h with h; injection h with hτ _; subst hτ
                      have hlfree := freeCell_spec σ to_ l' hfc
                      refine cl_transfer_core σ _ from_ s to_ s2 e (some l') hwf hac hcl
                        he hfree ?_ ?_ ?_ ?_
                      · intro d₂ s₂'
                        show ((σ.setDom to_ _).doms d₂).caps s₂' = _
                        unfold MachineState.setDom
                        by_cases hd : d₂ = to_
                        · subst hd
                          simp only [Loom.Fun.update_same, true_and]
                          by_cases hs2 : s₂' = s2
                          · subst hs2; simp [Loom.Fun.update_same]
                          · simp [Loom.Fun.update_ne _ _ _ _ hs2, hs2]
                        · simp [Loom.Fun.update_ne _ _ _ _ hd, hd]
                      · intro d₂
                        show ((σ.setDom to_ _).doms d₂).slotGen = _
                        unfold MachineState.setDom
                        by_cases hd : d₂ = to_
                        · subst hd; simp [Loom.Fun.update_same]
                        · simp [Loom.Fun.update_ne _ _ _ _ hd]
                      · intro l₂ hll
                        injection hll with hll; subst hll
                        exact hlfree
                      · intro d₂ l₂ cellI hcellI
                        replace hcellI : ((σ.setDom to_ (fun ds =>
                            { ds with
                              caps := Loom.Fun.update ds.caps s2
                                (some { kind := e.kind, lineage := some l' })
                              lineage := Loom.Fun.update ds.lineage l'
                                (some cell₀) })).doms d₂).lineage l₂ = some cellI := hcellI
                        unfold MachineState.setDom at hcellI
                        by_cases hd : d₂ = to_
                        · subst hd
                          simp only [Loom.Fun.update_same] at hcellI
                          by_cases hll : l₂ = l'
                          · subst hll
                            rw [Loom.Fun.update_same] at hcellI
                            injection hcellI with hcellI; subst hcellI
                            right
                            refine ⟨rfl, rfl, ?_⟩
                            exact (parentOf_some_iff σ from_ s _).mpr
                              ⟨e, l, cell₀, he, hl, hcell, rfl⟩
                          · rw [Loom.Fun.update_ne _ _ _ _ hll] at hcellI
                            exact Or.inl hcellI
                        · simp only [Loom.Fun.update_ne _ _ _ _ hd] at hcellI
                          exact Or.inl hcellI


/-! ## The class-lineage preservation kit -/

/-- Read-only computations: every outcome leaves the state unchanged. -/
def ReadOnly {α : Type} (mm : SpecM α) : Prop :=
  ∀ σ, (∀ a σ', mm σ = .ok a σ' → σ' = σ) ∧ (∀ e σ', mm σ = .err e σ' → σ' = σ)

theorem ReadOnly.reg (d : DomainId) (r : RegId) : ReadOnly (SpecM.reg d r) :=
  fun σ => ⟨fun a σ' he => by unfold SpecM.reg at he; injection he with _ h2; exact h2.symm,
            fun e σ' he => by unfold SpecM.reg at he; simp at he⟩

theorem ReadOnly.require (cond : Bool) (e : Errno) : ReadOnly (SpecM.require cond e) :=
  fun σ => ⟨fun a σ' he => require_ok cond e σ he,
            fun e' σ' he => require_err_state cond e σ he⟩

theorem ReadOnly.raise {α : Type} (e : Errno) : ReadOnly (SpecM.raise e : SpecM α) :=
  fun σ => ⟨fun a σ' he => by unfold SpecM.raise at he; simp at he,
            fun e' σ' he => by unfold SpecM.raise at he; injection he with _ h2; exact h2.symm⟩

theorem ReadOnly.capLive (d : DomainId) (hw : Loom.Word32) :
    ReadOnly (Machines.Lnp64u.Isa.capLive d hw) :=
  fun σ => ⟨fun a σ' he => (Machines.Lnp64u.Isa.Wip.capLive_ok d hw σ he).1,
            fun e σ' he => Machines.Lnp64u.Isa.Wip.capLive_err_state d hw σ he⟩

theorem ReadOnly.narrow (base : Addr) (len : BitVec 13) (perms : Perms) (dw : Loom.Word32) :
    ReadOnly (Machines.Lnp64u.Isa.narrow base len perms dw) :=
  fun σ => ⟨fun k σ' he => (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms dw σ he).1,
            fun e σ' he => Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms dw σ he⟩

/-- Tables-preserving outcomes from a fixed start state. -/
def TFrom (σ0 : MachineState) {α : Type} (mm : SpecM α) : Prop :=
  (∀ a σ', mm σ0 = .ok a σ' → TablesEq σ0 σ') ∧
  (∀ e σ', mm σ0 = .err e σ' → TablesEq σ0 σ')

theorem TablesEq.refl (σ : MachineState) : TablesEq σ σ := fun _ => ⟨rfl, rfl, rfl⟩

theorem TablesEq.trans {σ₁ σ₂ σ₃ : MachineState} (h₁ : TablesEq σ₁ σ₂) (h₂ : TablesEq σ₂ σ₃) :
    TablesEq σ₁ σ₃ :=
  fun d => ⟨(h₂ d).1.trans (h₁ d).1, (h₂ d).2.1.trans (h₁ d).2.1, (h₂ d).2.2.trans (h₁ d).2.2⟩

theorem TFrom.of_quiet {σ0 : MachineState} {α : Type} {mm : SpecM α}
    (h : QuietPres mm) : TFrom σ0 mm :=
  ⟨fun a σ' he => ((h σ0).1 a σ' he).1, fun e σ' he => ((h σ0).2 e σ' he).1⟩

theorem TFrom.bind {σ0 : MachineState} {α β : Type} {m : SpecM α} {f : α → SpecM β}
    (hm : TFrom σ0 m) (hf : ∀ a σ1, m σ0 = .ok a σ1 → TFrom σ1 (f a)) :
    TFrom σ0 (m >>= f) := by
  constructor
  · intro b σ' he
    rw [specM_bind] at he
    cases hm2 : m σ0 with
    | ok a σ1 => rw [hm2] at he
                 exact (hm.1 a σ1 hm2).trans ((hf a σ1 hm2).1 b σ' he)
    | err e σ1 => rw [hm2] at he; simp at he
    | fault g => rw [hm2] at he; simp at he
  · intro e σ' he
    rw [specM_bind] at he
    cases hm2 : m σ0 with
    | ok a σ1 => rw [hm2] at he
                 exact (hm.1 a σ1 hm2).trans ((hf a σ1 hm2).2 e σ' he)
    | err e1 σ1 => rw [hm2] at he; injection he with h1 h2; subst h2
                   exact hm.2 e1 σ1 hm2
    | fault g => rw [hm2] at he; simp at he

theorem TFrom.get_bind {σ0 : MachineState} {β : Type} {f : MachineState → SpecM β}
    (h : TFrom σ0 (f σ0)) : TFrom σ0 (SpecM.get >>= f) :=
  ⟨fun b σ' he => h.1 b σ' (by rw [specM_bind] at he; exact he),
   fun e σ' he => h.2 e σ' (by rw [specM_bind] at he; exact he)⟩

theorem TFrom.set {σ0 X : MachineState} (h : TablesEq σ0 X) :
    TFrom σ0 (SpecM.set X) := by
  constructor
  · intro a σ' he
    unfold SpecM.set at he; injection he with _ h2; subst h2; exact h
  · intro e σ' he; unfold SpecM.set at he; simp at he

theorem TFrom.fatal {σ0 : MachineState} {α : Type} (f : Fault) :
    TFrom σ0 (SpecM.fatal f : SpecM α) := by
  constructor
  · intro a σ' he; unfold SpecM.fatal at he; simp at he
  · intro e σ' he; unfold SpecM.fatal at he; simp at he

/-- Class-lineage-producing outcomes from a fixed start state. -/
def CLFrom (σ0 : MachineState) {α : Type} (mm : SpecM α) : Prop :=
  (∀ a σ', mm σ0 = .ok a σ' → ClassLineage σ') ∧
  (∀ e σ', mm σ0 = .err e σ' → ClassLineage σ')

theorem CLFrom.of_tfrom {σ0 : MachineState} {α : Type} {mm : SpecM α}
    (h : TFrom σ0 mm) (hcl : ClassLineage σ0) : CLFrom σ0 mm :=
  ⟨fun a σ' he => classLineage_of_tablesEq (h.1 a σ' he) hcl,
   fun e σ' he => classLineage_of_tablesEq (h.2 e σ' he) hcl⟩

theorem CLFrom.set {σ0 X : MachineState} (h : ClassLineage X) :
    CLFrom σ0 (SpecM.set X) := by
  constructor
  · intro a σ' he
    unfold SpecM.set at he; injection he with _ h2; subst h2; exact h
  · intro e σ' he; unfold SpecM.set at he; simp at he

theorem CLFrom.fatal {σ0 : MachineState} {α : Type} (f : Fault) :
    CLFrom σ0 (SpecM.fatal f : SpecM α) := by
  constructor
  · intro a σ' he; unfold SpecM.fatal at he; simp at he
  · intro e σ' he; unfold SpecM.fatal at he; simp at he

theorem CLFrom.get_bind {σ0 : MachineState} {β : Type} {f : MachineState → SpecM β}
    (h : CLFrom σ0 (f σ0)) : CLFrom σ0 (SpecM.get >>= f) :=
  ⟨fun b σ' he => h.1 b σ' (by rw [specM_bind] at he; exact he),
   fun e σ' he => h.2 e σ' (by rw [specM_bind] at he; exact he)⟩

/-- Bind a read-only prefix: the continuation runs at the same state and may
use the prefix's result equation. -/
theorem CLFrom.bind_ro {σ0 : MachineState} {α β : Type} {m : SpecM α} {f : α → SpecM β}
    (hro : ReadOnly m) (hcl0 : ClassLineage σ0)
    (hf : ∀ a, m σ0 = .ok a σ0 → CLFrom σ0 (f a)) :
    CLFrom σ0 (m >>= f) := by
  constructor
  · intro b σ' he
    rw [specM_bind] at he
    cases hm2 : m σ0 with
    | ok a σ1 =>
        have h1 := (hro σ0).1 a σ1 hm2; subst h1
        rw [hm2] at he
        exact (hf a hm2).1 b σ' he
    | err e σ1 => rw [hm2] at he; simp at he
    | fault g => rw [hm2] at he; simp at he
  · intro e σ' he
    rw [specM_bind] at he
    cases hm2 : m σ0 with
    | ok a σ1 =>
        have h1 := (hro σ0).1 a σ1 hm2; subst h1
        rw [hm2] at he
        exact (hf a hm2).2 e σ' he
    | err e1 σ1 =>
        have h1 := (hro σ0).2 e1 σ1 hm2; subst h1
        rw [hm2] at he; injection he with _ h2; subst h2
        exact hcl0
    | fault g => rw [hm2] at he; simp at he

/-- Bind a class-lineage-producing prefix with a tables-preserving tail. -/
theorem CLFrom.bind_t {σ0 : MachineState} {α β : Type} {m : SpecM α} {f : α → SpecM β}
    (hm : CLFrom σ0 m) (hf : ∀ a σ1, m σ0 = .ok a σ1 → TFrom σ1 (f a)) :
    CLFrom σ0 (m >>= f) := by
  constructor
  · intro b σ' he
    rw [specM_bind] at he
    cases hm2 : m σ0 with
    | ok a σ1 => rw [hm2] at he
                 exact classLineage_of_tablesEq ((hf a σ1 hm2).1 b σ' he) (hm.1 a σ1 hm2)
    | err e σ1 => rw [hm2] at he; simp at he
    | fault g => rw [hm2] at he; simp at he
  · intro e σ' he
    rw [specM_bind] at he
    cases hm2 : m σ0 with
    | ok a σ1 => rw [hm2] at he
                 exact classLineage_of_tablesEq ((hf a σ1 hm2).2 e σ' he) (hm.1 a σ1 hm2)
    | err e1 σ1 => rw [hm2] at he; injection he with h1 h2; subst h2
                   exact hm.2 e1 σ1 hm2
    | fault g => rw [hm2] at he; simp at he

/-- `allocDerived` preserves `ClassLineage` when the parent is live with a
matching class. -/
theorem cl_allocDerived (σ : MachineState) (owner : DomainId) (kind : CapKind)
    (parent : CapRef) (pe : CapEntry)
    (hwf : Wf σ) (hcl : ClassLineage σ)
    (hplive : (σ.doms parent.dom).liveCap parent.slot parent.gen = some pe)
    (hkcls : kind.cls = pe.kind.cls) :
    CLFrom σ (Machines.Lnp64u.Isa.allocDerived owner kind parent) := by
  unfold Machines.Lnp64u.Isa.allocDerived
  refine CLFrom.get_bind ?_
  cases hfs : σ.freeSlot owner with
  | none =>
      refine ⟨fun a σ' he => ?_, fun e σ' he => ?_⟩
      · simp [SpecM.raise] at he
      · simp only [SpecM.raise] at he
        injection he with _ h2; subst h2; exact hcl
  | some sl =>
      simp only [hfs]
      cases hfc : σ.freeCell owner with
      | none =>
          refine ⟨fun a σ' he => ?_, fun e σ' he => ?_⟩
          · simp [SpecM.raise] at he
          · simp only [SpecM.raise] at he
            injection he with _ h2; subst h2; exact hcl
      | some lc =>
          simp only []
          refine CLFrom.bind_t (CLFrom.set ?_)
            (fun _ σ1 _ => TFrom.of_quiet (QuietPres.pure _))
          exact cl_installDerived σ owner sl lc kind parent hwf hcl hfs hfc pe hplive hkcls

/-- `transferByHandle` preserves `ClassLineage`. -/
theorem cl_transferByHandle (σ : MachineState) (d to_ : DomainId) (hw : Loom.Word32)
    (hwf : Wf σ) (hac : Acyclic σ) (hcl : ClassLineage σ) :
    CLFrom σ (Machines.Lnp64u.Isa.transferByHandle d to_ hw) := by
  unfold Machines.Lnp64u.Isa.transferByHandle
  by_cases hz : hw = 0
  · rw [if_pos hz]
    exact ⟨fun a σ' he => by rw [specM_pure] at he; injection he with _ h2; subst h2; exact hcl,
           fun e σ' he => by rw [specM_pure] at he; simp at he⟩
  · rw [if_neg hz]
    refine CLFrom.bind_ro (ReadOnly.capLive d hw) hcl fun r hcl2 => ?_
    obtain ⟨sl, gg, ee⟩ := r
    simp only []
    refine CLFrom.get_bind ?_
    cases htc : σ.transferCap d sl to_ with
    | none =>
        simp only [htc]
        refine ⟨fun a σ' he => ?_, fun e σ' he => ?_⟩
        · simp [SpecM.raise] at he
        · simp only [SpecM.raise] at he
          injection he with _ h2; subst h2; exact hcl
    | some pr =>
        obtain ⟨τ, ref⟩ := pr
        simp only [htc]
        refine CLFrom.bind_t (CLFrom.set ?_)
          (fun _ σ1 _ => TFrom.of_quiet (QuietPres.pure _))
        exact cl_transferCap σ d sl to_ τ ref hwf hac hcl htc


theorem ReadOnly.pure {α : Type} (a : α) : ReadOnly (Pure.pure a : SpecM α) :=
  fun σ => ⟨fun a' σ' he => by rw [specM_pure] at he; injection he with _ h2; exact h2.symm,
            fun e σ' he => by rw [specM_pure] at he; simp at he⟩

/-- `move`'s exec preserves the capability tables. -/
theorem move_tfrom (c : Ctx) (σ0 : MachineState) :
    TFrom σ0 (Machines.Lnp64u.Isa.Wip.moveExec c) := by
  unfold Machines.Lnp64u.Isa.Wip.moveExec
  refine TFrom.get_bind ?_
  refine TFrom.bind (TFrom.of_quiet (QuietPres.require _ _)) fun _ σ1 _ => ?_
  refine TFrom.bind (TFrom.of_quiet (QuietPres.reg _ _)) fun aw σ2 _ => ?_
  refine TFrom.bind (TFrom.of_quiet (QuietPres.load _ _)) fun srcH σ3 _ => ?_
  refine TFrom.bind (TFrom.of_quiet (QuietPres.load _ _)) fun dstH σ4 _ => ?_
  refine TFrom.bind (TFrom.of_quiet (QuietPres.load _ _)) fun lenW σ5 _ => ?_
  refine TFrom.bind (TFrom.of_quiet (QuietPres.load _ _)) fun stW σ6 _ => ?_
  refine TFrom.bind (TFrom.of_quiet (QuietPres.capLive _ _)) fun rs σ7 _ => ?_
  obtain ⟨ss, gs_, es⟩ := rs
  simp only []
  refine TFrom.bind (TFrom.of_quiet (QuietPres.capLive _ _)) fun rd σ8 _ => ?_
  obtain ⟨sd, gd, ed⟩ := rd
  simp only []
  cases es.kind with
  | gate gg =>
      cases ed.kind with
      | gate _ => exact TFrom.of_quiet (QuietPres.raise _)
      | mem _ _ _ => exact TFrom.of_quiet (QuietPres.raise _)
  | mem sb sl sp =>
      cases ed.kind with
      | gate _ => exact TFrom.of_quiet (QuietPres.raise _)
      | mem db dl dp =>
          refine TFrom.bind (TFrom.of_quiet (QuietPres.require _ _)) fun _ σa _ => ?_
          refine TFrom.bind (TFrom.of_quiet (QuietPres.require _ _)) fun _ σb _ => ?_
          refine TFrom.bind (TFrom.of_quiet (QuietPres.require _ _)) fun _ σc _ => ?_
          refine TFrom.get_bind ?_
          refine TFrom.bind (TFrom.of_quiet (QuietPres.demand _ _)) fun _ σd hd => ?_
          obtain rfl := (demand_ok _ _ _ hd).symm
          refine TFrom.bind (TFrom.set ?_) fun _ σe _ => TFrom.of_quiet (QuietPres.setReg _ _ _)
          intro d
          exact ⟨rfl, rfl, rfl⟩

/-- The eleven system opcodes preserve `ClassLineage`. -/
theorem system_cl : ∀ instr ∈ Machines.Lnp64u.Isa.system, ∀ (c : Ctx) (σ : MachineState),
    Wf σ → Acyclic σ → ClassLineage σ → CLFrom σ (instr.sem.exec c) := by
  intro instr hmem c σ hwf hac hcl
  fin_cases hmem
  case _ => -- cap_dup
    refine CLFrom.bind_ro (ReadOnly.reg _ _) hcl fun hw hhw => ?_
    refine CLFrom.bind_ro (ReadOnly.reg _ _) hcl fun dw hdw => ?_
    refine CLFrom.bind_ro (ReadOnly.capLive _ _) hcl fun r hr => ?_
    obtain ⟨s, g, e⟩ := r
    have hlive := (Machines.Lnp64u.Isa.Wip.capLive_ok c.d hw σ hr).2
    simp only []
    cases hk : e.kind with
    | mem base len perms =>
        refine CLFrom.bind_ro (ReadOnly.narrow _ _ _ _) hcl fun kind hkind => ?_
        obtain ⟨_, off, nlen, np, hkindeq, _, _⟩ :=
          Machines.Lnp64u.Isa.Wip.narrow_ok _ _ _ _ σ hkind
        refine CLFrom.bind_t (cl_allocDerived σ c.d kind ⟨c.d, s, g⟩ e hwf hcl hlive ?_)
          fun h σ1 _ => TFrom.of_quiet (QuietPres.setReg _ _ _)
        rw [hkindeq, hk]; rfl
    | gate gid =>
        refine CLFrom.bind_ro (ReadOnly.pure _) hcl fun kind hkind => ?_
        have hkeq : kind = .gate gid := by
          rw [specM_pure] at hkind; injection hkind with h1 _; exact h1.symm
        refine CLFrom.bind_t (cl_allocDerived σ c.d kind ⟨c.d, s, g⟩ e hwf hcl hlive ?_)
          fun h σ1 _ => TFrom.of_quiet (QuietPres.setReg _ _ _)
        rw [hkeq, hk]
  case _ => -- cap_drop
    refine CLFrom.bind_ro (ReadOnly.reg _ _) hcl fun hw hhw => ?_
    refine CLFrom.bind_ro (ReadOnly.capLive _ _) hcl fun r hr => ?_
    obtain ⟨s, g, e⟩ := r
    have hlive := (Machines.Lnp64u.Isa.Wip.capLive_ok c.d hw σ hr).2
    simp only []
    refine CLFrom.get_bind ?_
    refine CLFrom.bind_t ?_ (fun _ σ1 _ => TFrom.of_quiet (QuietPres.setReg _ _ _))
    cases hp : σ.parentOf c.d s with
    | some p => exact CLFrom.set (cl_dropCore σ c.d s g e p hwf hac hcl hlive hp)
    | none => exact CLFrom.set (cl_dropOrphan σ c.d s g hwf hcl)
  case _ => -- cap_revoke
    refine CLFrom.bind_ro (ReadOnly.reg _ _) hcl fun hw hhw => ?_
    refine CLFrom.bind_ro (ReadOnly.capLive _ _) hcl fun r hr => ?_
    obtain ⟨s, g, e⟩ := r
    simp only []
    refine CLFrom.bind_ro (ReadOnly.require _ _) hcl fun _ _ => ?_
    refine CLFrom.get_bind ?_
    exact CLFrom.bind_t (CLFrom.set (cl_destroySweep σ _ hcl))
      (fun _ σ1 _ => TFrom.of_quiet (QuietPres.setReg _ _ _))
  case _ => -- mem_grant
    refine CLFrom.bind_ro (ReadOnly.reg _ _) hcl fun hw hhw => ?_
    refine CLFrom.bind_ro (ReadOnly.reg _ _) hcl fun dw hdw => ?_
    refine CLFrom.bind_ro (ReadOnly.capLive _ _) hcl fun r hr => ?_
    obtain ⟨s, g, e⟩ := r
    have hlive := (Machines.Lnp64u.Isa.Wip.capLive_ok c.d hw σ hr).2
    simp only []
    cases hk : e.kind with
    | gate gid => exact CLFrom.of_tfrom (TFrom.of_quiet (QuietPres.raise _)) hcl
    | mem base len perms =>
        refine CLFrom.bind_ro (ReadOnly.narrow _ _ _ _) hcl fun kind hkind => ?_
        obtain ⟨_, off, nlen, np, hkindeq, _, _⟩ :=
          Machines.Lnp64u.Isa.Wip.narrow_ok _ _ _ _ σ hkind
        refine CLFrom.bind_t (cl_allocDerived σ (descDom dw) kind ⟨c.d, s, g⟩ e hwf hcl hlive ?_)
          fun h σ1 _ => TFrom.of_quiet (QuietPres.setReg _ _ _)
        rw [hkindeq, hk]; rfl
  case _ => exact CLFrom.of_tfrom (TFrom.of_quiet (map_quiet c)) hcl
  case _ => exact CLFrom.of_tfrom (TFrom.of_quiet (QuietPres.bind
      (QuietPres.updDom _ _ (fun ds => ⟨rfl, rfl, rfl⟩)) (fun _ => QuietPres.setReg _ _ _))) hcl
  case _ => -- gate_call
    refine CLFrom.bind_ro (ReadOnly.reg _ _) hcl fun hw hhw => ?_
    refine CLFrom.bind_ro (ReadOnly.capLive _ _) hcl fun r hr => ?_
    obtain ⟨s0, g0, e⟩ := r
    simp only []
    cases hk : e.kind with
    | mem base len perms => exact CLFrom.of_tfrom (TFrom.of_quiet (QuietPres.raise _)) hcl
    | gate gid =>
        refine CLFrom.get_bind ?_
        refine CLFrom.bind_ro (ReadOnly.require _ _) hcl fun _ _ => ?_
        refine CLFrom.bind_ro (ReadOnly.require _ _) hcl fun _ _ => ?_
        refine CLFrom.bind_ro (ReadOnly.require _ _) hcl fun _ _ => ?_
        refine CLFrom.bind_ro (ReadOnly.require _ _) hcl fun _ _ => ?_
        refine CLFrom.bind_ro (ReadOnly.require _ _) hcl fun _ _ => ?_
        refine CLFrom.bind_ro (ReadOnly.reg _ _) hcl fun argw _ => ?_
        refine CLFrom.bind_t (cl_transferByHandle σ c.d _ argw hwf hac hcl)
          fun argH τ htbh => ?_
        refine TFrom.get_bind ?_
        refine TFrom.bind (TFrom.set (fun d => ⟨rfl, rfl, rfl⟩)) fun _ τ2 _ => ?_
        refine TFrom.bind (TFrom.of_quiet (QuietPres.updDom _ _ (fun ds => ⟨rfl, rfl, rfl⟩)))
          fun _ τ3 _ => ?_
        exact TFrom.of_quiet (QuietPres.updDom _ _ (fun ds => ⟨rfl, rfl, rfl⟩))
  case _ => -- gate_return
    refine CLFrom.get_bind ?_
    cases (σ.doms c.d).serving with
    | none => exact CLFrom.fatal _
    | some gid =>
        simp only []
        cases (σ.gates gid).act with
        | none => exact CLFrom.fatal _
        | some act =>
            simp only []
            refine CLFrom.bind_ro (ReadOnly.reg _ _) hcl fun rw _ => ?_
            refine CLFrom.bind_t (cl_transferByHandle σ c.d act.caller rw hwf hac hcl)
              fun reply τ _ => ?_
            refine TFrom.get_bind ?_
            refine TFrom.bind (TFrom.set (fun d => ⟨rfl, rfl, rfl⟩)) fun _ τ2 _ => ?_
            refine TFrom.bind (TFrom.of_quiet (QuietPres.updDom _ _ (fun ds => ⟨rfl, rfl, rfl⟩)))
              fun _ τ3 _ => ?_
            refine TFrom.bind (TFrom.of_quiet (QuietPres.updDom _ _ (fun ds => ⟨rfl, rfl, rfl⟩)))
              fun _ τ4 _ => ?_
            exact TFrom.of_quiet (QuietPres.setReg _ _ _)
  case _ => exact CLFrom.of_tfrom (move_tfrom c σ) hcl
  case _ => exact CLFrom.of_tfrom (TFrom.of_quiet (QuietPres.bind
      (QuietPres.updDom _ _ (fun ds => ⟨rfl, rfl, rfl⟩)) (fun _ => QuietPres.setReg _ _ _))) hcl
  case _ => exact CLFrom.of_tfrom (TFrom.of_quiet
      (QuietPres.modify _ (fun σ' => quiet_haltDom σ' c.d 0))) hcl

/-- Every ISA instruction preserves `ClassLineage`. -/
theorem exec_cl : ∀ instr ∈ isa, ∀ (c : Ctx) (σ : MachineState),
    Wf σ → Acyclic σ → ClassLineage σ → CLFrom σ (instr.sem.exec c) := by
  intro instr hmem c σ hwf hac hcl
  have hmem' : instr ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
    have hiseq : Machines.Lnp64u.isa =
      (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray := rfl
    rw [hiseq, Array.mem_toArray] at hmem; exact hmem
  rcases List.mem_append.mp hmem' with hb | hs
  · exact CLFrom.of_tfrom (TFrom.of_quiet (base_quiet instr hb c)) hcl
  · exact system_cl instr hs c σ hwf hac hcl

/-! ## Class-lineage lifts and the machine invariant -/

theorem retire_cl (σ : MachineState) (d : DomainId) (w : Loom.Word32)
    (hwf : Wf σ) (hac : Acyclic σ) (hcl : ClassLineage σ)
    (hdrun : (σ.doms d).run = .running) (hinf : σ.inflight = none) :
    ClassLineage (retire σ d w) := by
  unfold retire
  split
  · exact classLineage_of_tablesEq (quiet_haltDom σ d _).1 hcl
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
    have hσ1cl : ClassLineage σ1 :=
      classLineage_of_tablesEq
        (fun d' => ⟨(hpcproj d').1, (hpcproj d').2.1, (hpcproj d').2.2.1⟩) hcl
    have hmem : instr ∈ isa := Loom.Isa.decode_mem isa hdec
    have hexec := exec_cl instr hmem { d := d, pc := (σ.doms d).pc, op := operandsOf w }
      σ1 hσ1wf hσ1ac hσ1cl
    cases hexr : instr.sem.exec { d := d, pc := (σ.doms d).pc, op := operandsOf w } σ1 with
    | ok a σ' =>
        simp only [hexr]
        exact hexec.1 a σ' hexr
    | err e σ' =>
        simp only [hexr]
        exact classLineage_of_tablesEq
          (quiet_setDom σ' d _ ⟨setReg_caps _ _ _, setReg_lineage _ _ _, setReg_slotGen _ _ _⟩).1
          (hexec.2 e σ' hexr)
    | fault f =>
        simp only [hexr]
        exact classLineage_of_tablesEq (quiet_haltDom σ d _).1 hcl

theorem corePhase_cl (m : Manifest) (σ : MachineState)
    (hwf : Wf σ) (hac : Acyclic σ) (hcl : ClassLineage σ) :
    ClassLineage (corePhase m σ) := by
  unfold corePhase
  cases hinf : σ.inflight with
  | some fl =>
      by_cases hcy : fl.cyclesLeft ≤ 1
      · simp only [hcy, if_true]
        have hwf' : Wf { σ with inflight := none } :=
          wf_of_skeleton_sameGates σ { σ with inflight := none }
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
            (fun _ => rfl) rfl rfl (by simp) hwf
        have hac' : Acyclic { σ with inflight := none } :=
          acyclic_of_parentRef_eq σ _
            (parentRef_eq_of_doms σ _ (fun _ => ⟨rfl, rfl⟩)) hac
        have hcl' : ClassLineage { σ with inflight := none } :=
          classLineage_of_tablesEq (fun _ => ⟨rfl, rfl, rfl⟩) hcl
        refine retire_cl _ fl.dom fl.word hwf' hac' hcl' ?_ rfl
        show (σ.doms fl.dom).run = .running
        exact hwf.inflight_running fl hinf
      · simp only [hcy, if_false]
        exact classLineage_of_tablesEq (fun _ => ⟨rfl, rfl, rfl⟩) hcl
  | none =>
      simp only []
      split
      · exact hcl
      · rename_i d hsched
        split
        · exact classLineage_of_tablesEq (quiet_haltDom σ _ _).1 hcl
        · rename_i w hfetch
          split
          · exact classLineage_of_tablesEq (quiet_haltDom σ _ _).1 hcl
          · rename_i instr hdec
            by_cases hbud : instr.cost.cost ≤ (σ.doms (σ.payer d)).budget
            · simp only [hbud, if_true]
              obtain ⟨pc, pl, pg, pr, pru, ps, pgates, pmov⟩ :=
                setBudget_proj σ (σ.payer d) (fun ds => ds.budget - instr.cost.cost)
              have hclb : ClassLineage (σ.setDom (σ.payer d)
                  (fun ds => { ds with budget := ds.budget - instr.cost.cost })) :=
                classLineage_of_tablesEq (fun d' => ⟨pc d', pl d', pg d'⟩) hcl
              cases hserv : (σ.doms d).serving with
              | none =>
                  simp only [hserv]
                  exact classLineage_of_tablesEq (fun _ => ⟨rfl, rfl, rfl⟩) hclb
              | some g =>
                  simp only [hserv]
                  cases hact : (σ.gates g).act with
                  | none => exact classLineage_of_tablesEq (quiet_haltDom σ _ _).1 hcl
                  | some a =>
                      simp only [hact]
                      by_cases hdon : instr.cost.cost ≤ a.donated
                      · simp only [hdon, if_true]
                        exact classLineage_of_tablesEq (fun _ => ⟨rfl, rfl, rfl⟩)
                          (classLineage_of_tablesEq (fun _ => ⟨rfl, rfl, rfl⟩) hclb)
                      · simp only [hdon, if_false]
                        exact classLineage_of_tablesEq (quiet_haltDom σ _ _).1 hcl
            · simp only [hbud, if_false]
              cases hserv : (σ.doms d).serving with
              | some g =>
                  simp only [hserv]
                  exact classLineage_of_tablesEq (quiet_haltDom σ _ _).1 hcl
              | none =>
                  simp only [hserv]
                  exact classLineage_of_tablesEq
                    (quiet_setDom σ (σ.payer d)
                      (fun ds => { ds with budget := 0 }) ⟨rfl, rfl, rfl⟩).1 hcl

theorem step_cl (m : Manifest) (σ : MachineState)
    (hwf : Wf σ) (hac : Acyclic σ) (hcl : ClassLineage σ) :
    ClassLineage (step m σ) := by
  unfold step
  have hclr : ClassLineage (refillPhase m σ) :=
    classLineage_of_tablesEq
      (fun d => ⟨refillPhase_caps m σ d, refillPhase_lineage m σ d, refillPhase_slotGen m σ d⟩)
      hcl
  have hclc : ClassLineage (corePhase m (refillPhase m σ)) :=
    corePhase_cl m _ (refillPhase_preserves_wf m σ hwf) (acyclic_refillPhase m σ hac) hclr
  exact classLineage_of_tablesEq (fun _ => ⟨rfl, rfl, rfl⟩)
    (classLineage_of_tablesEq (fun d => by rw [moverPhase_doms]; exact ⟨rfl, rfl, rfl⟩) hclc)

/-- Boot states have no derived capabilities: `ClassLineage` holds vacuously. -/
theorem init_cl (m : Manifest) : ClassLineage m.initState := by
  intro d s e p ep hce hpar hlive
  exfalso
  obtain ⟨e', l, cell, hce', hl, _, _⟩ := (parentOf_some_iff _ d s p).mp hpar
  have : (m.initState.doms d).caps s = ((m.doms d).initCaps s).map
      (fun k => { kind := k, lineage := none }) := rfl
  rw [this] at hce'
  cases hic : (m.doms d).initCaps s with
  | none => rw [hic] at hce'; exact absurd hce' (by simp)
  | some k =>
      rw [hic] at hce'
      injection hce' with hce'; subst hce'
      exact absurd hl (by simp)

/-- **The class-lineage machine invariant**: every reachable state is
well-formed, acyclic, and class-uniform along lineage chains. -/
theorem wfacl_invariant (m : Manifest) (hwfm : m.WF) :
    (machine m).Invariant (fun σ => Wf σ ∧ Acyclic σ ∧ ClassLineage σ) := by
  have hexec := execPreservesWfA_of_system Machines.Lnp64u.Isa.Wip.system_preserves_wfa
  exact Loom.TSys.Inductive.invariant
    { init := fun σ hi =>
        ⟨hi ▸ Machines.Lnp64u.Theorems.Inv.init_wf m hwfm, hi ▸ init_acyclic m,
         hi ▸ init_cl m⟩
      step := fun σ σ2 hP hstep => by
        have hst : step m σ = σ2 := hstep
        obtain ⟨h1, h2⟩ := step_wfa hexec m hwfm σ hP.1 hP.2.1
        exact hst ▸ ⟨h1, h2, step_cl m σ hP.1 hP.2.1 hP.2.2⟩ }


/-! ## Marking facts -/

/-- Marked slots are occupied (marking requires a parent pointer). -/
theorem marked_occupied (σ : MachineState) (root : CapRef) (d' : DomainId) (s' : Slot)
    (h : σ.marks root d' s' = true) : ∃ e', (σ.doms d').caps s' = some e' := by
  rw [marks_eq_iter] at h
  revert h
  generalize numDomains * numSlots = k
  induction k with
  | zero => intro h; simp [MachineState.iterMark, Nat.fold] at h
  | succ n ih =>
      intro h
      rw [iterMark_succ] at h
      unfold MachineState.markStep at h
      rcases (Bool.or_eq_true _ _).mp h with h1 | h2
      · exact ih h1
      · cases hp : σ.parentOf d' s' with
        | none => rw [hp] at h2; simp at h2
        | some p =>
            obtain ⟨e, l, cell, hce, _, _, _⟩ := (parentOf_some_iff σ d' s' p).mp hp
            exact ⟨e, hce⟩

/-- Every marked descendant carries the root's class (`ClassLineage`
composed along the marking chain). -/
theorem marked_cls (σ : MachineState) (hwf : Wf σ) (hcl : ClassLineage σ)
    (root : CapRef) (eroot : CapEntry)
    (hrootlive : (σ.doms root.dom).liveCap root.slot root.gen = some eroot)
    (d' : DomainId) (s' : Slot) (h : σ.marks root d' s' = true) :
    ∃ e', (σ.doms d').caps s' = some e' ∧ e'.kind.cls = eroot.kind.cls := by
  rw [marks_eq_iter] at h
  revert d' s' h
  generalize numDomains * numSlots = k
  induction k with
  | zero => intro d' s' h; simp [MachineState.iterMark, Nat.fold] at h
  | succ n ih =>
      intro d' s' h
      rw [iterMark_succ] at h
      unfold MachineState.markStep at h
      rcases (Bool.or_eq_true _ _).mp h with h1 | h2
      · exact ih d' s' h1
      · cases hp : σ.parentOf d' s' with
        | none => rw [hp] at h2; simp at h2
        | some p =>
            rw [hp] at h2
            obtain ⟨e, l, cell, hce, hl, hcell, hcp⟩ := (parentOf_some_iff σ d' s' p).mp hp
            rcases (Bool.or_eq_true _ _).mp h2 with hroot | hpm
            · have hpr : p = root := by simpa using hroot
              subst hpr
              exact ⟨e, hce, hcl d' s' e p eroot hce hp hrootlive⟩
            · rcases (Bool.and_eq_true _ _).mp hpm with ⟨hg, hm⟩
              obtain ⟨ep, hcep, hclsp⟩ := ih p.dom p.slot hm
              have hglive : (σ.doms p.dom).slotGen p.slot = p.gen :=
                (of_decide_eq_true hg).symm
              have hlivep : (σ.doms p.dom).liveCap p.slot p.gen = some ep := by
                rw [liveCap_eq_some]
                refine ⟨hcep, hglive, ?_⟩
                rw [← hglive]
                exact gen_ne_zero_of_pos ((hwf.doms p.dom).gen_pos p.slot)
              exact ⟨e, hce, (hcl d' s' e p ep hce hp hlivep).trans hclsp⟩

/-- Marking only reads the capability tables. -/
theorem marks_congr (σ σ' : MachineState) (ht : TablesEq σ σ') (root : CapRef) :
    σ'.marks root = σ.marks root := by
  have hstep : ∀ mfun, σ'.markStep root mfun = σ.markStep root mfun := by
    intro mfun
    funext d s
    unfold MachineState.markStep
    rw [parentOf_congr σ σ' ht]
    cases σ.parentOf d s with
    | none => rfl
    | some p =>
        simp only []
        rw [(ht p.dom).2.2]
  have hiter : ∀ k, σ'.iterMark root k = σ.iterMark root k := by
    intro k
    induction k with
    | zero => rfl
    | succ n ih => rw [iterMark_succ, iterMark_succ, ih, hstep]
  rw [marks_eq_iter, marks_eq_iter, hiter]

/-! ## Forward evaluation of `capLive` -/

theorem capLive_eval_ok (d : DomainId) (w : Loom.Word32) (σ : MachineState) (e : CapEntry)
    (hlc : (σ.doms d).liveCap (Handle.decode w).slot (Handle.decode w).gen = some e)
    (hcls : (Handle.decode w).cls = e.kind.cls) :
    Machines.Lnp64u.Isa.capLive d w σ =
      .ok ((Handle.decode w).slot, (Handle.decode w).gen, e) σ := by
  have hred : Machines.Lnp64u.Isa.capLive d w σ =
      (match (σ.doms d).liveCap (Handle.decode w).slot (Handle.decode w).gen with
        | none => SpecM.raise .staleHandle
        | some e => (SpecM.require ((Handle.decode w).cls = e.kind.cls) .badCap >>=
            fun _ => (Pure.pure ((Handle.decode w).slot, (Handle.decode w).gen, e) :
              SpecM _))) σ := rfl
  rw [hred, hlc]
  simp [SpecM.require, hcls]

theorem capLive_eval_err (d : DomainId) (w : Loom.Word32) (σ : MachineState) (e : CapEntry)
    (hlc : (σ.doms d).liveCap (Handle.decode w).slot (Handle.decode w).gen = some e)
    (hcls : ¬ ((Handle.decode w).cls = e.kind.cls)) :
    Machines.Lnp64u.Isa.capLive d w σ = .err .badCap σ := by
  have hred : Machines.Lnp64u.Isa.capLive d w σ =
      (match (σ.doms d).liveCap (Handle.decode w).slot (Handle.decode w).gen with
        | none => SpecM.raise .staleHandle
        | some e => (SpecM.require ((Handle.decode w).cls = e.kind.cls) .badCap >>=
            fun _ => (Pure.pure ((Handle.decode w).slot, (Handle.decode w).gen, e) :
              SpecM _))) σ := rfl
  rw [hred, hlc]
  simp [SpecM.require, hcls, SpecM.raise]

/-! ## `cap_revoke` identification by mnemonic -/

/-- The only ISA instruction with mnemonic `cap_revoke` carries the revoke
semantics. -/
theorem caprevoke_exec_of_mnemonic (i : Instr) (hmem : i ∈ isa)
    (hrev : i.mnemonic = "cap_revoke") :
    i.sem.exec = fun c => (do
      let hw ← SpecM.reg c.d c.op.rs1
      let (s, g, e) ← Machines.Lnp64u.Isa.capLive c.d hw
      SpecM.require (e.kind.cls = .mem) .badCap
      let σ ← SpecM.get
      let mm := σ.marks ⟨c.d, s, g⟩
      SpecM.set (((σ.destroyMarked mm).sweepRegions).sweepMover)
      SpecM.setReg c.d c.op.rd 0) := by
  have hmem' : i ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
    have hiseq : Machines.Lnp64u.isa =
      (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray := rfl
    rw [hiseq, Array.mem_toArray] at hmem; exact hmem
  fin_cases hmem' <;>
    first
      | rfl
      | (exfalso; revert hrev;
         simp [Machines.Lnp64u.Isa.rrr, Machines.Lnp64u.Isa.branch])


/-! ## The revoke retirement: exact effect on marked slots -/

@[simp] theorem refillPhase_inflight (m : Manifest) (σ : MachineState) :
    (refillPhase m σ).inflight = σ.inflight := by
  rfl

theorem refillPhase_regs (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).regs = (σ.doms d).regs := by
  unfold refillPhase
  dsimp only
  by_cases h : σ.cycle.toNat % (m.doms d).periodP = 0 <;> simp [h]

theorem reg_congr {ds ds' : DomainState} (h : ds'.regs = ds.regs) : ds'.reg = ds.reg := by
  funext r; unfold DomainState.reg; rw [h]

/-- When `cap_revoke` retires on a live memory handle, the step destroys
exactly the marked slots: entry cleared, generation bumped. -/
theorem revoke_step_projections (m : Manifest) (σ : MachineState)
    (fl : InFlight) (hfl : σ.inflight = some fl) (hlast : fl.cyclesLeft ≤ 1)
    (i : Instr) (hdec : Loom.Isa.decode isa fl.word = some i)
    (hrev : i.mnemonic = "cap_revoke")
    (s : Slot) (g : Gen) (e : CapEntry)
    (hlive : (σ.doms fl.dom).liveCap s g = some e)
    (hhandle : Handle.decode ((σ.doms fl.dom).reg (operandsOf fl.word).rs1)
               = ⟨s, g, .mem⟩)
    (hcls : e.kind.cls = .mem) :
    ∀ d' s', σ.marks ⟨fl.dom, s, g⟩ d' s' = true →
      ((step m σ).doms d').caps s' = none ∧
      ((step m σ).doms d').slotGen s' = bumpGen ((σ.doms d').slotGen s') := by
  -- the retire-time state: refill, in-flight cleared, pc bumped
  have ht1 : TablesEq σ
      (({ refillPhase m σ with inflight := none }).setDom fl.dom
        (fun ds => { ds with pc := ds.pc + 1 })) := by
    refine TablesEq.trans (σ₂ := { refillPhase m σ with inflight := none }) ?_ ?_
    · intro d
      exact ⟨refillPhase_caps m σ d, refillPhase_lineage m σ d, refillPhase_slotGen m σ d⟩
    · exact (quiet_setDom _ fl.dom _ ⟨rfl, rfl, rfl⟩).1
  have hregs1 : ((({ refillPhase m σ with inflight := none }).setDom fl.dom
      (fun ds => { ds with pc := ds.pc + 1 })).doms fl.dom).reg = (σ.doms fl.dom).reg := by
    refine reg_congr ?_
    have h1 : ((({ refillPhase m σ with inflight := none }).setDom fl.dom
        (fun ds => { ds with pc := ds.pc + 1 })).doms fl.dom).regs
        = ((refillPhase m σ).doms fl.dom).regs := by
      unfold MachineState.setDom
      simp [Loom.Fun.update_same]
    rw [h1, refillPhase_regs]
  set σ1 := (({ refillPhase m σ with inflight := none }).setDom fl.dom
    (fun ds => { ds with pc := ds.pc + 1 })) with hσ1def
  have hlive1 : (σ1.doms fl.dom).liveCap s g = some e := by
    rw [liveCap_congr_of_eq _ _ (ht1 fl.dom).1 (ht1 fl.dom).2.2]
    exact hlive
  have hdec_s : (Handle.decode ((σ.doms fl.dom).reg (operandsOf fl.word).rs1)).slot = s := by
    rw [hhandle]
  have hdec_g : (Handle.decode ((σ.doms fl.dom).reg (operandsOf fl.word).rs1)).gen = g := by
    rw [hhandle]
  have hdec_c : (Handle.decode ((σ.doms fl.dom).reg (operandsOf fl.word).rs1)).cls
      = .mem := by rw [hhandle]
  have hcap : Machines.Lnp64u.Isa.capLive fl.dom
      ((σ.doms fl.dom).reg (operandsOf fl.word).rs1) σ1 = .ok (s, g, e) σ1 := by
    have h := capLive_eval_ok fl.dom ((σ.doms fl.dom).reg (operandsOf fl.word).rs1) σ1 e
      (by rw [hdec_s, hdec_g]; exact hlive1) (by rw [hdec_c, hcls])
    rw [hdec_s, hdec_g] at h
    exact h
  have hexec : i.sem.exec
      { d := fl.dom, pc := (({ refillPhase m σ with inflight := none }).doms fl.dom).pc,
        op := operandsOf fl.word } σ1
      = .ok () ((((σ1.destroyMarked (σ1.marks ⟨fl.dom, s, g⟩)).sweepRegions).sweepMover).setDom
          fl.dom (fun ds => ds.setReg (operandsOf fl.word).rd 0)) := by
    rw [caprevoke_exec_of_mnemonic i (Loom.Isa.decode_mem isa hdec) hrev]
    show (SpecM.reg fl.dom (operandsOf fl.word).rs1 >>= fun hw =>
      Machines.Lnp64u.Isa.capLive fl.dom hw >>= fun r =>
        (match r with
          | (s, g, e) =>
              SpecM.require (e.kind.cls = .mem) .badCap >>= fun _ =>
              SpecM.get >>= fun σ0 =>
              SpecM.set (((σ0.destroyMarked (σ0.marks ⟨fl.dom, s, g⟩)).sweepRegions).sweepMover)
                >>= fun _ =>
              SpecM.setReg fl.dom (operandsOf fl.word).rd 0)) σ1 = _
    simp only [specM_bind, SpecM.reg]
    rw [hregs1, hcap]
    simp only []
    rw [show SpecM.require (e.kind.cls = .mem) .badCap σ1 = .ok () σ1 from by
      simp [SpecM.require, hcls]]
    simp only [specM_bind, SpecM.get, SpecM.set, SpecM.setReg, SpecM.modify]
  have hcore : corePhase m (refillPhase m σ)
      = ((((σ1.destroyMarked (σ1.marks ⟨fl.dom, s, g⟩)).sweepRegions).sweepMover).setDom
          fl.dom (fun ds => ds.setReg (operandsOf fl.word).rd 0)) := by
    unfold corePhase
    rw [show (refillPhase m σ).inflight = some fl from by
      rw [refillPhase_inflight]; exact hfl]
    simp only [hlast, if_true]
    unfold retire
    rw [hdec]
    simp only []
    rw [hexec]
  have hstepdoms : (step m σ).doms
      = (((((σ1.destroyMarked (σ1.marks ⟨fl.dom, s, g⟩)).sweepRegions).sweepMover).setDom
          fl.dom (fun ds => ds.setReg (operandsOf fl.word).rd 0)).doms) := by
    have h0 : (step m σ).doms = (moverPhase (corePhase m (refillPhase m σ))).doms := rfl
    rw [h0, moverPhase_doms, hcore]
  have hsd : TablesEq ((((σ1.destroyMarked (σ1.marks ⟨fl.dom, s, g⟩)).sweepRegions).sweepMover))
      (((((σ1.destroyMarked (σ1.marks ⟨fl.dom, s, g⟩)).sweepRegions).sweepMover).setDom
          fl.dom (fun ds => ds.setReg (operandsOf fl.word).rd 0))) :=
    (quiet_setDom _ fl.dom _
      ⟨setReg_caps _ _ _, setReg_lineage _ _ _, setReg_slotGen _ _ _⟩).1
  intro d' s' hmark
  have hM1 : σ1.marks ⟨fl.dom, s, g⟩ d' s' = true := by
    rw [marks_congr σ σ1 ht1]
    exact hmark
  obtain ⟨e'', hocc⟩ := marked_occupied σ ⟨fl.dom, s, g⟩ d' s' hmark
  have hocc1 : ((σ1.doms d').caps s').isSome = true := by
    rw [(ht1 d').1, hocc]; rfl
  constructor
  · rw [hstepdoms, (hsd d').1, sweepMover_doms, sweepRegions_caps, destroyMarked_caps,
      if_pos hM1]
  · rw [hstepdoms, (hsd d').2.2, sweepMover_doms]
    rw [show (((σ1.destroyMarked (σ1.marks ⟨fl.dom, s, g⟩)).sweepRegions).doms d').slotGen s'
        = ((σ1.destroyMarked (σ1.marks ⟨fl.dom, s, g⟩)).doms d').slotGen s' from by
      rw [sweepRegions_slotGen]]
    rw [destroyMarked_slotGen]
    rw [show (σ1.marks ⟨fl.dom, s, g⟩ d' s' && ((σ1.doms d').caps s').isSome) = true from by
      rw [hM1, hocc1]; rfl]
    rw [if_pos rfl, (ht1 d').2.2]

end Machines.Lnp64u
