-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Logic.ExecWf
import Mathlib.Tactic.FinCases
import Machines.Lnp64u.Logic.SystemOpsWf

/-!
# Slot-generation monotonicity (T3 support)

Slot generations never decrease under any instruction: the only writes to
`slotGen` are in `clearSlot` and `destroyMarked`, both via `bumpGen`, which
never lowers a generation. `SlotGenLe` is the `SpecM`-level combinator (mirroring
`PreservesAcyclic`) that carries this monotonicity through the exec semantics;
`gen_monotone` lifts it to the whole `step` (the other phases leave `slotGen`
untouched).
-/

namespace Machines.Lnp64u

open Loom.Isa SpecM Machines.Lnp64u.Isa

/-- A `SpecM` computation never lowers any slot generation. -/
def SlotGenLe {α : Type} (m : SpecM α) : Prop :=
  ∀ σ, (∀ a σ', m σ = .ok a σ' →
          ∀ d s, ((σ.doms d).slotGen s).toNat ≤ ((σ'.doms d).slotGen s).toNat) ∧
       (∀ e σ', m σ = .err e σ' →
          ∀ d s, ((σ.doms d).slotGen s).toNat ≤ ((σ'.doms d).slotGen s).toNat)

/-- A computation that leaves `slotGen` untouched on every outcome is monotone. -/
theorem SlotGenLe.of_preservesGen {α : Type} (m : SpecM α)
    (hok : ∀ σ a σ', m σ = .ok a σ' → ∀ d s, (σ'.doms d).slotGen s = (σ.doms d).slotGen s)
    (herr : ∀ σ e σ', m σ = .err e σ' → ∀ d s, (σ'.doms d).slotGen s = (σ.doms d).slotGen s) :
    SlotGenLe m :=
  fun σ => ⟨fun a σ' he d s => by rw [hok σ a σ' he d s],
            fun e σ' he d s => by rw [herr σ e σ' he d s]⟩

theorem SlotGenLe.pure {α : Type} (a : α) : SlotGenLe (Pure.pure a : SpecM α) :=
  SlotGenLe.of_preservesGen _
    (fun σ a' σ' he d s => by rw [specM_pure] at he; injection he with _ h2; subst h2; rfl)
    (fun σ e σ' he d s => by rw [specM_pure] at he; simp at he)

theorem SlotGenLe.bind {α β : Type} {m : SpecM α} {f : α → SpecM β}
    (hm : SlotGenLe m) (hf : ∀ a, SlotGenLe (f a)) : SlotGenLe (m >>= f) := by
  intro σ
  refine ⟨?_, ?_⟩
  · intro b σ' he d s
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he
                 exact le_trans ((hm σ).1 a σ1 hmσ d s) ((hf a σ1).1 b σ' he d s)
    | err e σ1 => rw [hmσ] at he; simp at he
    | fault g => rw [hmσ] at he; simp at he
  · intro e σ' he d s
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he
                 exact le_trans ((hm σ).1 a σ1 hmσ d s) ((hf a σ1).2 e σ' he d s)
    | err e1 σ1 => rw [hmσ] at he; injection he with h1 h2; subst h2; exact (hm σ).2 e1 σ1 hmσ d s
    | fault g => rw [hmσ] at he; simp at he

theorem SlotGenLe.iteBool {α : Type} (b : Bool) {m1 m2 : SpecM α}
    (h1 : SlotGenLe m1) (h2 : SlotGenLe m2) : SlotGenLe (if b then m1 else m2) := by
  cases b <;> simp only [Bool.false_eq_true, if_true, if_false]
  · exact h2
  · exact h1

theorem SlotGenLe.reg (d : DomainId) (r : RegId) : SlotGenLe (SpecM.reg d r) :=
  SlotGenLe.of_preservesGen _
    (fun σ a σ' he d s => by unfold SpecM.reg at he; injection he with _ h2; subst h2; rfl)
    (fun σ e σ' he d s => by unfold SpecM.reg at he; simp at he)

theorem SlotGenLe.raise {α : Type} (e : Errno) : SlotGenLe (SpecM.raise e : SpecM α) :=
  SlotGenLe.of_preservesGen _
    (fun σ a σ' he d s => by unfold SpecM.raise at he; simp at he)
    (fun σ e' σ' he d s => by unfold SpecM.raise at he; injection he with _ h2; subst h2; rfl)

theorem SlotGenLe.require (cond : Bool) (e : Errno) : SlotGenLe (SpecM.require cond e) :=
  SlotGenLe.of_preservesGen _
    (fun σ a σ' he d s => by rw [require_ok cond e σ he])
    (fun σ e' σ' he d s => by rw [require_err_state cond e σ he])

theorem SlotGenLe.load (d : DomainId) (a : Addr) : SlotGenLe (SpecM.load d a) :=
  SlotGenLe.of_preservesGen _
    (fun σ v σ' he d' s => by rw [load_ok d a σ he])
    (fun σ e σ' he d' s => by rw [load_err_state d a σ he])

theorem SlotGenLe.setReg (d : DomainId) (r : RegId) (v : Loom.Word32) :
    SlotGenLe (SpecM.setReg d r v) :=
  SlotGenLe.of_preservesGen _
    (fun σ a σ' he d' s => by
      unfold SpecM.setReg SpecM.modify at he; injection he with _ h2; subst h2
      unfold MachineState.setDom
      by_cases h : d' = d
      · subst h; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ h])
    (fun σ e σ' he d' s => by unfold SpecM.setReg SpecM.modify at he; simp at he)

theorem SlotGenLe.updDomPc (d : DomainId) (k : DomainState → Addr) :
    SlotGenLe (SpecM.updDom d (fun ds => { ds with pc := k ds })) := by
  intro σ; refine ⟨?_, ?_⟩
  · intro a σ' he d' s
    simp only [SpecM.updDom, SpecM.modify] at he; injection he with _ h2; subst h2
    unfold MachineState.setDom
    by_cases h : d' = d
    · subst h; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ h]
  · intro e σ' he d' s; simp [SpecM.updDom, SpecM.modify] at he

theorem SlotGenLe.store (d : DomainId) (a : Addr) (v : Loom.Word32) :
    SlotGenLe (SpecM.store d a v) := by
  intro σ; unfold SpecM.store; refine ⟨?_, ?_⟩
  · intro x σ' he d' s
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp only [SpecM.demand, hc, if_true, specM_pure, specM_bind, SpecM.set] at he
      injection he with _ h2; subst h2
      show ((σ.doms d').slotGen s).toNat ≤ (((σ.write a v).doms d').slotGen s).toNat
      rw [show (σ.write a v).doms = σ.doms from rfl]
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he
  · intro e σ' he d' s
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp [SpecM.demand, hc, specM_pure, specM_bind, SpecM.set] at he
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he

/-- **The base opcodes never lower a slot generation.** Their `exec` only
touches regs/pc/memory, never `slotGen`. -/
theorem base_slotGen_le : ∀ instr ∈ base, ∀ c : Ctx, SlotGenLe (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  · exact SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.setReg _ _ _))
  · exact SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.setReg _ _ _))
  · exact SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.setReg _ _ _))
  · exact SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.setReg _ _ _))
  · exact SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.setReg _ _ _))
  · exact SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.setReg _ _ _))
  · exact SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.setReg _ _ _))
  · exact SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.setReg _ _ _)
  · exact SlotGenLe.setReg _ _ _
  · exact SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.bind (SlotGenLe.load _ _) (fun _ => SlotGenLe.setReg _ _ _))
  · exact SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.store _ _ _))
  · exact SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.iteBool _ (SlotGenLe.updDomPc _ _) (SlotGenLe.pure ())))
  · exact SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.bind (SlotGenLe.reg _ _) (fun _ => SlotGenLe.iteBool _ (SlotGenLe.updDomPc _ _) (SlotGenLe.pure ())))
  · exact SlotGenLe.bind (SlotGenLe.reg _ _)
      (fun _ => SlotGenLe.bind (SlotGenLe.setReg _ _ _) (fun _ => SlotGenLe.updDomPc _ _))

/-! ### Kernel-level slot-generation bounds -/

theorem clearSlot_slotGen_ge (σ : MachineState) (d : DomainId) (s : Slot) (d' : DomainId) (s' : Slot) :
    ((σ.doms d').slotGen s').toNat ≤ (((σ.clearSlot d s).doms d').slotGen s').toNat := by
  rw [clearSlot_slotGen]; split
  · rename_i h; obtain ⟨hd, hs⟩ := h; subst hd; subst hs; exact bumpGen_ge _
  · exact le_refl _

theorem destroyMarked_slotGen_ge (σ : MachineState) (m : DomainId → Slot → Bool) (d : DomainId) (s : Slot) :
    ((σ.doms d).slotGen s).toNat ≤ (((σ.destroyMarked m).doms d).slotGen s).toNat := by
  rw [destroyMarked_slotGen]; split
  · exact bumpGen_ge _
  · exact le_refl _

@[simp] theorem sweepRegions_slotGen' (σ : MachineState) (d : DomainId) (s : Slot) :
    ((σ.sweepRegions.doms d).slotGen s) = (σ.doms d).slotGen s := by rw [sweepRegions_slotGen]

theorem SlotGenLe.capLive (d : DomainId) (hw : Loom.Word32) :
    SlotGenLe (Machines.Lnp64u.Isa.capLive d hw) :=
  SlotGenLe.of_preservesGen _
    (fun σ r σ' he d' s => by rw [(Machines.Lnp64u.Isa.Wip.capLive_ok d hw σ he).1])
    (fun σ e σ' he d' s => by rw [Machines.Lnp64u.Isa.Wip.capLive_err_state d hw σ he])

/-- A `updDom` whose update leaves `slotGen` alone is slot-gen monotone. -/
theorem SlotGenLe.updDomGen (d : DomainId) (f : DomainState → DomainState)
    (hf : ∀ ds, (f ds).slotGen = ds.slotGen) : SlotGenLe (SpecM.updDom d f) := by
  intro σ; refine ⟨?_, ?_⟩
  · intro a σ' he d' s
    simp only [SpecM.updDom, SpecM.modify] at he; injection he with _ h2; subst h2
    unfold MachineState.setDom
    by_cases h : d' = d
    · subst h; simp [Loom.Fun.update_same, hf]
    · simp [Loom.Fun.update_ne _ _ _ _ h]
  · intro e σ' he d' s; simp [SpecM.updDom, SpecM.modify] at he

theorem haltDom_slotGen (σ : MachineState) (d : DomainId) (c : Loom.Word32) (d' : DomainId) (s : Slot) :
    ((σ.haltDom d c).doms d').slotGen s = (σ.doms d').slotGen s := by
  unfold MachineState.haltDom
  split
  · rw [haltBase_slotGen]
  · split
    · rw [haltBase_slotGen]
    · rw [unwindGate_slotGen, haltBase_slotGen]

/-- `halt`'s exec never lowers a slot generation (`haltDom` touches run/serving/gates). -/
theorem SlotGenLe.halt (c : Ctx) :
    SlotGenLe (SpecM.modify (fun σ => σ.haltDom c.d 0)) :=
  SlotGenLe.of_preservesGen _
    (fun σ a σ' he d s => by
      simp only [SpecM.modify, SpecM.set] at he; injection he with _ h2; subst h2
      exact haltDom_slotGen σ c.d 0 d s)
    (fun σ e σ' he d s => by simp [SpecM.modify, SpecM.set] at he)

/-- `yield`'s exec never lowers a slot generation. -/
theorem SlotGenLe.yield (c : Ctx) :
    SlotGenLe (SpecM.updDom c.d (fun ds => { ds with budget := 0 }) >>=
      fun _ => SpecM.setReg c.d c.op.rd 0) :=
  SlotGenLe.bind (SlotGenLe.updDomGen _ _ (fun ds => rfl)) (fun _ => SlotGenLe.setReg _ _ _)

theorem installDerived_slotGen (σ : MachineState) (d : DomainId) (s : Slot) (l : LineageId)
    (kind : CapKind) (parent : CapRef) (d' : DomainId) (s' : Slot) :
    (((σ.installDerived d s l kind parent).1).doms d').slotGen s' = (σ.doms d').slotGen s' := by
  unfold MachineState.installDerived MachineState.setDom
  by_cases hd : d' = d
  · subst hd; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd]

theorem SlotGenLe.allocDerived (owner : DomainId) (kind : CapKind) (parent : CapRef) :
    SlotGenLe (Machines.Lnp64u.Isa.allocDerived owner kind parent) := by
  intro σ; refine ⟨?_, ?_⟩
  · intro hw σ' he d' s
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
            rw [show σ' = (σ.installDerived owner sl lc kind parent).1 from by rw [← h2]]
            rw [installDerived_slotGen]
  · intro e σ' he d' s
    unfold Machines.Lnp64u.Isa.allocDerived at he
    simp only [SpecM.get, specM_bind] at he
    cases hfs : σ.freeSlot owner with
    | none => rw [hfs] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact le_refl _
    | some sl =>
        rw [hfs] at he
        cases hfc : σ.freeCell owner with
        | none => rw [hfc] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact le_refl _
        | some lc => rw [hfc] at he; simp [SpecM.set, specM_bind, specM_pure] at he

/-- `unmap`'s exec never lowers a slot generation (only clears a region register). -/
theorem SlotGenLe.unmap (c : Ctx) (ri : RegionId) :
    SlotGenLe (SpecM.updDom c.d (fun ds => { ds with regions := Loom.Fun.update ds.regions ri none }) >>=
      fun _ => SpecM.setReg c.d c.op.rd 0) :=
  SlotGenLe.bind (SlotGenLe.updDomGen _ _ (fun ds => rfl)) (fun _ => SlotGenLe.setReg _ _ _)

/-- The `map` region-install update never lowers a slot generation. -/
theorem SlotGenLe.mapUpd (c : Ctx) (ri : RegionId) (rgn : Region) :
    SlotGenLe (SpecM.updDom c.d (fun ds => { ds with regions := Loom.Fun.update ds.regions ri (some rgn) }) >>=
      fun _ => SpecM.setReg c.d c.op.rd 0) :=
  SlotGenLe.bind (SlotGenLe.updDomGen _ _ (fun ds => rfl)) (fun _ => SlotGenLe.setReg _ _ _)

@[simp] theorem reparent_slotGen (σ : MachineState) (old new : CapRef) (d : DomainId) (s : Slot) :
    ((σ.reparent old new).doms d).slotGen s = (σ.doms d).slotGen s := rfl

@[simp] theorem sweepMover_slotGen (σ : MachineState) (d : DomainId) (s : Slot) :
    ((σ.sweepMover.doms d).slotGen s) = (σ.doms d).slotGen s := by rw [sweepMover_doms]

/-- The `cap_drop` kernel core (reparent/orphan + clearSlot + sweeps) never lowers a
slot generation: `clearSlot` bumps the dropped slot, everything else preserves. -/
theorem clearSlot_sweeps_slotGen_ge (σ : MachineState) (d : DomainId) (s : Slot)
    (d' : DomainId) (s' : Slot) :
    ((σ.doms d').slotGen s').toNat ≤
      (((((σ.clearSlot d s).sweepRegions).sweepMover).doms d').slotGen s').toNat := by
  rw [sweepMover_slotGen, sweepRegions_slotGen']
  exact clearSlot_slotGen_ge σ d s d' s'

/-- The `cap_revoke` kernel core (destroyMarked + sweeps) never lowers a slot generation. -/
theorem destroyMarked_sweeps_slotGen_ge (σ : MachineState) (m : DomainId → Slot → Bool)
    (d : DomainId) (s : Slot) :
    ((σ.doms d).slotGen s).toNat ≤
      (((((σ.destroyMarked m).sweepRegions).sweepMover).doms d).slotGen s).toNat := by
  rw [sweepMover_slotGen, sweepRegions_slotGen']
  exact destroyMarked_slotGen_ge σ m d s

@[simp] theorem moverPhase_slotGen (σ : MachineState) (d : DomainId) (s : Slot) :
    ((moverPhase σ).doms d).slotGen s = (σ.doms d).slotGen s := by rw [moverPhase_doms]

/-- `step`'s slot generations equal `corePhase`'s (refill and the cycle bump leave
`slotGen` untouched; `moverPhase` leaves all domains untouched). -/
theorem step_slotGen_reduce (m : Manifest) (σ : MachineState) (d : DomainId) (s : Slot) :
    ((step m σ).doms d).slotGen s = ((corePhase m (refillPhase m σ)).doms d).slotGen s := by
  unfold step; simp only [moverPhase_slotGen]

theorem SlotGenLe.narrow (base : Addr) (len : BitVec 13) (perms : Perms) (dw : Loom.Word32) :
    SlotGenLe (Machines.Lnp64u.Isa.narrow base len perms dw) :=
  SlotGenLe.of_preservesGen _
    (fun σ k σ' he d s => by rw [(Machines.Lnp64u.Isa.Wip.narrow_ok base len perms dw σ he).1])
    (fun σ e σ' he d s => by rw [Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms dw σ he])

theorem SlotGenLe.demand (cond : Bool) (f : Fault) : SlotGenLe (SpecM.demand cond f) :=
  SlotGenLe.of_preservesGen _
    (fun σ a σ' he d s => by rw [demand_ok cond f σ he])
    (fun σ e σ' he d s => by
      unfold SpecM.demand at he; split at he
      · simp [specM_pure] at he
      · simp [SpecM.fatal] at he)

theorem SlotGenLe.get : SlotGenLe SpecM.get :=
  SlotGenLe.of_preservesGen _
    (fun σ a σ' he d s => by unfold SpecM.get at he; injection he with _ h2; subst h2; rfl)
    (fun σ e σ' he d s => by unfold SpecM.get at he; simp at he)

namespace Wip
open Machines.Lnp64u.Isa Machines.Lnp64u.Isa.Wip

/-- Helper: `setDom` with a `slotGen`-preserving update preserves `slotGen`. -/
theorem setDom_slotGen_of (σ : MachineState) (dd : DomainId) (f : DomainState → DomainState)
    (hf : (f (σ.doms dd)).slotGen = (σ.doms dd).slotGen) (d' : DomainId) (s' : Slot) :
    ((σ.setDom dd f).doms d').slotGen s' = (σ.doms d').slotGen s' := by
  unfold MachineState.setDom
  by_cases h : d' = dd
  · subst h; simp [Loom.Fun.update_same, hf]
  · simp [Loom.Fun.update_ne _ _ _ _ h]

/-- **`transferCap` never lowers a slot generation.** Install-at-recipient and
reparent preserve `slotGen`; `clearSlot` bumps the source slot; the sweeps
preserve. -/
theorem transferCap_slotGen_ge (σ : MachineState) (from_ : DomainId) (s : Slot) (to_ : DomainId)
    (τ : MachineState) (ref : CapRef) (h : σ.transferCap from_ s to_ = some (τ, ref))
    (d' : DomainId) (s' : Slot) :
    ((σ.doms d').slotGen s').toNat ≤ ((τ.doms d').slotGen s').toNat := by
  unfold MachineState.transferCap at h
  cases he : (σ.doms from_).caps s with
  | none => rw [he] at h; simp at h
  | some e =>
      rw [he] at h; simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hfs : σ.freeSlot to_ with
      | none => rw [hfs] at h; simp at h
      | some s2 =>
          rw [hfs] at h; simp only [Option.bind_some] at h
          have key : ∀ (σ₁ : MachineState), (∀ d s, (σ₁.doms d).slotGen s = (σ.doms d).slotGen s) →
              some (((((σ₁.reparent ⟨from_, s, (σ.doms from_).slotGen s⟩
                ⟨to_, s2, (σ.doms to_).slotGen s2⟩).clearSlot from_ s).sweepRegions).sweepMover),
                (⟨to_, s2, (σ.doms to_).slotGen s2⟩ : CapRef))
                = some (τ, ref) →
              ((σ.doms d').slotGen s').toNat ≤ ((τ.doms d').slotGen s').toNat := by
            intro σ₁ hpre heq
            injection heq with heq; injection heq with hτ _; subst hτ
            have h1 : (((σ₁.reparent ⟨from_, s, (σ.doms from_).slotGen s⟩
                ⟨to_, s2, (σ.doms to_).slotGen s2⟩).doms d').slotGen s') = (σ.doms d').slotGen s' := by
              rw [reparent_slotGen]; exact hpre d' s'
            rw [← h1]
            exact clearSlot_sweeps_slotGen_ge _ from_ s d' s'
          cases hl : e.lineage with
          | none =>
              rw [hl] at h; simp only [Option.pure_def, Option.bind_some] at h
              exact key (σ.setDom to_ (fun ds =>
                  { ds with caps := Loom.Fun.update ds.caps s2 (some { kind := e.kind, lineage := none }) }))
                (fun d ss => setDom_slotGen_of σ to_ _ rfl d ss) h
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
                      exact key (σ.setDom to_ (fun ds =>
                          { ds with
                            caps := Loom.Fun.update ds.caps s2 (some { kind := e.kind, lineage := some l' })
                            lineage := Loom.Fun.update ds.lineage l' (some cell) }))
                        (fun d ss => setDom_slotGen_of σ to_ _ rfl d ss) h

theorem move_slotGen_le (c : Ctx) : SlotGenLe (moveExec c) := by
  intro σ; refine ⟨fun x σ' he d' s => ?_, fun x σ' he d' s => ?_⟩
  ·
    simp only [moveExec, SpecM.get, specM_bind] at he
    cases hr0 : SpecM.require σ.mover.isNone .moverBusy σ with
    | err e0 σ0 => rw [hr0] at he; simp at he
    | fault f => rw [hr0] at he; simp at he
    | ok u0 σ0 =>
        have hh0 := require_ok _ _ σ hr0; subst σ0
        rw [hr0] at he; simp only [SpecM.reg] at he
        set B : Addr := ((σ.doms c.d).reg c.op.rs1).setWidth 12 with hB
        cases hl1 : load c.d B σ with
        | err e σe => rw [hl1] at he; simp at he
        | fault f => rw [hl1] at he; simp at he
        | ok srcH σ1 =>
            have hh1 := load_ok _ _ σ hl1; subst σ1; rw [hl1] at he; simp only [specM_bind] at he
            cases hl2 : load c.d (B + 1) σ with
            | err e σe => rw [hl2] at he; simp at he
            | fault f => rw [hl2] at he; simp at he
            | ok dstH σ2 =>
                have hh2 := load_ok _ _ σ hl2; subst σ2; rw [hl2] at he; simp only [specM_bind] at he
                cases hl3 : load c.d (B + 2) σ with
                | err e σe => rw [hl3] at he; simp at he
                | fault f => rw [hl3] at he; simp at he
                | ok lenW σ3 =>
                    have hh3 := load_ok _ _ σ hl3; subst σ3; rw [hl3] at he; simp only [specM_bind] at he
                    cases hl4 : load c.d (B + 3) σ with
                    | err e σe => rw [hl4] at he; simp at he
                    | fault f => rw [hl4] at he; simp at he
                    | ok stW σ4 =>
                        have hh4 := load_ok _ _ σ hl4; subst σ4; rw [hl4] at he; simp only [specM_bind] at he
                        cases hc1 : capLive c.d srcH σ with
                        | err e σe => rw [hc1] at he; simp at he
                        | fault f => rw [hc1] at he; simp at he
                        | ok rs σ5 =>
                            have hcs := capLive_ok c.d _ σ hc1; obtain ⟨hhs, hslive⟩ := hcs; subst σ5
                            rw [hc1] at he; obtain ⟨ss, gs_, es⟩ := rs; simp only at he hslive
                            cases hc2 : capLive c.d dstH σ with
                            | err e σe => rw [hc2] at he; simp at he
                            | fault f => rw [hc2] at he; simp at he
                            | ok rdd σ6 =>
                                have hcd := capLive_ok c.d _ σ hc2; obtain ⟨hhd, hdlive⟩ := hcd; subst σ6
                                rw [hc2] at he; obtain ⟨sd, gd, ed⟩ := rdd; simp only at he hdlive
                                cases hks : es.kind with
                                | gate _ => rw [hks] at he; cases hkd : ed.kind with
                                            | gate _ => rw [hkd] at he; simp [SpecM.raise] at he
                                            | mem _ _ _ => rw [hkd] at he; simp [SpecM.raise] at he
                                | mem sb sl sp =>
                                    cases hkd : ed.kind with
                                    | gate _ => rw [hks, hkd] at he; simp [SpecM.raise] at he
                                    | mem db dl dp =>
                                        rw [hks, hkd] at he; simp only [specM_bind] at he
                                        cases hq1 : SpecM.require sp.r .permDenied σ with
                                        | err e σe => rw [hq1] at he; simp at he
                                        | fault f => rw [hq1] at he; simp at he
                                        | ok _ σq1 =>
                                            have := require_ok _ _ σ hq1; subst σq1; rw [hq1] at he; simp only [specM_bind] at he
                                            cases hq2 : SpecM.require dp.w .permDenied σ with
                                            | err e σe => rw [hq2] at he; simp at he
                                            | fault f => rw [hq2] at he; simp at he
                                            | ok _ σq2 =>
                                                have := require_ok _ _ σ hq2; subst σq2; rw [hq2] at he; simp only [specM_bind] at he
                                                cases hq3 : SpecM.require (decide (lenW.toNat ≤ sl.toNat) && decide (lenW.toNat ≤ dl.toNat)) .outOfRange σ with
                                                | err e σe => rw [hq3] at he; simp at he
                                                | fault f => rw [hq3] at he; simp at he
                                                | ok _ σq3 =>
                                                    have := require_ok _ _ σ hq3; subst σq3; rw [hq3] at he; simp only [SpecM.get, specM_bind] at he
                                                    cases hd : SpecM.demand (σ.domCovers c.d (stW.setWidth 12) { r := false, w := true, x := false }) .memoryAuthority σ with
                                                    | err e σe => rw [hd] at he; simp at he
                                                    | fault f => rw [hd] at he; simp at he
                                                    | ok _ σdd =>
                                                        have := demand_ok _ _ σ hd; subst σdd; rw [hd] at he
                                                        simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
                                                        injection he with _ h2; subst h2
                                                        unfold MachineState.setDom
                                                        by_cases hdc : d' = c.d
                                                        · subst hdc; simp [Loom.Fun.update_same]
                                                        · simp [Loom.Fun.update_ne _ _ _ _ hdc]
  ·
    simp only [moveExec, SpecM.get, specM_bind] at he
    cases hr0 : SpecM.require σ.mover.isNone .moverBusy σ with
    | err e0 σ0 => have hq := require_err_state _ _ σ hr0; rw [hr0] at he; injection he with _ h2; subst h2; subst hq; exact le_refl _
    | fault f => rw [hr0] at he; simp at he
    | ok u0 σ0 =>
        have hh0 := require_ok _ _ σ hr0; subst σ0
        rw [hr0] at he; simp only [SpecM.reg] at he
        set B : Addr := ((σ.doms c.d).reg c.op.rs1).setWidth 12 with hB
        cases hl1 : load c.d B σ with
        | err e σe => have hq := load_err_state _ _ σ hl1; rw [hl1] at he; injection he with _ h2; subst h2; subst hq; exact le_refl _
        | fault f => rw [hl1] at he; simp at he
        | ok srcH σ1 =>
            have hh1 := load_ok _ _ σ hl1; subst σ1; rw [hl1] at he; simp only [specM_bind] at he
            cases hl2 : load c.d (B + 1) σ with
            | err e σe => have hq := load_err_state _ _ σ hl2; rw [hl2] at he; injection he with _ h2; subst h2; subst hq; exact le_refl _
            | fault f => rw [hl2] at he; simp at he
            | ok dstH σ2 =>
                have hh2 := load_ok _ _ σ hl2; subst σ2; rw [hl2] at he; simp only [specM_bind] at he
                cases hl3 : load c.d (B + 2) σ with
                | err e σe => have hq := load_err_state _ _ σ hl3; rw [hl3] at he; injection he with _ h2; subst h2; subst hq; exact le_refl _
                | fault f => rw [hl3] at he; simp at he
                | ok lenW σ3 =>
                    have hh3 := load_ok _ _ σ hl3; subst σ3; rw [hl3] at he; simp only [specM_bind] at he
                    cases hl4 : load c.d (B + 3) σ with
                    | err e σe => have hq := load_err_state _ _ σ hl4; rw [hl4] at he; injection he with _ h2; subst h2; subst hq; exact le_refl _
                    | fault f => rw [hl4] at he; simp at he
                    | ok stW σ4 =>
                        have hh4 := load_ok _ _ σ hl4; subst σ4; rw [hl4] at he; simp only [specM_bind] at he
                        cases hc1 : capLive c.d srcH σ with
                        | err e σe => have hq := capLive_err_state c.d _ σ hc1; rw [hc1] at he; injection he with _ h2; subst h2; subst hq; exact le_refl _
                        | fault f => rw [hc1] at he; simp at he
                        | ok rs σ5 =>
                            have hcs := capLive_ok c.d _ σ hc1; obtain ⟨hhs, hslive⟩ := hcs; subst σ5
                            rw [hc1] at he; obtain ⟨ss, gs_, es⟩ := rs; simp only at he hslive
                            cases hc2 : capLive c.d dstH σ with
                            | err e σe => have hq := capLive_err_state c.d _ σ hc2; rw [hc2] at he; injection he with _ h2; subst h2; subst hq; exact le_refl _
                            | fault f => rw [hc2] at he; simp at he
                            | ok rdd σ6 =>
                                have hcd := capLive_ok c.d _ σ hc2; obtain ⟨hhd, hdlive⟩ := hcd; subst σ6
                                rw [hc2] at he; obtain ⟨sd, gd, ed⟩ := rdd; simp only at he hdlive
                                cases hks : es.kind with
                                | gate _ => rw [hks] at he; cases hkd : ed.kind with
                                            | gate _ => rw [hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact le_refl _
                                            | mem _ _ _ => rw [hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact le_refl _
                                | mem sb sl sp =>
                                    cases hkd : ed.kind with
                                    | gate _ => rw [hks, hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact le_refl _
                                    | mem db dl dp =>
                                        rw [hks, hkd] at he; simp only [specM_bind] at he
                                        cases hq1 : SpecM.require sp.r .permDenied σ with
                                        | err e σe => have hq := require_err_state _ _ σ hq1; rw [hq1] at he; injection he with _ h2; subst h2; subst hq; exact le_refl _
                                        | fault f => rw [hq1] at he; simp at he
                                        | ok _ σq1 =>
                                            have := require_ok _ _ σ hq1; subst σq1; rw [hq1] at he; simp only [specM_bind] at he
                                            cases hq2 : SpecM.require dp.w .permDenied σ with
                                            | err e σe => have hq := require_err_state _ _ σ hq2; rw [hq2] at he; injection he with _ h2; subst h2; subst hq; exact le_refl _
                                            | fault f => rw [hq2] at he; simp at he
                                            | ok _ σq2 =>
                                                have := require_ok _ _ σ hq2; subst σq2; rw [hq2] at he; simp only [specM_bind] at he
                                                cases hq3 : SpecM.require (decide (lenW.toNat ≤ sl.toNat) && decide (lenW.toNat ≤ dl.toNat)) .outOfRange σ with
                                                | err e σe => have hq := require_err_state _ _ σ hq3; rw [hq3] at he; injection he with _ h2; subst h2; subst hq; exact le_refl _
                                                | fault f => rw [hq3] at he; simp at he
                                                | ok _ σq3 =>
                                                    have := require_ok _ _ σ hq3; subst σq3; rw [hq3] at he; simp only [SpecM.get, specM_bind] at he
                                                    cases hd : SpecM.demand (σ.domCovers c.d (stW.setWidth 12) { r := false, w := true, x := false }) .memoryAuthority σ with
                                                    | err e σe => exact absurd hd (by simp [SpecM.demand]; split <;> simp [SpecM.fatal])
                                                    | fault f => rw [hd] at he; simp at he
                                                    | ok _ σdd =>
                                                        have := demand_ok _ _ σ hd; subst σdd; rw [hd] at he
                                                        simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he

/-- `transferByHandle` never lowers a slot generation: the `hw = 0` and error
paths leave the state unchanged; the transfer path is `transferCap_slotGen_ge`. -/
theorem transferByHandle_slotGen_le (d to_ : DomainId) (hw : Loom.Word32) :
    SlotGenLe (transferByHandle d to_ hw) := by
  intro σ
  unfold Machines.Lnp64u.Isa.transferByHandle
  by_cases hz : hw = 0
  · rw [if_pos hz]
    exact ⟨fun a σ' he d' s => by
        simp only [specM_pure] at he; obtain ⟨_, rfl⟩ := he; exact le_refl _,
      fun e σ' he d' s => by simp [specM_pure] at he⟩
  · simp only [if_neg hz, specM_bind]
    constructor
    · intro a σ' he d' s
      cases hcl : capLive d hw σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := capLive_ok d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sslot, gg, ee⟩ := r
          simp only [SpecM.get, specM_bind] at he
          cases htc : σ.transferCap d sslot to_ with
          | none => rw [htc] at he; simp [SpecM.raise] at he
          | some pr =>
              obtain ⟨σ2, ref⟩ := pr
              rw [htc] at he; simp only [SpecM.set, specM_bind, specM_pure] at he
              injection he with _ h2; subst h2
              exact transferCap_slotGen_ge σ d sslot to_ σ2 ref htc d' s
    · intro er σ' he d' s
      cases hcl : capLive d hw σ with
      | err e0 σ0 =>
          have hs := capLive_err_state d _ σ hcl; rw [hcl] at he
          injection he with _ h2; subst h2; subst hs; exact le_refl _
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := capLive_ok d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sslot, gg, ee⟩ := r
          simp only [SpecM.get, specM_bind] at he
          cases htc : σ.transferCap d sslot to_ with
          | none =>
              rw [htc] at he; simp only [SpecM.raise] at he
              injection he with _ h2; subst h2; exact le_refl _
          | some pr =>
              obtain ⟨σ2, ref⟩ := pr
              rw [htc] at he; simp [SpecM.set, specM_bind, specM_pure] at he

/-- `gate_call` never lowers a slot generation: the only lineage-touching piece
is the capability transfer (`transferByHandle_slotGen_le`); the activation /
serving / run bookkeeping leaves `slotGen` alone. -/
theorem gatecall_slotGen_le (c : Ctx) : SlotGenLe (gateCallExec c) := by
  intro σ
  have body : ∀ (out : Res Unit), gateCallExec c σ = out →
      (∀ a σ', out = .ok a σ' →
        ∀ d' s, ((σ.doms d').slotGen s).toNat ≤ ((σ'.doms d').slotGen s).toNat) ∧
      (∀ e σ', out = .err e σ' →
        ∀ d' s, ((σ.doms d').slotGen s).toNat ≤ ((σ'.doms d').slotGen s).toNat) := by
    intro out hout
    unfold gateCallExec at hout
    simp only [SpecM.reg, specM_bind] at hout
    cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 =>
        have hs := capLive_err_state c.d _ σ hcl; rw [hcl] at hout; subst hout
        exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
          simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hs
          intro d' s; exact le_refl _⟩
    | fault f => rw [hcl] at hout; subst hout
                 exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
    | ok r σ0 =>
        obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at hout; obtain ⟨s0, g0, e⟩ := r; simp only at hout
        cases hk : e.kind with
        | mem base len perms =>
            rw [hk] at hout; simp only [SpecM.raise] at hout; subst hout
            exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
              simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h
              intro d' s; exact le_refl _⟩
        | gate gid =>
            rw [hk] at hout; simp only [SpecM.get, specM_bind] at hout
            set cal := (σ.gates gid).config.callee with hcaldef
            cases hr1 : SpecM.require (σ.gates gid).act.isNone .gateBusy σ with
            | err e1 σ1 => have hst := require_err_state _ _ σ hr1; rw [hr1] at hout; simp only [specM_bind] at hout; subst hout
                           exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                             simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; intro d' s; exact le_refl _⟩
            | fault f => rw [hr1] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
            | ok u1 σ1 =>
                have hst := require_ok _ _ σ hr1; subst σ1
                rw [hr1] at hout; simp only [specM_bind] at hout
                cases hr2 : SpecM.require (decide (cal ≠ c.d)) .gateBusy σ with
                | err e2 σ2 => have hst := require_err_state _ _ σ hr2; rw [hr2] at hout; simp only [specM_bind] at hout; subst hout
                               exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                 simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; intro d' s; exact le_refl _⟩
                | fault f => rw [hr2] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                | ok u2 σ2 =>
                    have hst := require_ok _ _ σ hr2; subst σ2
                    rw [hr2] at hout; simp only [specM_bind] at hout
                    cases hr3 : SpecM.require (decide ((σ.doms cal).run = .running)) .gateBusy σ with
                    | err e3 σ3 => have hst := require_err_state _ _ σ hr3; rw [hr3] at hout; simp only [specM_bind] at hout; subst hout
                                   exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                     simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; intro d' s; exact le_refl _⟩
                    | fault f => rw [hr3] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                    | ok u3 σ3 =>
                        have hst := require_ok _ _ σ hr3; subst σ3
                        rw [hr3] at hout; simp only [specM_bind] at hout
                        cases hr4 : SpecM.require (σ.doms cal).serving.isNone .gateBusy σ with
                        | err e4 σ4 => have hst := require_err_state _ _ σ hr4; rw [hr4] at hout; simp only [specM_bind] at hout; subst hout
                                       exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                         simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; intro d' s; exact le_refl _⟩
                        | fault f => rw [hr4] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                        | ok u4 σ4 =>
                            have hst := require_ok _ _ σ hr4; subst σ4
                            rw [hr4] at hout; simp only [specM_bind] at hout
                            cases hr5 : SpecM.require (decide (gateDepth c σ ≤ maxChainDepth)) .gateBusy σ with
                            | err e5 σ5 => have hst := require_err_state _ _ σ hr5; rw [hr5] at hout; simp only [specM_bind] at hout; subst hout
                                           exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                             simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; intro d' s; exact le_refl _⟩
                            | fault f => rw [hr5] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                            | ok u5 σ5 =>
                                have hst := require_ok _ _ σ hr5; subst σ5
                                rw [hr5] at hout; simp only [specM_bind, SpecM.reg] at hout
                                cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d cal ((σ.doms c.d).reg c.op.rs2) σ with
                                | fault f => rw [htbh] at hout; subst hout
                                             exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                                | err e6 τ =>
                                    rw [htbh] at hout; subst hout
                                    have hτ := (transferByHandle_slotGen_le c.d cal _ σ).2 e6 τ htbh
                                    exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                      simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hτ⟩
                                | ok argHandle τ =>
                                    rw [htbh] at hout
                                    have hτ := (transferByHandle_slotGen_le c.d cal _ σ).1 argHandle τ htbh
                                    simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom, SpecM.modify] at hout
                                    subst hout
                                    refine ⟨fun a σ' h => ?_, fun e σ' h => by simp at h⟩
                                    simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                                    intro d' s
                                    refine le_trans (hτ d' s) (le_of_eq ?_)
                                    rw [setDom_slotGen_of _ c.d _ rfl, setDom_slotGen_of _ cal _ rfl]
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun e σ' h => (body _ h).2 e σ' rfl⟩

/-- `gate_return` never lowers a slot generation: the only lineage-touching
piece is the reply transfer; restoring the caller's context leaves `slotGen`
alone. -/
theorem gatereturn_slotGen_le (c : Ctx) :
    SlotGenLe ((do
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
              SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
              SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
              SpecM.updDom act.caller (fun ds => { ds with run := .running })
              SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) := by
  intro σ
  have body : ∀ (out : Res Unit),
      ((do
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
                SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
                SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
                SpecM.updDom act.caller (fun ds => { ds with run := .running })
                SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) σ = out →
      (∀ a σ', out = .ok a σ' →
        ∀ d' s, ((σ.doms d').slotGen s).toNat ≤ ((σ'.doms d').slotGen s).toNat) ∧
      (∀ e σ', out = .err e σ' →
        ∀ d' s, ((σ.doms d').slotGen s).toNat ≤ ((σ'.doms d').slotGen s).toNat) := by
    intro out hout
    simp only [SpecM.get, specM_bind] at hout
    cases hserv : (σ.doms c.d).serving with
    | none => rw [hserv] at hout; simp only [SpecM.fatal] at hout; subst hout
              exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
    | some gid =>
        simp only [hserv] at hout
        cases hgact : (σ.gates gid).act with
        | none => simp only [hgact] at hout; simp only [SpecM.fatal] at hout; subst hout
                  exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
        | some act =>
            simp only [hgact, SpecM.reg, specM_bind] at hout
            cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d act.caller ((σ.doms c.d).reg c.op.rs1) σ with
            | fault f => rw [htbh] at hout; subst hout
                         exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
            | err e1 τ =>
                rw [htbh] at hout; subst hout
                have hτ := (transferByHandle_slotGen_le c.d act.caller _ σ).2 e1 τ htbh
                exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                  simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hτ⟩
            | ok reply τ =>
                rw [htbh] at hout
                have hτ := (transferByHandle_slotGen_le c.d act.caller _ σ).1 reply τ htbh
                simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom, SpecM.modify,
                           SpecM.setReg] at hout
                subst hout
                refine ⟨fun a σ' h => ?_, fun e σ' h => by simp at h⟩
                simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                intro d' s
                refine le_trans (hτ d' s) (le_of_eq ?_)
                rw [setDom_slotGen_of _ act.caller _ (by unfold DomainState.setReg; split <;> rfl),
                    setDom_slotGen_of _ act.caller _ rfl,
                    setDom_slotGen_of _ c.d _ rfl]
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun e σ' h => (body _ h).2 e σ' rfl⟩

/-- **The system opcodes never lower a slot generation** (7 preserving via the
combinator, 4 bumping via the kernel `clearSlot`/`destroyMarked` bounds). -/
theorem system_slotGen_le : ∀ instr ∈ Machines.Lnp64u.Isa.system, ∀ c : Ctx,
    SlotGenLe (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  case _ => -- cap_dup
    intro σ; constructor
    · intro a σ' he d' s
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          have hstep : ∀ (kd : CapKind) (hh : Loom.Word32) (τ : MachineState),
              allocDerived c.d kd ⟨c.d, sl, gg⟩ σ = .ok hh τ →
              (SpecM.setReg c.d c.op.rd hh) τ = .ok a σ' →
              ((σ.doms d').slotGen s).toNat ≤ ((σ'.doms d').slotGen s).toNat := by
            intro kd hh τ hal hsr
            have h1 := (SlotGenLe.allocDerived c.d kd ⟨c.d, sl, gg⟩ σ).1 hh τ hal d' s
            have h2 := (SlotGenLe.setReg c.d c.op.rd hh τ).1 a σ' hsr d' s
            exact le_trans h1 h2
          cases hk : e.kind with
          | gate g =>
              rw [hk] at he; simp only [specM_pure, specM_bind] at he
              cases hal : allocDerived c.d (.gate g) ⟨c.d, sl, gg⟩ σ with
              | err e1 σ1 => rw [hal] at he; simp at he
              | fault f => rw [hal] at he; simp at he
              | ok hh τ => rw [hal] at he; exact hstep _ hh τ hal he
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => rw [hn] at he; simp at he
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : allocDerived c.d kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => rw [hal] at he; simp at he
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ => rw [hal] at he; exact hstep _ hh τ hal he
    · intro e σ' he d' s
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs; exact le_refl _
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g =>
              rw [hk] at he; simp only [specM_pure, specM_bind] at he
              cases hal : allocDerived c.d (.gate g) ⟨c.d, sl, gg⟩ σ with
              | err e1 σ1 => have hs := Machines.Lnp64u.Isa.Wip.allocDerived_err_state c.d _ _ σ hal
                             rw [hal] at he; injection he with _ h2; subst h2; subst hs; exact le_refl _
              | fault f => rw [hal] at he; simp at he
              | ok hh τ => rw [hal] at he; simp [SpecM.setReg, SpecM.modify] at he
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => have hs := Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms _ σ hn
                             rw [hn] at he; injection he with _ h2; subst h2; subst hs; exact le_refl _
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : allocDerived c.d kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => have hs := Machines.Lnp64u.Isa.Wip.allocDerived_err_state c.d _ _ σ hal
                                 rw [hal] at he; injection he with _ h2; subst h2; subst hs; exact le_refl _
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ => rw [hal] at he; simp [SpecM.setReg, SpecM.modify] at he
  case _ => -- cap_drop
    intro σ; constructor
    · intro a σ'' he d' s
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, _⟩ := r; simp only at he
          simp only [SpecM.get, specM_bind] at he
          have key : ∀ (σ' : MachineState), (σ'.doms d').slotGen s = (σ.doms d').slotGen s →
              (SpecM.set (((σ'.clearSlot c.d sl).sweepRegions).sweepMover) >>=
                fun _ => SpecM.setReg c.d c.op.rd 0) σ = .ok a σ'' →
              ((σ.doms d').slotGen s).toNat ≤ ((σ''.doms d').slotGen s).toNat := by
            intro σ' hpre hset
            simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at hset
            injection hset with _ h2; subst h2
            have hsr : ((((((σ'.clearSlot c.d sl).sweepRegions).sweepMover).setDom c.d
                        (fun ds => ds.setReg c.op.rd 0)).doms d').slotGen s) =
                       ((((σ'.clearSlot c.d sl).sweepRegions).sweepMover).doms d').slotGen s := by
              unfold MachineState.setDom
              by_cases h1 : d' = c.d
              · subst h1; simp [Loom.Fun.update_same]
              · simp [Loom.Fun.update_ne _ _ _ _ h1]
            rw [hsr, ← hpre]; exact clearSlot_sweeps_slotGen_ge σ' c.d sl d' s
          cases hp : σ.parentOf c.d sl with
          | some p => rw [hp] at he
                      exact key _ (reparent_slotGen σ _ _ d' s) he
          | none => rw [hp] at he
                    exact key _ (congrFun (orphanChildren_slotGen σ _ d') s) he
    · intro e σ'' he d' s
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs; exact le_refl _
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, _⟩ := r; simp only at he
          simp only [SpecM.get, specM_bind] at he
          cases hp : σ.parentOf c.d sl with
          | some p => rw [hp] at he; simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
          | none => rw [hp] at he; simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
  case _ => -- cap_revoke
    intro σ; constructor
    · intro a σ'' he d' s
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          simp only [SpecM.require] at he
          by_cases hcls : decide (e.kind.cls = .mem) = true
          · simp only [hcls, if_true, specM_pure, specM_bind, SpecM.get] at he
            simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
            injection he with _ h2; subst h2
            have hsr : (((((σ.destroyMarked (σ.marks ⟨c.d, sl, gg⟩)).sweepRegions).sweepMover).setDom c.d
                        (fun ds => ds.setReg c.op.rd 0)).doms d').slotGen s =
                       ((((σ.destroyMarked (σ.marks ⟨c.d, sl, gg⟩)).sweepRegions).sweepMover).doms d').slotGen s := by
              unfold MachineState.setDom
              by_cases h1 : d' = c.d
              · subst h1; simp [Loom.Fun.update_same]
              · simp [Loom.Fun.update_ne _ _ _ _ h1]
            rw [hsr]; exact destroyMarked_sweeps_slotGen_ge σ _ d' s
          · rw [if_neg hcls] at he; simp [SpecM.raise, specM_bind] at he
    · intro e σ'' he d' s
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs; exact le_refl _
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          simp only [SpecM.require] at he
          by_cases hcls : decide (e.kind.cls = .mem) = true
          · simp only [hcls, if_true, specM_pure, specM_bind, SpecM.get] at he
            simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
          · rw [if_neg hcls] at he; simp only [SpecM.raise, specM_bind] at he
            injection he with _ h2; subst h2; exact le_refl _
  case _ => -- mem_grant
    intro σ; constructor
    · intro a σ' he d' s
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp [SpecM.raise] at he
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => rw [hn] at he; simp at he
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : allocDerived (descDom ((σ.doms c.d).reg c.op.rs2)) kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => rw [hal] at he; simp at he
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ =>
                      rw [hal] at he
                      have h1 := (SlotGenLe.allocDerived (descDom _) kd ⟨c.d, sl, gg⟩ σ).1 hh τ hal d' s
                      have h2 := (SlotGenLe.setReg c.d c.op.rd hh τ).1 a σ' he d' s
                      exact le_trans h1 h2
    · intro e σ' he d' s
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs; exact le_refl _
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact le_refl _
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => have hs := Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms _ σ hn
                             rw [hn] at he; injection he with _ h2; subst h2; subst hs; exact le_refl _
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : allocDerived (descDom ((σ.doms c.d).reg c.op.rs2)) kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => have hs := Machines.Lnp64u.Isa.Wip.allocDerived_err_state (descDom _) _ _ σ hal
                                 rw [hal] at he; injection he with _ h2; subst h2; subst hs; exact le_refl _
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ => rw [hal] at he; simp [SpecM.setReg, SpecM.modify] at he
  case _ => -- map
    intro σ; constructor
    · intro a σ' he d' s
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp [SpecM.raise] at he
          | mem base len perms =>
              rw [hk] at he
              simp only [SpecM.updDom, SpecM.modify, SpecM.setReg, specM_bind, SpecM.set] at he
              injection he with _ h2; subst h2
              unfold MachineState.setDom
              by_cases h1 : d' = c.d
              · subst h1; simp [Loom.Fun.update_same]
              · simp [Loom.Fun.update_ne _ _ _ _ h1]
    · intro e σ' he d' s
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs; exact le_refl _
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact le_refl _
          | mem base len perms =>
              rw [hk] at he
              simp [SpecM.updDom, SpecM.modify, SpecM.setReg, specM_bind, SpecM.set] at he
  case _ => exact SlotGenLe.unmap c _
  case _ => exact gatecall_slotGen_le c
  case _ => exact gatereturn_slotGen_le c
  case _ => exact move_slotGen_le c
  case _ => exact SlotGenLe.yield c
  case _ => exact SlotGenLe.halt c

/-- Transport a `Gen` equality to the `toNat` bound. -/
theorem toNat_le_of_eq {w : Nat} {a b : BitVec w} (h : a = b) : a.toNat ≤ b.toNat :=
  h ▸ Nat.le_refl _

/-- **Every instruction's exec never lowers a slot generation** — the base
combinator dispatch plus the 11 system-op cases. -/
theorem exec_slotGen_le : ∀ instr ∈ isa, ∀ c : Ctx, SlotGenLe (instr.sem.exec c) := by
  intro instr hmem c
  have hmem' : instr ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
    have hiseq : Machines.Lnp64u.isa =
      (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray := rfl
    rw [hiseq, Array.mem_toArray] at hmem; exact hmem
  rcases List.mem_append.mp hmem' with hb | hs
  · exact base_slotGen_le instr hb c
  · exact system_slotGen_le instr hs c

/-- `retire` never lowers a slot generation: the pc bump and the errno
write-back preserve `slotGen`; halts preserve; the instruction effect is
`exec_slotGen_le`. -/
theorem retire_slotGen_ge (σ : MachineState) (d : DomainId) (w : Loom.Word32)
    (d' : DomainId) (s : Slot) :
    ((σ.doms d').slotGen s).toNat ≤ (((retire σ d w).doms d').slotGen s).toNat := by
  unfold retire
  split
  · exact toNat_le_of_eq (haltDom_slotGen σ d _ d' s).symm
  · rename_i instr hdec
    have h1 : (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').slotGen s)
        = (σ.doms d').slotGen s :=
      setDom_slotGen_of σ d _ rfl d' s
    have hex := exec_slotGen_le instr (Loom.Isa.decode_mem isa hdec)
      { d := d, pc := (σ.doms d).pc, op := operandsOf w }
      (σ.setDom d (fun ds => { ds with pc := ds.pc + 1 }))
    cases hexr : instr.sem.exec { d := d, pc := (σ.doms d).pc, op := operandsOf w }
        (σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })) with
    | ok a σ' =>
        simp only [hexr]
        rw [← h1]; exact hex.1 a σ' hexr d' s
    | err e σ' =>
        simp only [hexr]
        rw [setDom_slotGen_of σ' d _ (by unfold DomainState.setReg; split <;> rfl) d' s, ← h1]
        exact hex.2 e σ' hexr d' s
    | fault f =>
        simp only [hexr]
        exact toNat_le_of_eq (haltDom_slotGen σ d _ d' s).symm

/-- `corePhase` never lowers a slot generation: countdown/stall/issue leave
`slotGen` alone; retirement is `retire_slotGen_ge`; halts preserve. -/
theorem corePhase_slotGen_ge (m : Manifest) (σ : MachineState)
    (d' : DomainId) (s : Slot) :
    ((σ.doms d').slotGen s).toNat ≤ (((corePhase m σ).doms d').slotGen s).toNat := by
  unfold corePhase
  cases hinf : σ.inflight with
  | some fl =>
      by_cases hc : fl.cyclesLeft ≤ 1
      · simp only [hc, if_true]
        exact retire_slotGen_ge { σ with inflight := none } fl.dom fl.word d' s
      · simp only [hc, if_false]
        exact Nat.le_refl _
  | none =>
      simp only []
      split
      · exact Nat.le_refl _
      · rename_i d hsched
        split
        · exact toNat_le_of_eq (haltDom_slotGen σ d _ d' s).symm
        · rename_i w hfetch
          split
          · exact toNat_le_of_eq (haltDom_slotGen σ d _ d' s).symm
          · rename_i instr hdec
            by_cases hbud : instr.cost.cost ≤ (σ.doms (σ.payer d)).budget
            · simp only [hbud, if_true]
              cases hserv : (σ.doms d).serving with
              | none =>
                  simp only [hserv]
                  exact toNat_le_of_eq (setDom_slotGen_of σ (σ.payer d) _ rfl d' s).symm
              | some g =>
                  simp only [hserv]
                  cases hact : (σ.gates g).act with
                  | none => exact toNat_le_of_eq (haltDom_slotGen σ d _ d' s).symm
                  | some a =>
                      simp only [hact]
                      by_cases hdon : instr.cost.cost ≤ a.donated
                      · simp only [hdon, if_true]
                        exact toNat_le_of_eq (setDom_slotGen_of σ (σ.payer d) _ rfl d' s).symm
                      · simp only [hdon, if_false]
                        exact toNat_le_of_eq (haltDom_slotGen σ d _ d' s).symm
            · simp only [hbud, if_false]; exact Nat.le_refl _

/-- **Slot generations never decrease across one cycle** — the `step`-level
monotonicity bound feeding T3's `gen_monotone`. -/
theorem step_slotGen_ge (m : Manifest) (σ : MachineState) (d : DomainId) (s : Slot) :
    ((σ.doms d).slotGen s).toNat ≤ (((step m σ).doms d).slotGen s).toNat := by
  rw [step_slotGen_reduce]
  have h1 : (σ.doms d).slotGen s = ((refillPhase m σ).doms d).slotGen s := by
    rw [refillPhase_slotGen]
  rw [show ((σ.doms d).slotGen s) = ((refillPhase m σ).doms d).slotGen s from h1]
  exact corePhase_slotGen_ge m (refillPhase m σ) d s

end Wip

end Machines.Lnp64u
