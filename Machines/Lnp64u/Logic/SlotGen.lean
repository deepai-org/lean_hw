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
open Machines.Lnp64u.Isa

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
  case _ => sorry -- gate_call
  case _ => sorry -- gate_return
  case _ => sorry -- move
  case _ => exact SlotGenLe.yield c
  case _ => exact SlotGenLe.halt c

end Wip

end Machines.Lnp64u
