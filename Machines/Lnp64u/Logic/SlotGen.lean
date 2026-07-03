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

end Machines.Lnp64u
