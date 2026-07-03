import Machines.Lnp64u.Logic.GateStep
import Machines.Lnp64u.Logic.Inflight
import Machines.Lnp64u.Logic.Authority
import Machines.Lnp64u.Logic.DFrame

/-!
# The two-run relational sweep (T5 support)

`NonInt.retire_step_lockstep`'s engine: executing the *same*
(`code_local`-constrained) instruction of domain `d` in two states that
agree on everything `d` can see produces matching outcomes and preserves
the agreement. The agreement bundle `RC` is `Coupled` plus the boot-pinned
capability view and the coverage-confinement facts, all with the address
set `R` abstracted (instantiated with `NonInt.UnderRoots m₁ d`).
-/

namespace Machines.Lnp64u.DRel

open Machines.Lnp64u Loom SpecM

/-- The relational coupling on everything `d`'s instruction can see or
touch. -/
structure RC (d : DomainId) (R : Addr → Prop) (σ₁ σ₂ : MachineState) : Prop where
  regs : (σ₁.doms d).regs = (σ₂.doms d).regs
  pc : (σ₁.doms d).pc = (σ₂.doms d).pc
  run : (σ₁.doms d).run = (σ₂.doms d).run
  cause : (σ₁.doms d).cause = (σ₂.doms d).cause
  regions : (σ₁.doms d).regions = (σ₂.doms d).regions
  caps : (σ₁.doms d).caps = (σ₂.doms d).caps
  gen : (σ₁.doms d).slotGen = (σ₂.doms d).slotGen
  serv1 : (σ₁.doms d).serving = none
  serv2 : (σ₂.doms d).serving = none
  full1 : ∀ s, (σ₁.doms d).caps s ≠ none
  nog1 : ∀ s e g, (σ₁.doms d).caps s = some e → e.kind ≠ .gate g
  /-- `d`'s own memory kinds sit inside `R` (they are boot roots). -/
  capsR : ∀ s e b l p, (σ₁.doms d).caps s = some e → e.kind = .mem b l p →
    ∀ a : Addr, b.toNat ≤ a.toNat → a.toNat < b.toNat + l.toNat → R a
  memR : ∀ a, R a → σ₁.mem a = σ₂.mem a
  covR : ∀ a need, σ₁.domCovers d a need = true → R a

section Kit

variable {d : DomainId} {R : Addr → Prop}

/-- Coverage agrees across the coupling. -/
theorem RC.covers {σ₁ σ₂ : MachineState} (h : RC d R σ₁ σ₂) (a : Addr) (need : Perms) :
    σ₁.domCovers d a need = σ₂.domCovers d a need := by
  unfold MachineState.domCovers
  rw [h.regions]

theorem RC.reg_eq {σ₁ σ₂ : MachineState} (h : RC d R σ₁ σ₂) (r : RegId) :
    (σ₁.doms d).reg r = (σ₂.doms d).reg r := by
  unfold DomainState.reg
  rw [h.regs]

/-- The relational obligation: matching outcomes with equal values/errnos/
faults, agreement preserved. -/
def RLe (d : DomainId) (R : Addr → Prop) {α : Type} (mm : SpecM α) : Prop :=
  ∀ σ₁ σ₂, RC d R σ₁ σ₂ →
    (∀ a τ₁, mm σ₁ = .ok a τ₁ → ∃ τ₂, mm σ₂ = .ok a τ₂ ∧ RC d R τ₁ τ₂) ∧
    (∀ e τ₁, mm σ₁ = .err e τ₁ → ∃ τ₂, mm σ₂ = .err e τ₂ ∧ RC d R τ₁ τ₂) ∧
    (∀ f, mm σ₁ = .fault f → mm σ₂ = .fault f)

theorem RLe.pure {α : Type} (a : α) : RLe d R (Pure.pure a : SpecM α) := by
  intro σ₁ σ₂ hrc
  refine ⟨?_, ?_, ?_⟩
  · intro a' τ₁ he
    rw [specM_pure] at he
    injection he with h1 h2
    subst h1; subst h2
    exact ⟨σ₂, rfl, hrc⟩
  · intro e τ₁ he
    rw [specM_pure] at he
    simp at he
  · intro f he
    rw [specM_pure] at he
    simp at he

theorem RLe.bind {α β : Type} {m : SpecM α} {f : α → SpecM β}
    (hm : RLe d R m) (hf : ∀ a, RLe d R (f a)) : RLe d R (m >>= f) := by
  intro σ₁ σ₂ hrc
  obtain ⟨hok, herr, hfa⟩ := hm σ₁ σ₂ hrc
  refine ⟨?_, ?_, ?_⟩
  · intro b τ₁ he
    rw [specM_bind] at he
    cases hm1 : m σ₁ with
    | ok a κ₁ =>
        rw [hm1] at he
        obtain ⟨κ₂, hm2, hrc'⟩ := hok a κ₁ hm1
        obtain ⟨τ₂, hf2, hrc''⟩ := (hf a κ₁ κ₂ hrc').1 b τ₁ he
        exact ⟨τ₂, by rw [specM_bind, hm2]; exact hf2, hrc''⟩
    | err e κ₁ => rw [hm1] at he; simp at he
    | fault g => rw [hm1] at he; simp at he
  · intro e τ₁ he
    rw [specM_bind] at he
    cases hm1 : m σ₁ with
    | ok a κ₁ =>
        rw [hm1] at he
        obtain ⟨κ₂, hm2, hrc'⟩ := hok a κ₁ hm1
        obtain ⟨τ₂, hf2, hrc''⟩ := (hf a κ₁ κ₂ hrc').2.1 e τ₁ he
        exact ⟨τ₂, by rw [specM_bind, hm2]; exact hf2, hrc''⟩
    | err e1 κ₁ =>
        rw [hm1] at he
        injection he with h1 h2
        subst h1; subst h2
        obtain ⟨κ₂, hm2, hrc'⟩ := herr e1 κ₁ hm1
        exact ⟨κ₂, by rw [specM_bind, hm2], hrc'⟩
    | fault g => rw [hm1] at he; simp at he
  · intro f0 he
    rw [specM_bind] at he
    cases hm1 : m σ₁ with
    | ok a κ₁ =>
        rw [hm1] at he
        obtain ⟨κ₂, hm2, hrc'⟩ := hok a κ₁ hm1
        rw [specM_bind, hm2]
        exact (hf a κ₁ κ₂ hrc').2.2 f0 he
    | err e κ₁ => rw [hm1] at he; simp at he
    | fault g =>
        rw [hm1] at he
        injection he with h1
        subst h1
        rw [specM_bind, hfa g hm1]

theorem RLe.iteBool {α : Type} (b : Bool) {m1 m2 : SpecM α}
    (h1 : RLe d R m1) (h2 : RLe d R m2) : RLe d R (if b then m1 else m2) := by
  cases b <;> simp only [Bool.false_eq_true, if_true, if_false]
  · exact h2
  · exact h1

theorem RLe.reg (r : RegId) : RLe d R (SpecM.reg d r) := by
  intro σ₁ σ₂ hrc
  refine ⟨?_, ?_, ?_⟩
  · intro a τ₁ he
    unfold SpecM.reg at he
    injection he with h1 h2
    subst h1; subst h2
    exact ⟨σ₂, by unfold SpecM.reg; rw [hrc.reg_eq r], hrc⟩
  · intro e τ₁ he
    unfold SpecM.reg at he
    simp at he
  · intro f he
    unfold SpecM.reg at he
    simp at he

theorem RLe.raise {α : Type} (e : Errno) : RLe d R (SpecM.raise e : SpecM α) := by
  intro σ₁ σ₂ hrc
  refine ⟨?_, ?_, ?_⟩
  · intro a τ₁ he
    unfold SpecM.raise at he
    simp at he
  · intro e' τ₁ he
    unfold SpecM.raise at he
    injection he with h1 h2
    subst h1; subst h2
    exact ⟨σ₂, rfl, hrc⟩
  · intro f he
    unfold SpecM.raise at he
    simp at he

theorem RLe.require (cond : Bool) (e : Errno) : RLe d R (SpecM.require cond e) := by
  unfold SpecM.require
  cases cond <;> simp only [Bool.false_eq_true, if_true, if_false]
  · exact RLe.raise e
  · exact RLe.pure ()

theorem RLe.demand (cond : Bool) (f : Fault) : RLe d R (SpecM.demand cond f) := by
  unfold SpecM.demand
  cases cond <;> simp only [Bool.false_eq_true, if_true, if_false]
  · intro σ₁ σ₂ hrc
    exact ⟨fun a τ₁ he => by simp [SpecM.fatal] at he,
      fun e τ₁ he => by simp [SpecM.fatal] at he,
      fun f0 he => by
        unfold SpecM.fatal at he ⊢
        injection he with h1
        subst h1
        rfl⟩
  · exact RLe.pure ()

theorem RLe.load (a : Addr) : RLe d R (SpecM.load d a) := by
  intro σ₁ σ₂ hrc
  have hcov := hrc.covers a { r := true, w := false, x := false }
  unfold SpecM.load
  refine ⟨?_, ?_, ?_⟩
  · intro v τ₁ he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ₁.domCovers d a { r := true, w := false, x := false }
    · have hval : σ₁.read a = σ₂.read a :=
        hrc.memR a (hrc.covR a _ hc)
      simp only [SpecM.demand, hc, if_true, specM_pure, specM_bind] at he
      injection he with h1 h2
      subst h1; subst h2
      refine ⟨σ₂, ?_, hrc⟩
      simp only [SpecM.get, specM_bind, SpecM.demand, ← hcov, hc, if_true,
        specM_pure, hval]
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he
  · intro e τ₁ he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ₁.domCovers d a { r := true, w := false, x := false }
    · simp [SpecM.demand, hc, specM_pure, specM_bind] at he
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he
  · intro f he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ₁.domCovers d a { r := true, w := false, x := false }
    · simp [SpecM.demand, hc, specM_pure, specM_bind] at he
    · simp only [SpecM.demand, hc, if_false, SpecM.fatal, specM_bind] at he ⊢
      injection he with h1
      subst h1
      simp [SpecM.get, SpecM.demand, ← hcov, hc, SpecM.fatal, specM_bind]

/-- Simultaneous same-value memory writes preserve the coupling. -/
theorem RC.write {σ₁ σ₂ : MachineState} (h : RC d R σ₁ σ₂) (a : Addr)
    (v : Loom.Word32) : RC d R (σ₁.write a v) (σ₂.write a v) where
  regs := h.regs
  pc := h.pc
  run := h.run
  cause := h.cause
  regions := h.regions
  caps := h.caps
  gen := h.gen
  serv1 := h.serv1
  serv2 := h.serv2
  full1 := h.full1
  nog1 := h.nog1
  capsR := h.capsR
  memR := fun a' ha' => by
    show Loom.Fun.update σ₁.mem a v a' = Loom.Fun.update σ₂.mem a v a'
    by_cases haa : a' = a
    · subst haa
      rw [Loom.Fun.update_same, Loom.Fun.update_same]
    · rw [Loom.Fun.update_ne _ _ _ _ haa, Loom.Fun.update_ne _ _ _ _ haa]
      exact h.memR a' ha'
  covR := h.covR

theorem RLe.store (a : Addr) (v : Loom.Word32) : RLe d R (SpecM.store d a v) := by
  intro σ₁ σ₂ hrc
  have hcov := hrc.covers a { r := false, w := true, x := false }
  unfold SpecM.store
  refine ⟨?_, ?_, ?_⟩
  · intro x τ₁ he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ₁.domCovers d a { r := false, w := true, x := false }
    · simp only [SpecM.demand, hc, if_true, specM_pure, specM_bind, SpecM.set] at he
      injection he with h1 h2
      subst h2
      refine ⟨σ₂.write a v, ?_, hrc.write a v⟩
      simp [SpecM.get, specM_bind, SpecM.demand, ← hcov, hc, specM_pure, SpecM.set]
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he
  · intro e τ₁ he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ₁.domCovers d a { r := false, w := true, x := false }
    · simp [SpecM.demand, hc, specM_pure, specM_bind, SpecM.set] at he
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he
  · intro f he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ₁.domCovers d a { r := false, w := true, x := false }
    · simp [SpecM.demand, hc, specM_pure, specM_bind, SpecM.set] at he
    · simp only [SpecM.demand, hc, if_false, SpecM.fatal, specM_bind] at he ⊢
      injection he with h1
      subst h1
      simp [SpecM.get, SpecM.demand, ← hcov, hc, SpecM.fatal, specM_bind]

/-- A simultaneous `setDom d` whose update preserves the coupling. -/
theorem RLe.updDomRC (f : DomainState → DomainState)
    (hf : ∀ σ₁ σ₂, RC d R σ₁ σ₂ → RC d R (σ₁.setDom d f) (σ₂.setDom d f)) :
    RLe d R (SpecM.updDom d f) := by
  intro σ₁ σ₂ hrc
  refine ⟨?_, ?_, ?_⟩
  · intro a τ₁ he
    unfold SpecM.updDom SpecM.modify at he
    injection he with h1 h2
    subst h2
    exact ⟨σ₂.setDom d f, rfl, hf σ₁ σ₂ hrc⟩
  · intro e τ₁ he
    unfold SpecM.updDom SpecM.modify at he
    simp at he
  · intro f0 he
    unfold SpecM.updDom SpecM.modify at he
    simp at he

private theorem setReg_pc0 (ds : DomainState) (r : RegId) (v : Loom.Word32) :
    (ds.setReg r v).pc = ds.pc := by
  unfold DomainState.setReg; split <;> rfl

private theorem setReg_cause0 (ds : DomainState) (r : RegId) (v : Loom.Word32) :
    (ds.setReg r v).cause = ds.cause := by
  unfold DomainState.setReg; split <;> rfl

/-- `setReg` writes the same value on both sides. -/
theorem RLe.setReg (r : RegId) (v : Loom.Word32) : RLe d R (SpecM.setReg d r v) := by
  refine RLe.updDomRC _ (fun σ₁ σ₂ h => ?_)
  have hs1 := setDom_doms_same σ₁ d (fun ds => ds.setReg r v)
  have hs2 := setDom_doms_same σ₂ d (fun ds => ds.setReg r v)
  exact
    { regs := by
        rw [hs1, hs2]
        unfold DomainState.setReg
        split <;> rw [h.regs]
      pc := by rw [hs1, hs2, setReg_pc0, setReg_pc0, h.pc]
      run := by rw [hs1, hs2, setReg_run, setReg_run, h.run]
      cause := by rw [hs1, hs2, setReg_cause0, setReg_cause0, h.cause]
      regions := by rw [hs1, hs2, setReg_regions, setReg_regions, h.regions]
      caps := by rw [hs1, hs2, setReg_caps, setReg_caps, h.caps]
      gen := by rw [hs1, hs2, setReg_slotGen, setReg_slotGen, h.gen]
      serv1 := by rw [hs1, setReg_serving]; exact h.serv1
      serv2 := by rw [hs2, setReg_serving]; exact h.serv2
      full1 := fun s => by rw [hs1, setReg_caps]; exact h.full1 s
      nog1 := fun s e g hc => h.nog1 s e g (by rw [hs1, setReg_caps] at hc; exact hc)
      capsR := fun s e b l p hc => h.capsR s e b l p
        (by rw [hs1, setReg_caps] at hc; exact hc)
      memR := h.memR
      covR := fun a need hcov => by
        refine h.covR a need ?_
        unfold MachineState.domCovers at hcov ⊢
        rw [hs1, setReg_regions] at hcov
        exact hcov }

end Kit

/-! ## Relational atoms: `capLive`, `narrow`, `allocDerived`, halts -/

section Atoms

variable {d : DomainId} {R : Addr → Prop}

theorem RLe.capLive (hw : Loom.Word32) :
    RLe d R (Machines.Lnp64u.Isa.capLive d hw) := by
  intro σ₁ σ₂ hrc
  have hlc : ∀ s g, (σ₁.doms d).liveCap s g = (σ₂.doms d).liveCap s g := by
    intro s g
    unfold DomainState.liveCap
    rw [hrc.caps, hrc.gen]
  have hred : ∀ σ : MachineState, Machines.Lnp64u.Isa.capLive d hw σ =
      (match (σ.doms d).liveCap (Handle.decode hw).slot (Handle.decode hw).gen with
        | none => SpecM.raise .staleHandle
        | some e => (SpecM.require ((Handle.decode hw).cls = e.kind.cls) .badCap >>=
            fun _ => (Pure.pure ((Handle.decode hw).slot, (Handle.decode hw).gen, e) :
              SpecM _))) σ := fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro a τ₁ he
    rw [hred] at he
    cases hl : (σ₁.doms d).liveCap (Handle.decode hw).slot (Handle.decode hw).gen with
    | none => rw [hl] at he; simp [SpecM.raise] at he
    | some e =>
        rw [hl] at he
        by_cases hcls : (Handle.decode hw).cls = e.kind.cls
        · simp only [SpecM.require, hcls, if_true, specM_bind, specM_pure] at he
          injection he with h1 h2
          subst h1; subst h2
          refine ⟨σ₂, ?_, hrc⟩
          rw [hred, ← hlc, hl]
          simp [SpecM.require, hcls, specM_bind, specM_pure]
        · simp [SpecM.require, hcls, specM_bind, SpecM.raise] at he
  · intro e0 τ₁ he
    rw [hred] at he
    cases hl : (σ₁.doms d).liveCap (Handle.decode hw).slot (Handle.decode hw).gen with
    | none =>
        rw [hl] at he
        simp only [SpecM.raise] at he
        injection he with h1 h2
        subst h1; subst h2
        refine ⟨σ₂, ?_, hrc⟩
        rw [hred, ← hlc, hl]
        rfl
    | some e =>
        rw [hl] at he
        by_cases hcls : (Handle.decode hw).cls = e.kind.cls
        · simp [SpecM.require, hcls, specM_bind, specM_pure] at he
        · simp only [SpecM.require, hcls, if_false, specM_bind, SpecM.raise] at he
          injection he with h1 h2
          subst h1; subst h2
          refine ⟨σ₂, ?_, hrc⟩
          rw [hred, ← hlc, hl]
          simp [SpecM.require, hcls, specM_bind, SpecM.raise]
  · intro f he
    rw [hred] at he
    cases hl : (σ₁.doms d).liveCap (Handle.decode hw).slot (Handle.decode hw).gen with
    | none => rw [hl] at he; simp [SpecM.raise] at he
    | some e =>
        rw [hl] at he
        by_cases hcls : (Handle.decode hw).cls = e.kind.cls
        · simp [SpecM.require, hcls, specM_bind, specM_pure] at he
        · simp [SpecM.require, hcls, specM_bind, SpecM.raise] at he

theorem RLe.narrow (base : Addr) (len : BitVec 13) (perms : Perms) (dw : Loom.Word32) :
    RLe d R (Machines.Lnp64u.Isa.narrow base len perms dw) :=
  RLe.bind (RLe.require _ _) (fun _ =>
    RLe.bind (RLe.require _ _) (fun _ =>
      RLe.bind (RLe.require _ _) (fun _ =>
        RLe.bind (RLe.require _ _) (fun _ => RLe.pure _))))

/-- `allocDerived` into `d`'s full table fails identically on both sides. -/
theorem RLe.allocDerivedFull (kind : CapKind) (parent : CapRef) :
    RLe d R (Machines.Lnp64u.Isa.allocDerived d kind parent) := by
  intro σ₁ σ₂ hrc
  have h1 : σ₁.freeSlot d = none := DFrame.freeSlot_none_of_full hrc.full1
  have h2 : σ₂.freeSlot d = none := DFrame.freeSlot_none_of_full
    (fun s => by rw [← hrc.caps]; exact hrc.full1 s)
  refine ⟨?_, ?_, ?_⟩
  · intro a τ₁ he
    unfold Machines.Lnp64u.Isa.allocDerived at he
    simp only [SpecM.get, specM_bind, h1] at he
    simp [SpecM.raise] at he
  · intro e τ₁ he
    unfold Machines.Lnp64u.Isa.allocDerived at he
    simp only [SpecM.get, specM_bind, h1] at he
    simp only [SpecM.raise] at he
    injection he with hε h2'
    subst hε; subst h2'
    refine ⟨σ₂, ?_, hrc⟩
    unfold Machines.Lnp64u.Isa.allocDerived
    simp only [SpecM.get, specM_bind, h2]
    rfl
  · intro f he
    unfold Machines.Lnp64u.Isa.allocDerived at he
    simp only [SpecM.get, specM_bind, h1] at he
    simp [SpecM.raise] at he

private theorem haltBase_field (σ : MachineState) (d : DomainId) (cv : Loom.Word32) :
    ((σ.haltBase d cv).doms d) =
      { σ.doms d with run := .halted, cause := cv, serving := none } := by
  unfold MachineState.haltBase
  rw [setDom_doms_same]

/-- Simultaneous halts preserve the coupling. -/
theorem RC.haltBaseRC {σ₁ σ₂ : MachineState} (h : RC d R σ₁ σ₂) (cv : Loom.Word32) :
    RC d R (σ₁.haltBase d cv) (σ₂.haltBase d cv) where
  regs := by rw [haltBase_field, haltBase_field]; exact h.regs
  pc := by rw [haltBase_field, haltBase_field]; exact h.pc
  run := by rw [haltBase_field, haltBase_field]
  cause := by rw [haltBase_field, haltBase_field]
  regions := by rw [haltBase_field, haltBase_field]; exact h.regions
  caps := by rw [haltBase_field, haltBase_field]; exact h.caps
  gen := by rw [haltBase_field, haltBase_field]; exact h.gen
  serv1 := by rw [haltBase_field]
  serv2 := by rw [haltBase_field]
  full1 := fun s => by rw [haltBase_field]; exact h.full1 s
  nog1 := fun s e g hc => h.nog1 s e g (by rw [haltBase_field] at hc; exact hc)
  capsR := fun s e b l p hc => h.capsR s e b l p (by rw [haltBase_field] at hc; exact hc)
  memR := h.memR
  covR := fun a need hcov => by
    refine h.covR a need ?_
    unfold MachineState.domCovers at hcov ⊢
    rw [show ((σ₁.haltBase d cv).doms d).regions = (σ₁.doms d).regions from by
      rw [haltBase_field]] at hcov
    exact hcov

theorem RC.haltDomRC {σ₁ σ₂ : MachineState} (h : RC d R σ₁ σ₂) (cv : Loom.Word32) :
    RC d R (σ₁.haltDom d cv) (σ₂.haltDom d cv) := by
  rw [haltDom_base σ₁ d cv h.serv1, haltDom_base σ₂ d cv h.serv2]
  exact h.haltBaseRC cv

/-- Simultaneous `pc`-advance. -/
theorem RC.pcBump {σ₁ σ₂ : MachineState} (h : RC d R σ₁ σ₂) :
    RC d R (σ₁.setDom d fun ds => { ds with pc := ds.pc + 1 })
      (σ₂.setDom d fun ds => { ds with pc := ds.pc + 1 }) := by
  have hs1 := setDom_doms_same σ₁ d (fun ds => { ds with pc := ds.pc + 1 })
  have hs2 := setDom_doms_same σ₂ d (fun ds => { ds with pc := ds.pc + 1 })
  exact
    { regs := by rw [hs1, hs2]; exact h.regs
      pc := by rw [hs1, hs2]; show (σ₁.doms d).pc + 1 = (σ₂.doms d).pc + 1; rw [h.pc]
      run := by rw [hs1, hs2]; exact h.run
      cause := by rw [hs1, hs2]; exact h.cause
      regions := by rw [hs1, hs2]; exact h.regions
      caps := by rw [hs1, hs2]; exact h.caps
      gen := by rw [hs1, hs2]; exact h.gen
      serv1 := by rw [hs1]; exact h.serv1
      serv2 := by rw [hs2]; exact h.serv2
      full1 := fun s => by rw [hs1]; exact h.full1 s
      nog1 := fun s e g hc => h.nog1 s e g (by rw [hs1] at hc; exact hc)
      capsR := fun s e b l p hc => h.capsR s e b l p (by rw [hs1] at hc; exact hc)
      memR := h.memR
      covR := fun a need hcov => by
        refine h.covR a need ?_
        unfold MachineState.domCovers at hcov ⊢
        rw [show ((σ₁.setDom d fun ds => { ds with pc := ds.pc + 1 }).doms d).regions
          = (σ₁.doms d).regions from by rw [hs1]] at hcov
        exact hcov }

/-- Simultaneous same-value writes of one register (the errno write-back). -/
theorem RC.setRegBoth {σ₁ σ₂ : MachineState} (h : RC d R σ₁ σ₂) (r : RegId)
    (v : Loom.Word32) :
    RC d R (σ₁.setDom d fun ds => ds.setReg r v)
      (σ₂.setDom d fun ds => ds.setReg r v) := by
  have hs1 := setDom_doms_same σ₁ d (fun ds => ds.setReg r v)
  have hs2 := setDom_doms_same σ₂ d (fun ds => ds.setReg r v)
  exact
    { regs := by
        rw [hs1, hs2]
        unfold DomainState.setReg
        split <;> rw [h.regs]
      pc := by rw [hs1, hs2, setReg_pc0, setReg_pc0]; exact h.pc
      run := by rw [hs1, hs2, setReg_run, setReg_run]; exact h.run
      cause := by rw [hs1, hs2, setReg_cause0, setReg_cause0]; exact h.cause
      regions := by rw [hs1, hs2, setReg_regions, setReg_regions]; exact h.regions
      caps := by rw [hs1, hs2, setReg_caps, setReg_caps]; exact h.caps
      gen := by rw [hs1, hs2, setReg_slotGen, setReg_slotGen]; exact h.gen
      serv1 := by rw [hs1, setReg_serving]; exact h.serv1
      serv2 := by rw [hs2, setReg_serving]; exact h.serv2
      full1 := fun s => by rw [hs1, setReg_caps]; exact h.full1 s
      nog1 := fun s e g hc => h.nog1 s e g (by rw [hs1, setReg_caps] at hc; exact hc)
      capsR := fun s e b l p hc => h.capsR s e b l p
        (by rw [hs1, setReg_caps] at hc; exact hc)
      memR := h.memR
      covR := fun a need hcov => by
        refine h.covR a need ?_
        unfold MachineState.domCovers at hcov ⊢
        rw [show ((σ₁.setDom d fun ds => ds.setReg r v).doms d).regions
          = (σ₁.doms d).regions from by rw [hs1, setReg_regions]] at hcov
        exact hcov }

/-- Simultaneous identical region-register writes; an installed region must
sit inside `R`. -/
theorem RC.setRegions {σ₁ σ₂ : MachineState} (h : RC d R σ₁ σ₂) (ri : RegionId)
    (v : Option Region)
    (hv : ∀ rg, v = some rg → ∀ a : Addr, rg.base.toNat ≤ a.toNat →
      a.toNat < rg.base.toNat + rg.len.toNat → R a) :
    RC d R (σ₁.setDom d fun ds => { ds with regions := Loom.Fun.update ds.regions ri v })
      (σ₂.setDom d fun ds => { ds with regions := Loom.Fun.update ds.regions ri v }) := by
  have hs1 := setDom_doms_same σ₁ d
    (fun ds => { ds with regions := Loom.Fun.update ds.regions ri v })
  have hs2 := setDom_doms_same σ₂ d
    (fun ds => { ds with regions := Loom.Fun.update ds.regions ri v })
  exact
    { regs := by rw [hs1, hs2]; exact h.regs
      pc := by rw [hs1, hs2]; exact h.pc
      run := by rw [hs1, hs2]; exact h.run
      cause := by rw [hs1, hs2]; exact h.cause
      regions := by rw [hs1, hs2]; show Loom.Fun.update _ ri v = Loom.Fun.update _ ri v
                    rw [h.regions]
      caps := by rw [hs1, hs2]; exact h.caps
      gen := by rw [hs1, hs2]; exact h.gen
      serv1 := by rw [hs1]; exact h.serv1
      serv2 := by rw [hs2]; exact h.serv2
      full1 := fun s => by rw [hs1]; exact h.full1 s
      nog1 := fun s e g hc => h.nog1 s e g (by rw [hs1] at hc; exact hc)
      capsR := fun s e b l p hc => h.capsR s e b l p (by rw [hs1] at hc; exact hc)
      memR := h.memR
      covR := fun a need hcov => by
        unfold MachineState.domCovers at hcov
        rw [decide_eq_true_iff] at hcov
        obtain ⟨r, rg, hrg, hc⟩ := hcov
        have hrg' : Loom.Fun.update (σ₁.doms d).regions ri v r = some rg := by
          rw [← hrg, hs1]
        unfold Region.covers at hc
        simp only [Bool.and_eq_true, decide_eq_true_iff] at hc
        by_cases hri : r = ri
        · subst hri
          rw [Loom.Fun.update_same] at hrg'
          exact hv rg hrg' a hc.1.1 hc.1.2
        · rw [Loom.Fun.update_ne _ _ _ _ hri] at hrg'
          refine h.covR a need ?_
          unfold MachineState.domCovers
          rw [decide_eq_true_iff]
          refine ⟨r, rg, hrg', ?_⟩
          unfold Region.covers
          simp only [Bool.and_eq_true, decide_eq_true_iff]
          exact hc }

end Atoms

/-! ## The relational sweep -/

section Sweep

variable {d : DomainId} {R : Addr → Prop}

/-- Simultaneous `pc := X` (branch targets and jumps are shared values). -/
theorem RC.setPcConst {σ₁ σ₂ : MachineState} (h : RC d R σ₁ σ₂) (X : Addr) :
    RC d R (σ₁.setDom d fun ds => { ds with pc := X })
      (σ₂.setDom d fun ds => { ds with pc := X }) := by
  have hs1 := setDom_doms_same σ₁ d (fun ds => { ds with pc := X })
  have hs2 := setDom_doms_same σ₂ d (fun ds => { ds with pc := X })
  exact
    { regs := by rw [hs1, hs2]; exact h.regs
      pc := by rw [hs1, hs2]
      run := by rw [hs1, hs2]; exact h.run
      cause := by rw [hs1, hs2]; exact h.cause
      regions := by rw [hs1, hs2]; exact h.regions
      caps := by rw [hs1, hs2]; exact h.caps
      gen := by rw [hs1, hs2]; exact h.gen
      serv1 := by rw [hs1]; exact h.serv1
      serv2 := by rw [hs2]; exact h.serv2
      full1 := fun s => by rw [hs1]; exact h.full1 s
      nog1 := fun s e g hc => h.nog1 s e g (by rw [hs1] at hc; exact hc)
      capsR := fun s e b l p hc => h.capsR s e b l p (by rw [hs1] at hc; exact hc)
      memR := h.memR
      covR := fun a need hcov => by
        refine h.covR a need ?_
        unfold MachineState.domCovers at hcov ⊢
        rw [show ((σ₁.setDom d fun ds => { ds with pc := X }).doms d).regions
          = (σ₁.doms d).regions from by rw [hs1]] at hcov
        exact hcov }

/-- Simultaneous `budget := 0` (`yield`; budgets are not coupled). -/
theorem RC.setBudZero {σ₁ σ₂ : MachineState} (h : RC d R σ₁ σ₂) :
    RC d R (σ₁.setDom d fun ds => { ds with budget := 0 })
      (σ₂.setDom d fun ds => { ds with budget := 0 }) := by
  have hs1 := setDom_doms_same σ₁ d (fun ds => { ds with budget := 0 })
  have hs2 := setDom_doms_same σ₂ d (fun ds => { ds with budget := 0 })
  exact
    { regs := by rw [hs1, hs2]; exact h.regs
      pc := by rw [hs1, hs2]; exact h.pc
      run := by rw [hs1, hs2]; exact h.run
      cause := by rw [hs1, hs2]; exact h.cause
      regions := by rw [hs1, hs2]; exact h.regions
      caps := by rw [hs1, hs2]; exact h.caps
      gen := by rw [hs1, hs2]; exact h.gen
      serv1 := by rw [hs1]; exact h.serv1
      serv2 := by rw [hs2]; exact h.serv2
      full1 := fun s => by rw [hs1]; exact h.full1 s
      nog1 := fun s e g hc => h.nog1 s e g (by rw [hs1] at hc; exact hc)
      capsR := fun s e b l p hc => h.capsR s e b l p (by rw [hs1] at hc; exact hc)
      memR := h.memR
      covR := fun a need hcov => by
        refine h.covR a need ?_
        unfold MachineState.domCovers at hcov ⊢
        rw [show ((σ₁.setDom d fun ds => { ds with budget := 0 }).doms d).regions
          = (σ₁.doms d).regions from by rw [hs1]] at hcov
        exact hcov }

/-- **Every `code_local`-legal instruction is relationally safe.** -/
theorem exec_rel : ∀ instr ∈ isa,
    instr.opcode ≠ 17 → instr.opcode ≠ 18 → instr.opcode ≠ 19 → instr.opcode ≠ 24 →
    ∀ c : Ctx, c.d = d → RLe d R (instr.sem.exec c) := by
  intro instr hmem h17 h18 h19 h24 c hcd
  subst hcd
  have hmem' : instr ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
    have hiseq : Machines.Lnp64u.isa =
      (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray := rfl
    rw [hiseq, Array.mem_toArray] at hmem
    exact hmem
  rcases List.mem_append.mp hmem' with hb | hs
  · clear h17 h18 h19 h24
    fin_cases hb
    case _ => exact RLe.bind (RLe.reg _) (fun _ => RLe.bind (RLe.reg _) (fun _ => RLe.setReg _ _))
    case _ => exact RLe.bind (RLe.reg _) (fun _ => RLe.bind (RLe.reg _) (fun _ => RLe.setReg _ _))
    case _ => exact RLe.bind (RLe.reg _) (fun _ => RLe.bind (RLe.reg _) (fun _ => RLe.setReg _ _))
    case _ => exact RLe.bind (RLe.reg _) (fun _ => RLe.bind (RLe.reg _) (fun _ => RLe.setReg _ _))
    case _ => exact RLe.bind (RLe.reg _) (fun _ => RLe.bind (RLe.reg _) (fun _ => RLe.setReg _ _))
    case _ => exact RLe.bind (RLe.reg _) (fun _ => RLe.bind (RLe.reg _) (fun _ => RLe.setReg _ _))
    case _ => exact RLe.bind (RLe.reg _) (fun _ => RLe.bind (RLe.reg _) (fun _ => RLe.setReg _ _))
    case _ => exact RLe.bind (RLe.reg _) (fun _ => RLe.setReg _ _)
    case _ => exact RLe.setReg _ _
    case _ => exact RLe.bind (RLe.reg _) (fun _ => RLe.bind (RLe.load _) (fun _ => RLe.setReg _ _))
    case _ => exact RLe.bind (RLe.reg _) (fun _ => RLe.bind (RLe.reg _) (fun _ => RLe.store _ _))
    case _ => exact RLe.bind (RLe.reg _) (fun _ => RLe.bind (RLe.reg _) (fun _ => RLe.iteBool _ (RLe.updDomRC (fun ds => { ds with pc := branchTarget c.pc c.op.imm }) (fun _ _ h => h.setPcConst _)) (RLe.pure ())))
    case _ => exact RLe.bind (RLe.reg _) (fun _ => RLe.bind (RLe.reg _) (fun _ => RLe.iteBool _ (RLe.updDomRC (fun ds => { ds with pc := branchTarget c.pc c.op.imm }) (fun _ _ h => h.setPcConst _)) (RLe.pure ())))
    case _ => exact RLe.bind (RLe.reg _) (fun a => RLe.bind (RLe.setReg _ _) (fun _ => RLe.updDomRC (fun ds => { ds with pc := effAddr a c.op.imm }) (fun _ _ h => h.setPcConst _)))
  · fin_cases hs
    case _ => -- cap_dup: derivation fails identically at the full table
      refine RLe.bind (RLe.reg _) (fun hw => RLe.bind (RLe.reg _) (fun dw =>
        RLe.bind (RLe.capLive _) (fun r => ?_)))
      obtain ⟨s, g, e⟩ := r
      dsimp only
      cases hk : e.kind with
      | mem base len perms =>
          exact RLe.bind (RLe.narrow base len perms dw) (fun kind =>
            RLe.bind (RLe.allocDerivedFull kind _) (fun h => RLe.setReg _ _))
      | gate gid =>
          exact RLe.bind (RLe.pure _) (fun kind =>
            RLe.bind (RLe.allocDerivedFull kind _) (fun h => RLe.setReg _ _))
    case _ => exact absurd rfl h17
    case _ => exact absurd rfl h18
    case _ => exact absurd rfl h19
    case _ => -- map: both runs cache the same (in-R) authority
      intro σ₁ σ₂ hrc
      have hval : (σ₂.doms c.d).reg c.op.rs1 = (σ₁.doms c.d).reg c.op.rs1 :=
        (hrc.reg_eq c.op.rs1).symm
      obtain ⟨hclok, hclerr, hclfa⟩ :=
        RLe.capLive (d := c.d) (R := R) ((σ₁.doms c.d).reg c.op.rs1) σ₁ σ₂ hrc
      refine ⟨?_, ?_, ?_⟩
      · intro x τ₁ he
        simp only [SpecM.reg, specM_bind] at he
        cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ₁.doms c.d).reg c.op.rs1) σ₁ with
        | err e0 σ0 => rw [hcl] at he; simp at he
        | fault f => rw [hcl] at he; simp at he
        | ok r σ0 =>
            obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ₁ hcl
            subst σ0
            obtain ⟨κ₂, hcl2, hrc'⟩ := hclok r σ₁ hcl
            obtain ⟨hσeq2, -⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ₂ hcl2
            subst κ₂
            rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he hlc
            cases hk : e.kind with
            | gate g => rw [hk] at he; simp [SpecM.raise] at he
            | mem base len perms =>
                rw [hk] at he
                simp only [SpecM.updDom, SpecM.modify, specM_bind, SpecM.setReg] at he
                injection he with h1 h2
                subst h1; subst h2
                have hcapsd : (σ₁.doms c.d).caps sl = some e := caps_of_liveCap hlc
                have hrc1 := hrc.setRegions
                  ⟨(c.op.imm.extractLsb' 0 2).toNat, (c.op.imm.extractLsb' 0 2).isLt⟩
                  (some { base := base, len := len, perms := perms
                          backing := ⟨c.d, sl, gg⟩ })
                  (fun rg hrg => by
                    injection hrg with hrg
                    subst hrg
                    exact hrc.capsR sl e base len perms hcapsd hk)
                refine ⟨_, ?_, hrc1.setRegBoth c.op.rd 0⟩
                simp only [SpecM.reg, specM_bind, hval, hcl2, hk,
                  SpecM.updDom, SpecM.modify, SpecM.setReg]
      · intro e0 τ₁ he
        simp only [SpecM.reg, specM_bind] at he
        cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ₁.doms c.d).reg c.op.rs1) σ₁ with
        | err e1 σ0 =>
            obtain ⟨κ₂, hcl2, hrc'⟩ := hclerr e1 σ0 hcl
            rw [hcl] at he
            injection he with h1 h2
            subst h1; subst h2
            refine ⟨κ₂, ?_, hrc'⟩
            simp only [SpecM.reg, specM_bind, hval, hcl2]
        | fault f => rw [hcl] at he; simp at he
        | ok r σ0 =>
            obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ₁ hcl
            subst σ0
            obtain ⟨κ₂, hcl2, hrc'⟩ := hclok r σ₁ hcl
            obtain ⟨hσeq2, -⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ₂ hcl2
            subst κ₂
            rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
            cases hk : e.kind with
            | gate g =>
                rw [hk] at he
                simp only [SpecM.raise] at he
                injection he with h1 h2
                subst h1; subst h2
                refine ⟨σ₂, ?_, hrc'⟩
                simp only [SpecM.reg, specM_bind, hval, hcl2, hk, SpecM.raise]
            | mem base len perms =>
                rw [hk] at he
                simp [SpecM.updDom, SpecM.modify, specM_bind, SpecM.setReg] at he
      · intro f he
        simp only [SpecM.reg, specM_bind] at he
        cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ₁.doms c.d).reg c.op.rs1) σ₁ with
        | err e1 σ0 => rw [hcl] at he; simp at he
        | fault f0 =>
            have hf2 := hclfa f0 hcl
            rw [hcl] at he
            injection he with h1
            subst h1
            simp only [SpecM.reg, specM_bind, hval, hf2]
        | ok r σ0 =>
            obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ₁ hcl
            subst σ0
            rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
            cases hk : e.kind with
            | gate g => rw [hk] at he; simp [SpecM.raise] at he
            | mem base len perms =>
                rw [hk] at he
                simp [SpecM.updDom, SpecM.modify, specM_bind, SpecM.setReg] at he
    case _ => -- unmap
      exact RLe.bind (RLe.updDomRC
          (fun ds => { ds with regions := Loom.Fun.update ds.regions ⟨(c.op.imm.extractLsb' 0 2).toNat, (c.op.imm.extractLsb' 0 2).isLt⟩ none })
          (fun _ _ h => h.setRegions _ none (fun rg hrg => by cases hrg)))
        (fun _ => RLe.setReg _ _)
    case _ => -- gate_call: `d` holds no gate capabilities
      intro σ₁ σ₂ hrc
      have hval : (σ₂.doms c.d).reg c.op.rs1 = (σ₁.doms c.d).reg c.op.rs1 :=
        (hrc.reg_eq c.op.rs1).symm
      obtain ⟨hclok, hclerr, hclfa⟩ :=
        RLe.capLive (d := c.d) (R := R) ((σ₁.doms c.d).reg c.op.rs1) σ₁ σ₂ hrc
      refine ⟨?_, ?_, ?_⟩
      · intro x τ₁ he
        simp only [SpecM.reg, specM_bind] at he
        cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ₁.doms c.d).reg c.op.rs1) σ₁ with
        | err e0 σ0 => rw [hcl] at he; simp at he
        | fault f => rw [hcl] at he; simp at he
        | ok r σ0 =>
            obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ₁ hcl
            subst σ0
            rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he hlc
            cases hk : e.kind with
            | gate g => exact absurd hk (hrc.nog1 sl e g (caps_of_liveCap hlc))
            | mem base len perms => rw [hk] at he; simp [SpecM.raise] at he
      · intro e0 τ₁ he
        simp only [SpecM.reg, specM_bind] at he
        cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ₁.doms c.d).reg c.op.rs1) σ₁ with
        | err e1 σ0 =>
            obtain ⟨κ₂, hcl2, hrc'⟩ := hclerr e1 σ0 hcl
            rw [hcl] at he
            injection he with h1 h2
            subst h1; subst h2
            refine ⟨κ₂, ?_, hrc'⟩
            simp only [SpecM.reg, specM_bind, hval, hcl2]
        | fault f => rw [hcl] at he; simp at he
        | ok r σ0 =>
            obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ₁ hcl
            subst σ0
            obtain ⟨κ₂, hcl2, hrc'⟩ := hclok r σ₁ hcl
            obtain ⟨hσeq2, -⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ₂ hcl2
            subst κ₂
            rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he hlc
            cases hk : e.kind with
            | gate g => exact absurd hk (hrc.nog1 sl e g (caps_of_liveCap hlc))
            | mem base len perms =>
                rw [hk] at he
                simp only [SpecM.raise] at he
                injection he with h1 h2
                subst h1; subst h2
                refine ⟨σ₂, ?_, hrc'⟩
                simp only [SpecM.reg, specM_bind, hval, hcl2, hk, SpecM.raise]
      · intro f he
        simp only [SpecM.reg, specM_bind] at he
        cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ₁.doms c.d).reg c.op.rs1) σ₁ with
        | err e1 σ0 => rw [hcl] at he; simp at he
        | fault f0 =>
            have hf2 := hclfa f0 hcl
            rw [hcl] at he
            injection he with h1
            subst h1
            simp only [SpecM.reg, specM_bind, hval, hf2]
        | ok r σ0 =>
            obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ₁ hcl
            subst σ0
            rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he hlc
            cases hk : e.kind with
            | gate g => exact absurd hk (hrc.nog1 sl e g (caps_of_liveCap hlc))
            | mem base len perms => rw [hk] at he; simp [SpecM.raise] at he
    case _ => -- gate_return: both runs fault (nobody is served)
      intro σ₁ σ₂ hrc
      refine ⟨?_, ?_, ?_⟩
      · intro x τ₁ he
        simp only [SpecM.get, specM_bind, hrc.serv1] at he
        simp [SpecM.fatal] at he
      · intro e0 τ₁ he
        simp only [SpecM.get, specM_bind, hrc.serv1] at he
        simp [SpecM.fatal] at he
      · intro f he
        simp only [SpecM.get, specM_bind, hrc.serv1] at he
        unfold SpecM.fatal at he
        injection he with h1
        subst h1
        simp [SpecM.get, specM_bind, hrc.serv2, SpecM.fatal]
    case _ => exact absurd rfl h24
    case _ => -- yield
      exact RLe.bind (RLe.updDomRC (fun ds => { ds with budget := 0 })
        (fun _ _ h => h.setBudZero)) (fun _ => RLe.setReg _ _)
    case _ => -- halt
      intro σ₁ σ₂ hrc
      refine ⟨?_, ?_, ?_⟩
      · intro a τ₁ he
        simp only [SpecM.modify] at he
        injection he with h1 h2
        subst h1; subst h2
        exact ⟨σ₂.haltDom c.d 0, rfl, hrc.haltDomRC 0⟩
      · intro e τ₁ he
        simp [SpecM.modify] at he
      · intro f he
        simp [SpecM.modify] at he

/-- **`retire` of the same legal word from coupled states lands coupled.** -/
theorem retire_rel (σ₁ σ₂ : MachineState) (w : Loom.Word32)
    (hrc : RC d R σ₁ σ₂)
    (hop : ∀ instr, Loom.Isa.decode isa w = some instr →
      instr.opcode ≠ 17 ∧ instr.opcode ≠ 18 ∧ instr.opcode ≠ 19 ∧ instr.opcode ≠ 24) :
    RC d R (retire σ₁ d w) (retire σ₂ d w) := by
  unfold retire
  cases hdec : Loom.Isa.decode isa w with
  | none => exact hrc.haltDomRC _
  | some instr =>
      obtain ⟨h17, h18, h19, h24⟩ := hop instr hdec
      rw [show (σ₂.doms d).pc = (σ₁.doms d).pc from hrc.pc.symm]
      have hrc' := hrc.pcBump
      have hobl := exec_rel instr (Loom.Isa.decode_mem isa hdec) h17 h18 h19 h24
        { d := d, pc := (σ₁.doms d).pc, op := operandsOf w } rfl _ _ hrc'
      cases hexr : instr.sem.exec { d := d, pc := (σ₁.doms d).pc, op := operandsOf w }
          (σ₁.setDom d fun ds => { ds with pc := ds.pc + 1 }) with
      | ok a τ₁ =>
          obtain ⟨τ₂, hex2, hrc''⟩ := hobl.1 a τ₁ hexr
          simp only [hexr, hex2]
          exact hrc''
      | err er τ₁ =>
          obtain ⟨τ₂, hex2, hrc''⟩ := hobl.2.1 er τ₁ hexr
          simp only [hexr, hex2]
          exact hrc''.setRegBoth (operandsOf w).rd er.toWord
      | fault f =>
          have hex2 := hobl.2.2 f hexr
          simp only [hexr, hex2]
          exact hrc.haltDomRC _

end Sweep

end Machines.Lnp64u.DRel
