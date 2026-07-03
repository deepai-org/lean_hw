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

end Machines.Lnp64u.DRel
