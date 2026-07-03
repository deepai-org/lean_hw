import Machines.Lnp64u.Logic.SlotGen
import Machines.Lnp64u.Logic.AcyclicWfa
import Machines.Lnp64u.Logic.Defs

/-!
# Authority domination (T2 support)

Every capability kind in a post-state is dominated (`CapKind.le`) by some
capability kind of the pre-state: the only kind-creating operations are
`cap_dup`/`mem_grant`, whose `narrow` yields a sub-kind of the live parent
(no-wrap guaranteed by `narrow`'s in-memory require), and the transfers,
which move kinds unchanged. `KindsLe` is the `SpecM`-level combinator
(mirroring `SlotGenLe`); `step_dominated` lifts it to the whole `step`.
Together with `AuthorityConfined` this closes T2's `step_confined`.
-/

namespace Machines.Lnp64u

open Loom.Isa SpecM Machines.Lnp64u.Isa

/-- Every capability entry of `σ'` is dominated (`CapKind.le`) by some
capability entry of `σ`. -/
def Dominated (σ σ' : MachineState) : Prop :=
  ∀ d s e', (σ'.doms d).caps s = some e' →
    ∃ d0 s0 e0, (σ.doms d0).caps s0 = some e0 ∧ e'.kind.le e0.kind

theorem Dominated.refl (σ : MachineState) : Dominated σ σ :=
  fun d s e' h => ⟨d, s, e', h, CapKind.le_refl _⟩

theorem Dominated.trans {σ σ₁ σ₂ : MachineState}
    (h1 : Dominated σ σ₁) (h2 : Dominated σ₁ σ₂) : Dominated σ σ₂ := by
  intro d s e' h
  obtain ⟨d1, s1, e1, he1, hle1⟩ := h2 d s e' h
  obtain ⟨d0, s0, e0, he0, hle0⟩ := h1 d1 s1 e1 he1
  exact ⟨d0, s0, e0, he0, CapKind.le_trans hle1 hle0⟩

theorem Dominated.of_caps_eq {σ σ' : MachineState}
    (h : ∀ d s, (σ'.doms d).caps s = (σ.doms d).caps s) : Dominated σ σ' := by
  intro d s e' hc
  rw [h] at hc
  exact ⟨d, s, e', hc, CapKind.le_refl _⟩

/-- A `SpecM` computation only creates dominated capability kinds: on every
`ok`/`err` outcome the post-state is `Dominated` by the pre-state. -/
def KindsLe {α : Type} (mm : SpecM α) : Prop :=
  ∀ σ, (∀ a σ', mm σ = .ok a σ' → Dominated σ σ') ∧
       (∀ e σ', mm σ = .err e σ' → Dominated σ σ')

/-- A computation that leaves `caps` untouched on every outcome creates
nothing. -/
theorem KindsLe.of_preservesCaps {α : Type} (mm : SpecM α)
    (hok : ∀ σ a σ', mm σ = .ok a σ' → ∀ d s, (σ'.doms d).caps s = (σ.doms d).caps s)
    (herr : ∀ σ e σ', mm σ = .err e σ' → ∀ d s, (σ'.doms d).caps s = (σ.doms d).caps s) :
    KindsLe mm :=
  fun σ => ⟨fun a σ' he => Dominated.of_caps_eq (hok σ a σ' he),
            fun e σ' he => Dominated.of_caps_eq (herr σ e σ' he)⟩

theorem KindsLe.pure {α : Type} (a : α) : KindsLe (Pure.pure a : SpecM α) :=
  KindsLe.of_preservesCaps _
    (fun σ a' σ' he d s => by rw [specM_pure] at he; injection he with _ h2; subst h2; rfl)
    (fun σ e σ' he d s => by rw [specM_pure] at he; simp at he)

theorem KindsLe.bind {α β : Type} {m : SpecM α} {f : α → SpecM β}
    (hm : KindsLe m) (hf : ∀ a, KindsLe (f a)) : KindsLe (m >>= f) := by
  intro σ
  refine ⟨?_, ?_⟩
  · intro b σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he
                 exact ((hm σ).1 a σ1 hmσ).trans ((hf a σ1).1 b σ' he)
    | err e σ1 => rw [hmσ] at he; simp at he
    | fault g => rw [hmσ] at he; simp at he
  · intro e σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he
                 exact ((hm σ).1 a σ1 hmσ).trans ((hf a σ1).2 e σ' he)
    | err e1 σ1 => rw [hmσ] at he; injection he with h1 h2; subst h2; exact (hm σ).2 e1 σ1 hmσ
    | fault g => rw [hmσ] at he; simp at he

theorem KindsLe.iteBool {α : Type} (b : Bool) {m1 m2 : SpecM α}
    (h1 : KindsLe m1) (h2 : KindsLe m2) : KindsLe (if b then m1 else m2) := by
  cases b <;> simp only [Bool.false_eq_true, if_true, if_false]
  · exact h2
  · exact h1

theorem KindsLe.reg (d : DomainId) (r : RegId) : KindsLe (SpecM.reg d r) :=
  KindsLe.of_preservesCaps _
    (fun σ a σ' he d s => by unfold SpecM.reg at he; injection he with _ h2; subst h2; rfl)
    (fun σ e σ' he d s => by unfold SpecM.reg at he; simp at he)

theorem KindsLe.load (d : DomainId) (a : Addr) : KindsLe (SpecM.load d a) :=
  KindsLe.of_preservesCaps _
    (fun σ v σ' he d' s => by rw [load_ok d a σ he])
    (fun σ e σ' he d' s => by rw [load_err_state d a σ he])

theorem KindsLe.setReg (d : DomainId) (r : RegId) (v : Loom.Word32) :
    KindsLe (SpecM.setReg d r v) :=
  KindsLe.of_preservesCaps _
    (fun σ a σ' he d' s => by
      unfold SpecM.setReg SpecM.modify at he; injection he with _ h2; subst h2
      unfold MachineState.setDom
      by_cases h : d' = d
      · subst h; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ h])
    (fun σ e σ' he d' s => by unfold SpecM.setReg SpecM.modify at he; simp at he)

/-- An `updDom` whose update leaves `caps` alone creates nothing. -/
theorem KindsLe.updDomCaps (d : DomainId) (f : DomainState → DomainState)
    (hf : ∀ ds, (f ds).caps = ds.caps) : KindsLe (SpecM.updDom d f) := by
  intro σ; refine ⟨?_, ?_⟩
  · intro a σ' he
    simp only [SpecM.updDom, SpecM.modify] at he; injection he with _ h2; subst h2
    refine Dominated.of_caps_eq fun d' s => ?_
    unfold MachineState.setDom
    by_cases h : d' = d
    · subst h; simp [Loom.Fun.update_same, hf]
    · simp [Loom.Fun.update_ne _ _ _ _ h]
  · intro e σ' he; simp [SpecM.updDom, SpecM.modify] at he

theorem KindsLe.updDomPc (d : DomainId) (k : DomainState → Addr) :
    KindsLe (SpecM.updDom d (fun ds => { ds with pc := k ds })) :=
  KindsLe.updDomCaps d _ (fun ds => rfl)

theorem KindsLe.store (d : DomainId) (a : Addr) (v : Loom.Word32) :
    KindsLe (SpecM.store d a v) := by
  intro σ; unfold SpecM.store; refine ⟨?_, ?_⟩
  · intro x σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp only [SpecM.demand, hc, if_true, specM_pure, specM_bind, SpecM.set] at he
      injection he with _ h2; subst h2
      exact Dominated.of_caps_eq fun d' s => rfl
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he
  · intro e σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp [SpecM.demand, hc, specM_pure, specM_bind, SpecM.set] at he
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he

/-- **The base opcodes create no capability kinds.** Their `exec` only
touches regs/pc/memory, never `caps`. -/
theorem base_kinds_le : ∀ instr ∈ base, ∀ c : Ctx, KindsLe (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  · exact KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.setReg _ _ _))
  · exact KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.setReg _ _ _))
  · exact KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.setReg _ _ _))
  · exact KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.setReg _ _ _))
  · exact KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.setReg _ _ _))
  · exact KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.setReg _ _ _))
  · exact KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.setReg _ _ _))
  · exact KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.setReg _ _ _)
  · exact KindsLe.setReg _ _ _
  · exact KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.bind (KindsLe.load _ _) (fun _ => KindsLe.setReg _ _ _))
  · exact KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.store _ _ _))
  · exact KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.iteBool _ (KindsLe.updDomPc _ _) (KindsLe.pure ())))
  · exact KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.bind (KindsLe.reg _ _) (fun _ => KindsLe.iteBool _ (KindsLe.updDomPc _ _) (KindsLe.pure ())))
  · exact KindsLe.bind (KindsLe.reg _ _)
      (fun _ => KindsLe.bind (KindsLe.setReg _ _ _) (fun _ => KindsLe.updDomPc _ _))

/-! ### Kernel-level domination -/

/-- A live capability's entry is in the `caps` table. -/
theorem caps_of_liveCap {ds : DomainState} {s : Slot} {g : Gen} {e : CapEntry}
    (h : ds.liveCap s g = some e) : ds.caps s = some e := by
  unfold DomainState.liveCap at h
  cases hc : ds.caps s with
  | none => simp only [hc] at h; exact h
  | some e0 =>
      simp only [hc] at h
      split at h
      · exact h
      · exact absurd h (by simp)

/-- The kind produced by `narrow` is a sub-authority of the parent kind:
subrange (no-wrap by `narrow`'s in-memory require) with non-escalating
permissions. Extracted here by unfolding `narrow` (the perms require is not
exported by `narrow_ok`). -/
theorem narrow_kind_le (base : Addr) (len : BitVec 13) (perms : Perms) (dw : Loom.Word32)
    (σ : MachineState) {kind : CapKind} {σ' : MachineState}
    (he : Machines.Lnp64u.Isa.narrow base len perms dw σ = .ok kind σ') :
    kind.le (.mem base len perms) := by
  unfold Machines.Lnp64u.Isa.narrow at he
  simp only [SpecM.require, specM_bind, specM_pure] at he
  split_ifs at he with h1 h2 h3 h4
  · injection he with hk hσ
    subst hk
    have hlt : base.toNat + (descOff dw).toNat < memWords := by simpa using h2
    have hmw : memWords = 4096 := rfl
    have hadd : (base + descOff dw).toNat = base.toNat + (descOff dw).toNat := by
      rw [BitVec.toNat_add,
        Nat.mod_eq_of_lt (by omega : base.toNat + (descOff dw).toNat < 2 ^ 12)]
    have hin : (descOff dw).toNat + (descLen dw).toNat ≤ len.toNat := by simpa using h1
    exact ⟨by omega, by omega, h3⟩
  all_goals simp [SpecM.raise] at he

theorem clearSlot_dominated (σ : MachineState) (d : DomainId) (s : Slot) :
    Dominated σ (σ.clearSlot d s) := by
  intro d' s' e' hc
  rw [clearSlot_caps] at hc
  split at hc
  · exact absurd hc (by simp)
  · exact ⟨d', s', e', hc, CapKind.le_refl _⟩

theorem destroyMarked_dominated (σ : MachineState) (mk : DomainId → Slot → Bool) :
    Dominated σ (σ.destroyMarked mk) := by
  intro d' s' e' hc
  rw [destroyMarked_caps] at hc
  split at hc
  · exact absurd hc (by simp)
  · exact ⟨d', s', e', hc, CapKind.le_refl _⟩

@[simp] theorem reparent_caps (σ : MachineState) (old new : CapRef) (d : DomainId) :
    ((σ.reparent old new).doms d).caps = (σ.doms d).caps := rfl

/-- `orphanChildren` only drops lineage indices; kinds are untouched. -/
theorem orphanChildren_dominated (σ : MachineState) (old : CapRef) :
    Dominated σ (σ.orphanChildren old) := by
  intro d' s' e' hc
  rw [orphanChildren_caps] at hc
  cases h0 : (σ.doms d').caps s' with
  | none => simp only [h0] at hc; exact absurd hc (by simp)
  | some e =>
      simp only [h0] at hc
      cases hl : e.lineage with
      | none =>
          simp only [hl] at hc
          injection hc with hc
          exact ⟨d', s', e, h0, by rw [← hc]; exact CapKind.le_refl _⟩
      | some l =>
          simp only [hl] at hc
          injection hc with hc
          refine ⟨d', s', e, h0, ?_⟩
          have hk : e'.kind = e.kind := by
            rw [← hc]
            split <;> first
              | rfl
              | (split <;> rfl)
          rw [hk]
          exact CapKind.le_refl _

/-- `setDom` with a `caps`-preserving update preserves `caps`. -/
theorem setDom_caps_of (σ : MachineState) (dd : DomainId) (f : DomainState → DomainState)
    (hf : (f (σ.doms dd)).caps = (σ.doms dd).caps) (d' : DomainId) (s' : Slot) :
    ((σ.setDom dd f).doms d').caps s' = (σ.doms d').caps s' := by
  unfold MachineState.setDom
  by_cases h : d' = dd
  · subst h; simp [Loom.Fun.update_same, hf]
  · simp [Loom.Fun.update_ne _ _ _ _ h]

theorem haltDom_caps (σ : MachineState) (d : DomainId) (c : Loom.Word32)
    (d' : DomainId) (s : Slot) :
    ((σ.haltDom d c).doms d').caps s = (σ.doms d').caps s := by
  unfold MachineState.haltDom
  split
  · rw [haltBase_caps]
  · split
    · rw [haltBase_caps]
    · rw [unwindGate_caps, haltBase_caps]

/-- `halt`'s exec creates nothing (`haltDom` touches run/serving/gates). -/
theorem KindsLe.halt (c : Ctx) :
    KindsLe (SpecM.modify (fun σ => σ.haltDom c.d 0)) := by
  intro σ; refine ⟨?_, ?_⟩
  · intro a σ' he
    simp only [SpecM.modify, SpecM.set] at he; injection he with _ h2; subst h2
    exact Dominated.of_caps_eq fun d s => haltDom_caps σ c.d 0 d s
  · intro e σ' he; simp [SpecM.modify, SpecM.set] at he

theorem KindsLe.yield (c : Ctx) :
    KindsLe (SpecM.updDom c.d (fun ds => { ds with budget := 0 }) >>=
      fun _ => SpecM.setReg c.d c.op.rd 0) :=
  KindsLe.bind (KindsLe.updDomCaps _ _ (fun ds => rfl)) (fun _ => KindsLe.setReg _ _ _)

theorem KindsLe.unmap (c : Ctx) (ri : RegionId) :
    KindsLe (SpecM.updDom c.d (fun ds => { ds with regions := Loom.Fun.update ds.regions ri none }) >>=
      fun _ => SpecM.setReg c.d c.op.rd 0) :=
  KindsLe.bind (KindsLe.updDomCaps _ _ (fun ds => rfl)) (fun _ => KindsLe.setReg _ _ _)

/-- Installing one dominated entry at a fresh slot of `to_` keeps the state
dominated: the new entry is covered by the witness, everything else by
itself. -/
theorem dominated_setDom_installEntry (σ : MachineState) (to_ : DomainId) (s2 : Slot)
    (ent : CapEntry) (f : DomainState → DomainState)
    (hf : ∀ s', (f (σ.doms to_)).caps s' = Loom.Fun.update (σ.doms to_).caps s2 (some ent) s')
    (hwit : ∃ dw sw ew, (σ.doms dw).caps sw = some ew ∧ ent.kind.le ew.kind) :
    Dominated σ (σ.setDom to_ f) := by
  have hdoms : ∀ d' : DomainId,
      ((σ.setDom to_ f).doms d') = if d' = to_ then f (σ.doms to_) else σ.doms d' := by
    intro d'
    unfold MachineState.setDom
    by_cases h : d' = to_
    · subst h; simp
    · simp [Loom.Fun.update_ne _ _ _ _ h, h]
  intro d' s' e' hc
  rw [hdoms d'] at hc
  by_cases hd : d' = to_
  · rw [if_pos hd] at hc
    rw [hf s'] at hc
    by_cases hs : s' = s2
    · subst hs
      rw [Loom.Fun.update_same] at hc
      injection hc with hc
      obtain ⟨dw, sw, ew, hw, hle⟩ := hwit
      exact ⟨dw, sw, ew, hw, by rw [← hc]; exact hle⟩
    · rw [Loom.Fun.update_ne _ _ _ _ hs] at hc
      exact ⟨to_, s', e', hc, CapKind.le_refl _⟩
  · rw [if_neg hd] at hc
    exact ⟨d', s', e', hc, CapKind.le_refl _⟩

theorem installDerived_dominated (σ : MachineState) (d : DomainId) (s : Slot)
    (l : LineageId) (kind : CapKind) (parent : CapRef)
    (hwit : ∃ dw sw ew, (σ.doms dw).caps sw = some ew ∧ kind.le ew.kind) :
    Dominated σ (σ.installDerived d s l kind parent).1 :=
  dominated_setDom_installEntry σ d s { kind := kind, lineage := some l }
    (fun ds =>
      { ds with
        caps := Loom.Fun.update ds.caps s (some { kind := kind, lineage := some l })
        lineage := Loom.Fun.update ds.lineage l (some { parent := parent }) })
    (fun s' => rfl) hwit

/-- `allocDerived` with a dominated kind keeps the state dominated. -/
theorem allocDerived_dominated (owner : DomainId) (kind : CapKind) (parent : CapRef)
    (σ : MachineState)
    (hwit : ∃ dw sw ew, (σ.doms dw).caps sw = some ew ∧ kind.le ew.kind) :
    (∀ hh τ, Machines.Lnp64u.Isa.allocDerived owner kind parent σ = .ok hh τ → Dominated σ τ) ∧
    (∀ e τ, Machines.Lnp64u.Isa.allocDerived owner kind parent σ = .err e τ → Dominated σ τ) := by
  refine ⟨?_, ?_⟩
  · intro hh τ he
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
            rw [show τ = (σ.installDerived owner sl lc kind parent).1 from by rw [← h2]]
            exact installDerived_dominated σ owner sl lc kind parent hwit
  · intro e τ he
    unfold Machines.Lnp64u.Isa.allocDerived at he
    simp only [SpecM.get, specM_bind] at he
    cases hfs : σ.freeSlot owner with
    | none => rw [hfs] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2
              exact Dominated.refl _
    | some sl =>
        rw [hfs] at he
        cases hfc : σ.freeCell owner with
        | none => rw [hfc] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2
                  exact Dominated.refl _
        | some lc => rw [hfc] at he; simp [SpecM.set, specM_bind, specM_pure] at he

/-- The `cap_drop` kernel core (clearSlot + sweeps) only removes entries. -/
theorem clearSlot_sweeps_dominated (σ : MachineState) (d : DomainId) (s : Slot) :
    Dominated σ ((((σ.clearSlot d s).sweepRegions).sweepMover)) := by
  intro d' s' e' hc
  rw [sweepMover_doms, sweepRegions_caps] at hc
  exact clearSlot_dominated σ d s d' s' e' hc

/-- The `cap_revoke` kernel core (destroyMarked + sweeps) only removes entries. -/
theorem destroyMarked_sweeps_dominated (σ : MachineState) (mk : DomainId → Slot → Bool) :
    Dominated σ ((((σ.destroyMarked mk).sweepRegions).sweepMover)) := by
  intro d' s' e' hc
  rw [sweepMover_doms, sweepRegions_caps] at hc
  exact destroyMarked_dominated σ mk d' s' e' hc

theorem moverPhase_caps (σ : MachineState) (d : DomainId) (s : Slot) :
    ((moverPhase σ).doms d).caps s = (σ.doms d).caps s := by rw [moverPhase_doms]

namespace Wip
open Machines.Lnp64u.Isa Machines.Lnp64u.Isa.Wip

/-- **`transferCap` moves kinds unchanged.** Install-at-recipient copies the
source entry's kind (dominated by the source itself); reparent touches
lineage only; `clearSlot` and the sweeps only remove. -/
theorem transferCap_dominated (σ : MachineState) (from_ : DomainId) (s : Slot) (to_ : DomainId)
    (τ : MachineState) (ref : CapRef) (h : σ.transferCap from_ s to_ = some (τ, ref)) :
    Dominated σ τ := by
  unfold MachineState.transferCap at h
  cases he : (σ.doms from_).caps s with
  | none => rw [he] at h; simp at h
  | some e =>
      rw [he] at h; simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hfs : σ.freeSlot to_ with
      | none => rw [hfs] at h; simp at h
      | some s2 =>
          rw [hfs] at h; simp only [Option.bind_some] at h
          have key : ∀ (σ₁ : MachineState), Dominated σ σ₁ →
              some (((((σ₁.reparent ⟨from_, s, (σ.doms from_).slotGen s⟩
                ⟨to_, s2, (σ.doms to_).slotGen s2⟩).clearSlot from_ s).sweepRegions).sweepMover),
                (⟨to_, s2, (σ.doms to_).slotGen s2⟩ : CapRef))
                = some (τ, ref) →
              Dominated σ τ := by
            intro σ₁ hpre heq
            injection heq with heq; injection heq with hτ _; subst hτ
            refine hpre.trans ?_
            intro d' s' e' hc
            rw [sweepMover_doms, sweepRegions_caps, clearSlot_caps] at hc
            split at hc
            · exact absurd hc (by simp)
            · exact ⟨d', s', e', hc, CapKind.le_refl _⟩
          cases hl : e.lineage with
          | none =>
              rw [hl] at h; simp only [Option.pure_def, Option.bind_some] at h
              refine key (σ.setDom to_ (fun ds =>
                  { ds with caps := Loom.Fun.update ds.caps s2 (some { kind := e.kind, lineage := none }) }))
                ?_ h
              exact dominated_setDom_installEntry σ to_ s2 { kind := e.kind, lineage := none } _
                (fun s' => rfl) ⟨from_, s, e, he, CapKind.le_refl _⟩
          | some l =>
              rw [hl] at h; simp only [Option.bind_eq_bind, Option.bind_some] at h
              cases hcell : (σ.doms from_).lineage l with
              | none => rw [hcell] at h; simp at h
              | some cell =>
                  rw [hcell] at h; simp only [Option.bind_some] at h
                  cases hfc : σ.freeCell to_ with
                  | none => rw [hfc] at h; simp at h
                  | some l' =>
                      rw [hfc] at h; simp only [Option.pure_def, Option.bind_some] at h
                      refine key (σ.setDom to_ (fun ds =>
                          { ds with
                            caps := Loom.Fun.update ds.caps s2 (some { kind := e.kind, lineage := some l' })
                            lineage := Loom.Fun.update ds.lineage l' (some cell) })) ?_ h
                      exact dominated_setDom_installEntry σ to_ s2 { kind := e.kind, lineage := some l' } _
                        (fun s' => rfl) ⟨from_, s, e, he, CapKind.le_refl _⟩

/-- `transferByHandle` moves kinds unchanged: the `hw = 0` and error paths
leave the state alone; the transfer path is `transferCap_dominated`. -/
theorem transferByHandle_kinds_le (d to_ : DomainId) (hw : Loom.Word32) :
    KindsLe (transferByHandle d to_ hw) := by
  intro σ
  unfold Machines.Lnp64u.Isa.transferByHandle
  by_cases hz : hw = 0
  · rw [if_pos hz]
    exact ⟨fun a σ' he => by
        simp only [specM_pure] at he; obtain ⟨_, rfl⟩ := he; exact Dominated.refl _,
      fun e σ' he => by simp [specM_pure] at he⟩
  · simp only [if_neg hz, specM_bind]
    constructor
    · intro a σ' he
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
              exact transferCap_dominated σ d sslot to_ σ2 ref htc
    · intro er σ' he
      cases hcl : capLive d hw σ with
      | err e0 σ0 =>
          have hs := capLive_err_state d _ σ hcl; rw [hcl] at he
          injection he with _ h2; subst h2; subst hs; exact Dominated.refl _
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := capLive_ok d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sslot, gg, ee⟩ := r
          simp only [SpecM.get, specM_bind] at he
          cases htc : σ.transferCap d sslot to_ with
          | none =>
              rw [htc] at he; simp only [SpecM.raise] at he
              injection he with _ h2; subst h2; exact Dominated.refl _
          | some pr =>
              obtain ⟨σ2, ref⟩ := pr
              rw [htc] at he; simp [SpecM.set, specM_bind, specM_pure] at he

/-- `move` creates nothing: it only programs the Mover and writes `rd`. -/
theorem move_kinds_le (c : Ctx) : KindsLe (moveExec c) := by
  intro σ; refine ⟨fun x σ' he => ?_, fun x σ' he => ?_⟩
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
                                                        refine Dominated.of_caps_eq fun d' s => ?_
                                                        unfold MachineState.setDom
                                                        by_cases hdc : d' = c.d
                                                        · subst hdc; simp [Loom.Fun.update_same]
                                                        · simp [Loom.Fun.update_ne _ _ _ _ hdc]
  ·
    simp only [moveExec, SpecM.get, specM_bind] at he
    cases hr0 : SpecM.require σ.mover.isNone .moverBusy σ with
    | err e0 σ0 => have hq := require_err_state _ _ σ hr0; rw [hr0] at he; injection he with _ h2; subst h2; subst hq; exact Dominated.refl _
    | fault f => rw [hr0] at he; simp at he
    | ok u0 σ0 =>
        have hh0 := require_ok _ _ σ hr0; subst σ0
        rw [hr0] at he; simp only [SpecM.reg] at he
        set B : Addr := ((σ.doms c.d).reg c.op.rs1).setWidth 12 with hB
        cases hl1 : load c.d B σ with
        | err e σe => have hq := load_err_state _ _ σ hl1; rw [hl1] at he; injection he with _ h2; subst h2; subst hq; exact Dominated.refl _
        | fault f => rw [hl1] at he; simp at he
        | ok srcH σ1 =>
            have hh1 := load_ok _ _ σ hl1; subst σ1; rw [hl1] at he; simp only [specM_bind] at he
            cases hl2 : load c.d (B + 1) σ with
            | err e σe => have hq := load_err_state _ _ σ hl2; rw [hl2] at he; injection he with _ h2; subst h2; subst hq; exact Dominated.refl _
            | fault f => rw [hl2] at he; simp at he
            | ok dstH σ2 =>
                have hh2 := load_ok _ _ σ hl2; subst σ2; rw [hl2] at he; simp only [specM_bind] at he
                cases hl3 : load c.d (B + 2) σ with
                | err e σe => have hq := load_err_state _ _ σ hl3; rw [hl3] at he; injection he with _ h2; subst h2; subst hq; exact Dominated.refl _
                | fault f => rw [hl3] at he; simp at he
                | ok lenW σ3 =>
                    have hh3 := load_ok _ _ σ hl3; subst σ3; rw [hl3] at he; simp only [specM_bind] at he
                    cases hl4 : load c.d (B + 3) σ with
                    | err e σe => have hq := load_err_state _ _ σ hl4; rw [hl4] at he; injection he with _ h2; subst h2; subst hq; exact Dominated.refl _
                    | fault f => rw [hl4] at he; simp at he
                    | ok stW σ4 =>
                        have hh4 := load_ok _ _ σ hl4; subst σ4; rw [hl4] at he; simp only [specM_bind] at he
                        cases hc1 : capLive c.d srcH σ with
                        | err e σe => have hq := capLive_err_state c.d _ σ hc1; rw [hc1] at he; injection he with _ h2; subst h2; subst hq; exact Dominated.refl _
                        | fault f => rw [hc1] at he; simp at he
                        | ok rs σ5 =>
                            have hcs := capLive_ok c.d _ σ hc1; obtain ⟨hhs, hslive⟩ := hcs; subst σ5
                            rw [hc1] at he; obtain ⟨ss, gs_, es⟩ := rs; simp only at he hslive
                            cases hc2 : capLive c.d dstH σ with
                            | err e σe => have hq := capLive_err_state c.d _ σ hc2; rw [hc2] at he; injection he with _ h2; subst h2; subst hq; exact Dominated.refl _
                            | fault f => rw [hc2] at he; simp at he
                            | ok rdd σ6 =>
                                have hcd := capLive_ok c.d _ σ hc2; obtain ⟨hhd, hdlive⟩ := hcd; subst σ6
                                rw [hc2] at he; obtain ⟨sd, gd, ed⟩ := rdd; simp only at he hdlive
                                cases hks : es.kind with
                                | gate _ => rw [hks] at he; cases hkd : ed.kind with
                                            | gate _ => rw [hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact Dominated.refl _
                                            | mem _ _ _ => rw [hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact Dominated.refl _
                                | mem sb sl sp =>
                                    cases hkd : ed.kind with
                                    | gate _ => rw [hks, hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact Dominated.refl _
                                    | mem db dl dp =>
                                        rw [hks, hkd] at he; simp only [specM_bind] at he
                                        cases hq1 : SpecM.require sp.r .permDenied σ with
                                        | err e σe => have hq := require_err_state _ _ σ hq1; rw [hq1] at he; injection he with _ h2; subst h2; subst hq; exact Dominated.refl _
                                        | fault f => rw [hq1] at he; simp at he
                                        | ok _ σq1 =>
                                            have := require_ok _ _ σ hq1; subst σq1; rw [hq1] at he; simp only [specM_bind] at he
                                            cases hq2 : SpecM.require dp.w .permDenied σ with
                                            | err e σe => have hq := require_err_state _ _ σ hq2; rw [hq2] at he; injection he with _ h2; subst h2; subst hq; exact Dominated.refl _
                                            | fault f => rw [hq2] at he; simp at he
                                            | ok _ σq2 =>
                                                have := require_ok _ _ σ hq2; subst σq2; rw [hq2] at he; simp only [specM_bind] at he
                                                cases hq3 : SpecM.require (decide (lenW.toNat ≤ sl.toNat) && decide (lenW.toNat ≤ dl.toNat)) .outOfRange σ with
                                                | err e σe => have hq := require_err_state _ _ σ hq3; rw [hq3] at he; injection he with _ h2; subst h2; subst hq; exact Dominated.refl _
                                                | fault f => rw [hq3] at he; simp at he
                                                | ok _ σq3 =>
                                                    have := require_ok _ _ σ hq3; subst σq3; rw [hq3] at he; simp only [SpecM.get, specM_bind] at he
                                                    cases hd : SpecM.demand (σ.domCovers c.d (stW.setWidth 12) { r := false, w := true, x := false }) .memoryAuthority σ with
                                                    | err e σe => exact absurd hd (by simp [SpecM.demand]; split <;> simp [SpecM.fatal])
                                                    | fault f => rw [hd] at he; simp at he
                                                    | ok _ σdd =>
                                                        have := demand_ok _ _ σ hd; subst σdd; rw [hd] at he
                                                        simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he

/-- `gate_call` creates nothing: the only caps-touching piece is the argument
transfer (`transferByHandle_kinds_le`); the activation / serving / run
bookkeeping leaves `caps` alone. -/
theorem gatecall_kinds_le (c : Ctx) : KindsLe (gateCallExec c) := by
  intro σ
  have body : ∀ (out : Res Unit), gateCallExec c σ = out →
      (∀ a σ', out = .ok a σ' → Dominated σ σ') ∧
      (∀ e σ', out = .err e σ' → Dominated σ σ') := by
    intro out hout
    unfold gateCallExec at hout
    simp only [SpecM.reg, specM_bind] at hout
    cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 =>
        have hs := capLive_err_state c.d _ σ hcl; rw [hcl] at hout; subst hout
        exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
          simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hs
          exact Dominated.refl _⟩
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
              exact Dominated.refl _⟩
        | gate gid =>
            rw [hk] at hout; simp only [SpecM.get, specM_bind] at hout
            set cal := (σ.gates gid).config.callee with hcaldef
            cases hr1 : SpecM.require (σ.gates gid).act.isNone .gateBusy σ with
            | err e1 σ1 => have hst := require_err_state _ _ σ hr1; rw [hr1] at hout; simp only [specM_bind] at hout; subst hout
                           exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                             simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; exact Dominated.refl _⟩
            | fault f => rw [hr1] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
            | ok u1 σ1 =>
                have hst := require_ok _ _ σ hr1; subst σ1
                rw [hr1] at hout; simp only [specM_bind] at hout
                cases hr2 : SpecM.require (decide (cal ≠ c.d)) .gateBusy σ with
                | err e2 σ2 => have hst := require_err_state _ _ σ hr2; rw [hr2] at hout; simp only [specM_bind] at hout; subst hout
                               exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                 simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; exact Dominated.refl _⟩
                | fault f => rw [hr2] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                | ok u2 σ2 =>
                    have hst := require_ok _ _ σ hr2; subst σ2
                    rw [hr2] at hout; simp only [specM_bind] at hout
                    cases hr3 : SpecM.require (decide ((σ.doms cal).run = .running)) .gateBusy σ with
                    | err e3 σ3 => have hst := require_err_state _ _ σ hr3; rw [hr3] at hout; simp only [specM_bind] at hout; subst hout
                                   exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                     simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; exact Dominated.refl _⟩
                    | fault f => rw [hr3] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                    | ok u3 σ3 =>
                        have hst := require_ok _ _ σ hr3; subst σ3
                        rw [hr3] at hout; simp only [specM_bind] at hout
                        cases hr4 : SpecM.require (σ.doms cal).serving.isNone .gateBusy σ with
                        | err e4 σ4 => have hst := require_err_state _ _ σ hr4; rw [hr4] at hout; simp only [specM_bind] at hout; subst hout
                                       exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                         simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; exact Dominated.refl _⟩
                        | fault f => rw [hr4] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                        | ok u4 σ4 =>
                            have hst := require_ok _ _ σ hr4; subst σ4
                            rw [hr4] at hout; simp only [specM_bind] at hout
                            cases hr5 : SpecM.require (decide (gateDepth c σ ≤ maxChainDepth)) .gateBusy σ with
                            | err e5 σ5 => have hst := require_err_state _ _ σ hr5; rw [hr5] at hout; simp only [specM_bind] at hout; subst hout
                                           exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                             simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; exact Dominated.refl _⟩
                            | fault f => rw [hr5] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                            | ok u5 σ5 =>
                                have hst := require_ok _ _ σ hr5; subst σ5
                                rw [hr5] at hout; simp only [specM_bind, SpecM.reg] at hout
                                cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d cal ((σ.doms c.d).reg c.op.rs2) σ with
                                | fault f => rw [htbh] at hout; subst hout
                                             exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                                | err e6 τ =>
                                    rw [htbh] at hout; subst hout
                                    have hτ := (transferByHandle_kinds_le c.d cal _ σ).2 e6 τ htbh
                                    exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                      simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hτ⟩
                                | ok argHandle τ =>
                                    rw [htbh] at hout
                                    have hτ := (transferByHandle_kinds_le c.d cal _ σ).1 argHandle τ htbh
                                    simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom, SpecM.modify] at hout
                                    subst hout
                                    refine ⟨fun a σ' h => ?_, fun e σ' h => by simp at h⟩
                                    simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                                    refine hτ.trans (Dominated.of_caps_eq fun d' s => ?_)
                                    rw [setDom_caps_of _ c.d _ rfl, setDom_caps_of _ cal _ rfl]
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun e σ' h => (body _ h).2 e σ' rfl⟩

/-- `gate_return` creates nothing: the only caps-touching piece is the reply
transfer; restoring the caller's context leaves `caps` alone. -/
theorem gatereturn_kinds_le (c : Ctx) :
    KindsLe ((do
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
      (∀ a σ', out = .ok a σ' → Dominated σ σ') ∧
      (∀ e σ', out = .err e σ' → Dominated σ σ') := by
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
                have hτ := (transferByHandle_kinds_le c.d act.caller _ σ).2 e1 τ htbh
                exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                  simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hτ⟩
            | ok reply τ =>
                rw [htbh] at hout
                have hτ := (transferByHandle_kinds_le c.d act.caller _ σ).1 reply τ htbh
                simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom, SpecM.modify,
                           SpecM.setReg] at hout
                subst hout
                refine ⟨fun a σ' h => ?_, fun e σ' h => by simp at h⟩
                simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                refine hτ.trans (Dominated.of_caps_eq fun d' s => ?_)
                rw [setDom_caps_of _ act.caller _ (setReg_caps _ _ _),
                    setDom_caps_of _ act.caller _ rfl,
                    setDom_caps_of _ c.d _ rfl]
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun e σ' h => (body _ h).2 e σ' rfl⟩

/-- **The system opcodes create only dominated kinds** (dup/grant via the
narrowed live parent, gates via the unchanged-kind transfer, drop/revoke
only remove, the rest never touch `caps`). -/
theorem system_kinds_le : ∀ instr ∈ Machines.Lnp64u.Isa.system, ∀ c : Ctx,
    KindsLe (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  case _ => -- cap_dup
    intro σ; constructor
    · intro a σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, hlive⟩ := capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he hlive
          have hcaps : (σ.doms c.d).caps sl = some e := caps_of_liveCap hlive
          have hstep : ∀ (kd : CapKind), kd.le e.kind → ∀ (hh : Loom.Word32) (τ : MachineState),
              allocDerived c.d kd ⟨c.d, sl, gg⟩ σ = .ok hh τ →
              (SpecM.setReg c.d c.op.rd hh) τ = .ok a σ' →
              Dominated σ σ' := by
            intro kd hkd hh τ hal hsr
            have h1 := (allocDerived_dominated c.d kd ⟨c.d, sl, gg⟩ σ
              ⟨c.d, sl, e, hcaps, hkd⟩).1 hh τ hal
            have h2 := (KindsLe.setReg c.d c.op.rd hh τ).1 a σ' hsr
            exact h1.trans h2
          cases hk : e.kind with
          | gate g =>
              rw [hk] at he; simp only [specM_pure, specM_bind] at he
              cases hal : allocDerived c.d (.gate g) ⟨c.d, sl, gg⟩ σ with
              | err e1 σ1 => rw [hal] at he; simp at he
              | fault f => rw [hal] at he; simp at he
              | ok hh τ => rw [hal] at he
                           exact hstep _ (by rw [hk]; exact CapKind.le_refl _) hh τ hal he
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => rw [hn] at he; simp at he
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : allocDerived c.d kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => rw [hal] at he; simp at he
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ =>
                      rw [hal] at he
                      exact hstep _ (by rw [hk]; exact narrow_kind_le base len perms _ σ hn)
                        hh τ hal he
    · intro e σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs
                     exact Dominated.refl _
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g =>
              rw [hk] at he; simp only [specM_pure, specM_bind] at he
              cases hal : allocDerived c.d (.gate g) ⟨c.d, sl, gg⟩ σ with
              | err e1 σ1 => have hs := allocDerived_err_state c.d _ _ σ hal
                             rw [hal] at he; injection he with _ h2; subst h2; subst hs
                             exact Dominated.refl _
              | fault f => rw [hal] at he; simp at he
              | ok hh τ => rw [hal] at he; simp [SpecM.setReg, SpecM.modify] at he
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => have hs := narrow_err_state base len perms _ σ hn
                             rw [hn] at he; injection he with _ h2; subst h2; subst hs
                             exact Dominated.refl _
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : allocDerived c.d kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => have hs := allocDerived_err_state c.d _ _ σ hal
                                 rw [hal] at he; injection he with _ h2; subst h2; subst hs
                                 exact Dominated.refl _
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ => rw [hal] at he; simp [SpecM.setReg, SpecM.modify] at he
  case _ => -- cap_drop
    intro σ; constructor
    · intro a σ'' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, _⟩ := r; simp only at he
          simp only [SpecM.get, specM_bind] at he
          have key : ∀ (σ' : MachineState), Dominated σ σ' →
              (SpecM.set (((σ'.clearSlot c.d sl).sweepRegions).sweepMover) >>=
                fun _ => SpecM.setReg c.d c.op.rd 0) σ = .ok a σ'' →
              Dominated σ σ'' := by
            intro σ' hpre hset
            simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at hset
            injection hset with _ h2; subst h2
            exact (hpre.trans (clearSlot_sweeps_dominated σ' c.d sl)).trans
              (Dominated.of_caps_eq fun d' s =>
                setDom_caps_of _ c.d _ (setReg_caps _ _ _) d' s)
          cases hp : σ.parentOf c.d sl with
          | some p =>
              rw [hp] at he
              refine key _ ?_ he
              exact Dominated.of_caps_eq fun d' s => rfl
          | none =>
              rw [hp] at he
              refine key _ ?_ he
              exact orphanChildren_dominated σ _
    · intro e σ'' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs
                     exact Dominated.refl _
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, _⟩ := r; simp only at he
          simp only [SpecM.get, specM_bind] at he
          cases hp : σ.parentOf c.d sl with
          | some p => rw [hp] at he; simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
          | none => rw [hp] at he; simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
  case _ => -- cap_revoke
    intro σ; constructor
    · intro a σ'' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          simp only [SpecM.require] at he
          by_cases hcls : decide (e.kind.cls = .mem) = true
          · simp only [hcls, if_true, specM_pure, specM_bind, SpecM.get] at he
            simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
            injection he with _ h2; subst h2
            exact (destroyMarked_sweeps_dominated σ (σ.marks ⟨c.d, sl, gg⟩)).trans
              (Dominated.of_caps_eq fun d' s =>
                setDom_caps_of _ c.d _ (setReg_caps _ _ _) d' s)
          · rw [if_neg hcls] at he; simp [SpecM.raise, specM_bind] at he
    · intro e σ'' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs
                     exact Dominated.refl _
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          simp only [SpecM.require] at he
          by_cases hcls : decide (e.kind.cls = .mem) = true
          · simp only [hcls, if_true, specM_pure, specM_bind, SpecM.get] at he
            simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
          · rw [if_neg hcls] at he; simp only [SpecM.raise, specM_bind] at he
            injection he with _ h2; subst h2; exact Dominated.refl _
  case _ => -- mem_grant
    intro σ; constructor
    · intro a σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, hlive⟩ := capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he hlive
          have hcaps : (σ.doms c.d).caps sl = some e := caps_of_liveCap hlive
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp [SpecM.raise] at he
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => rw [hn] at he; simp at he
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : allocDerived (descDom ((σ.doms c.d).reg c.op.rs2)) kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => rw [hal] at he; simp at he
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ =>
                      rw [hal] at he
                      have hkd : kd.le e.kind := by
                        rw [hk]; exact narrow_kind_le base len perms _ σ hn
                      have h1 := (allocDerived_dominated (descDom ((σ.doms c.d).reg c.op.rs2))
                        kd ⟨c.d, sl, gg⟩ σ ⟨c.d, sl, e, hcaps, hkd⟩).1 hh τ hal
                      have h2 := (KindsLe.setReg c.d c.op.rd hh τ).1 a σ' he
                      exact h1.trans h2
    · intro e σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs
                     exact Dominated.refl _
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp only [SpecM.raise] at he
                      injection he with _ h2; subst h2; exact Dominated.refl _
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => have hs := narrow_err_state base len perms _ σ hn
                             rw [hn] at he; injection he with _ h2; subst h2; subst hs
                             exact Dominated.refl _
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : allocDerived (descDom ((σ.doms c.d).reg c.op.rs2)) kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => have hs := allocDerived_err_state (descDom _) _ _ σ hal
                                 rw [hal] at he; injection he with _ h2; subst h2; subst hs
                                 exact Dominated.refl _
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ => rw [hal] at he; simp [SpecM.setReg, SpecM.modify] at he
  case _ => -- map
    intro σ; constructor
    · intro a σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp [SpecM.raise] at he
          | mem base len perms =>
              rw [hk] at he
              simp only [SpecM.updDom, SpecM.modify, SpecM.setReg, specM_bind, SpecM.set] at he
              injection he with _ h2; subst h2
              refine Dominated.of_caps_eq fun d' s => ?_
              unfold MachineState.setDom
              by_cases h1 : d' = c.d
              · subst h1; simp [Loom.Fun.update_same]
              · simp [Loom.Fun.update_ne _ _ _ _ h1]
    · intro e σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs
                     exact Dominated.refl _
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp only [SpecM.raise] at he
                      injection he with _ h2; subst h2; exact Dominated.refl _
          | mem base len perms =>
              rw [hk] at he
              simp [SpecM.updDom, SpecM.modify, SpecM.setReg, specM_bind, SpecM.set] at he
  case _ => exact KindsLe.unmap c _
  case _ => exact gatecall_kinds_le c
  case _ => exact gatereturn_kinds_le c
  case _ => exact move_kinds_le c
  case _ => exact KindsLe.yield c
  case _ => exact KindsLe.halt c

/-- **Every instruction's exec creates only dominated kinds** — the base
combinator dispatch plus the 11 system-op cases. -/
theorem exec_kinds_le : ∀ instr ∈ isa, ∀ c : Ctx, KindsLe (instr.sem.exec c) := by
  intro instr hmem c
  have hmem' : instr ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
    have hiseq : Machines.Lnp64u.isa =
      (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray := rfl
    rw [hiseq, Array.mem_toArray] at hmem; exact hmem
  rcases List.mem_append.mp hmem' with hb | hs
  · exact base_kinds_le instr hb c
  · exact system_kinds_le instr hs c

/-- `retire` creates only dominated kinds: the pc bump and the errno
write-back preserve `caps`; halts preserve; the instruction effect is
`exec_kinds_le`. -/
theorem retire_dominated (σ : MachineState) (d : DomainId) (w : Loom.Word32) :
    Dominated σ (retire σ d w) := by
  unfold retire
  split
  · exact Dominated.of_caps_eq fun d' s => haltDom_caps σ d _ d' s
  · rename_i instr hdec
    have h1 : Dominated σ (σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })) :=
      Dominated.of_caps_eq fun d' s => setDom_caps_of σ d _ rfl d' s
    have hex := exec_kinds_le instr (Loom.Isa.decode_mem isa hdec)
      { d := d, pc := (σ.doms d).pc, op := operandsOf w }
      (σ.setDom d (fun ds => { ds with pc := ds.pc + 1 }))
    cases hexr : instr.sem.exec { d := d, pc := (σ.doms d).pc, op := operandsOf w }
        (σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })) with
    | ok a σ' =>
        simp only [hexr]
        exact h1.trans (hex.1 a σ' hexr)
    | err e σ' =>
        simp only [hexr]
        exact (h1.trans (hex.2 e σ' hexr)).trans
          (Dominated.of_caps_eq fun d' s => setDom_caps_of σ' d _ (setReg_caps _ _ _) d' s)
    | fault f =>
        simp only [hexr]
        exact Dominated.of_caps_eq fun d' s => haltDom_caps σ d _ d' s

/-- `corePhase` creates only dominated kinds: countdown/stall/issue leave
`caps` alone; retirement is `retire_dominated`; halts preserve. -/
theorem corePhase_dominated (m : Manifest) (σ : MachineState) :
    Dominated σ (corePhase m σ) := by
  unfold corePhase
  cases hinf : σ.inflight with
  | some fl =>
      by_cases hc : fl.cyclesLeft ≤ 1
      · simp only [hc, if_true]
        exact retire_dominated { σ with inflight := none } fl.dom fl.word
      · simp only [hc, if_false]
        exact Dominated.of_caps_eq fun d s => rfl
  | none =>
      simp only []
      split
      · exact Dominated.refl _
      · rename_i d hsched
        split
        · exact Dominated.of_caps_eq fun d' s => haltDom_caps σ d _ d' s
        · rename_i w hfetch
          split
          · exact Dominated.of_caps_eq fun d' s => haltDom_caps σ d _ d' s
          · rename_i instr hdec
            by_cases hbud : instr.cost.cost ≤ (σ.doms (σ.payer d)).budget
            · simp only [hbud, if_true]
              cases hserv : (σ.doms d).serving with
              | none =>
                  simp only [hserv]
                  exact Dominated.of_caps_eq fun d' s =>
                    setDom_caps_of σ (σ.payer d)
                      (fun ds => { ds with budget := ds.budget - instr.cost.cost }) rfl d' s
              | some g =>
                  simp only [hserv]
                  cases hact : (σ.gates g).act with
                  | none => exact Dominated.of_caps_eq fun d' s => haltDom_caps σ d _ d' s
                  | some a =>
                      simp only [hact]
                      by_cases hdon : instr.cost.cost ≤ a.donated
                      · simp only [hdon, if_true]
                        exact Dominated.of_caps_eq fun d' s =>
                          setDom_caps_of σ (σ.payer d)
                            (fun ds => { ds with budget := ds.budget - instr.cost.cost }) rfl d' s
                      · simp only [hdon, if_false]
                        exact Dominated.of_caps_eq fun d' s => haltDom_caps σ d _ d' s
            · simp only [hbud, if_false]; exact Dominated.refl _

/-- `step`'s caps equal `corePhase`'s (refill and the cycle bump leave `caps`
untouched; `moverPhase` leaves all domains untouched). -/
theorem step_caps_reduce (m : Manifest) (σ : MachineState) (d : DomainId) (s : Slot) :
    ((step m σ).doms d).caps s = ((corePhase m (refillPhase m σ)).doms d).caps s := by
  unfold step; simp only [moverPhase_caps]

/-- **One cycle only creates dominated capability kinds** — the `step`-level
bound feeding T2's `step_confined`. -/
theorem step_dominated (m : Manifest) (σ : MachineState) : Dominated σ (step m σ) := by
  have h0 : Dominated σ (refillPhase m σ) :=
    Dominated.of_caps_eq fun d s => congrFun (refillPhase_caps m σ d) s
  refine h0.trans ?_
  intro d s e' hc
  rw [step_caps_reduce] at hc
  exact corePhase_dominated m (refillPhase m σ) d s e' hc

end Wip

end Machines.Lnp64u
