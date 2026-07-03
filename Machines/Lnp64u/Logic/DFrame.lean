import Machines.Lnp64u.Logic.GateStep
import Machines.Lnp64u.Logic.Inflight
import Machines.Lnp64u.Logic.Authority
import Machines.Lnp64u.Logic.Tombstone

/-!
# The d-slice frame sweep (T5 support)

The unary per-instruction sweep behind `NonInt.insulated_step` and
`NonInt.frame_step`: a cycle executed by a domain `cd ≠ d` (with `d`
insulated in the sense of the `DCtx` hypothesis bundle below) leaves `d`'s
whole domain record, the memory under `d`'s roots (`R`), the gate
configurations, and the machine-wide ownership/foreignness facts intact.

Everything is parametrized by an abstract address set `R : Addr → Prop`
(instantiated with `NonInt.UnderRoots m d`), so this file needs none of the
manifest-level vocabulary of `NonInt.lean`.

Structure mirrors the seven worked sweeps (`SlotGen`/`Budget`/`Inflight`/
`Authority`/`Tombstone`/`GateStep`/`Hostage`): kernel-function frame
lemmas, a `SpecM` combinator kit (`DKLe`), the base-op sweep, and one
monolithic lemma per system op.
-/

namespace Machines.Lnp64u.DFrame

open Machines.Lnp64u Loom SpecM

/-! ## Vocabulary -/

/-- Foreign capability ranges avoid `R` (the `Insulated.foreign_off` clause
with `UnderRoots` abstracted). -/
def ForeignOff (d : DomainId) (R : Addr → Prop) (σ : MachineState) : Prop :=
  ∀ e, e ≠ d → ∀ s entry b l p, (σ.doms e).caps s = some entry →
    entry.kind = .mem b l p → ∀ a : Addr, b.toNat ≤ a.toNat →
    a.toNat < b.toNat + l.toNat → ¬ R a

/-- Every region register is backed by a capability of its own domain. -/
def RegionsOwn (σ : MachineState) : Prop :=
  ∀ e r rg, (σ.doms e).regions r = some rg → rg.backing.dom = e

/-- The pre-state context of the sweep: everything the per-op arguments
consume, stated so that it transports across the sweep's own output
(`DCtx.transport`). All clauses are facts about `σ` alone. -/
structure DCtx (d : DomainId) (R : Addr → Prop) (σ : MachineState) : Prop where
  /-- `d`'s capability table is full (grants into `d` find no free slot). -/
  dfull : ∀ s, (σ.doms d).caps s ≠ none
  /-- `d` owns no lineage cells (boot roots only). -/
  dlin : ∀ l, (σ.doms d).lineage l = none
  /-- `d`'s entries are roots (`lineage = none`). -/
  dent : ∀ s e, (σ.doms d).caps s = some e → e.lineage = none
  /-- `d` holds no gate capabilities. -/
  dgates : ∀ s e g, (σ.doms d).caps s = some e → e.kind ≠ .gate g
  dserv : (σ.doms d).serving = none
  dnoblk : ∀ g, (σ.doms d).run ≠ .blocked g
  /-- `d`'s region registers cache `d`'s own live capabilities. -/
  dreg : ∀ r rg, (σ.doms d).regions r = some rg → rg.backing.dom = d ∧
    ((σ.doms d).liveCap rg.backing.slot rg.backing.gen).isSome
  ro : RegionsOwn σ
  fo : ForeignOff d R σ
  /-- A covered access by any `e ≠ d` misses `R`. -/
  covOff : ∀ e, e ≠ d → ∀ a need, σ.domCovers e a need = true → ¬ R a
  movOff : ∀ job, σ.mover = some job → job.owner ≠ d
  ncallee : ∀ g, (σ.gates g).config.callee ≠ d
  acaller : ∀ g a, (σ.gates g).act = some a → a.caller ≠ d

/-- The sweep's output: what one `cd`-transition preserves. -/
structure DKeep (d cd : DomainId) (R : Addr → Prop) (σ σ' : MachineState) : Prop where
  ddoms : σ'.doms d = σ.doms d
  mem : ∀ a, R a → σ'.mem a = σ.mem a
  gcfg : ∀ g, (σ'.gates g).config = (σ.gates g).config
  /-- New gate activations are created only by the executing domain. -/
  acts : ∀ g a, (σ'.gates g).act = some a → (σ.gates g).act = some a ∨ a.caller = cd
  /-- New Mover jobs are created only by the executing domain. -/
  mover : ∀ job, σ'.mover = some job → σ.mover = some job ∨ job.owner = cd
  ro : RegionsOwn σ'
  fo : ForeignOff d R σ'
  /-- Foreign region registers are either inherited or cover only non-`R`
  addresses (fresh `map`s cache foreign capabilities, which avoid `R`). -/
  regR : ∀ e, e ≠ d → ∀ r rg, (σ'.doms e).regions r = some rg →
    (σ.doms e).regions r = some rg ∨
    ∀ a : Addr, rg.base.toNat ≤ a.toNat →
      a.toNat < rg.base.toNat + rg.len.toNat → ¬ R a

theorem DKeep.refl {d cd : DomainId} {R : Addr → Prop} {σ : MachineState}
    (hro : RegionsOwn σ) (hfo : ForeignOff d R σ) : DKeep d cd R σ σ :=
  ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ h => Or.inl h, fun _ h => Or.inl h,
   hro, hfo, fun _ _ _ _ h => Or.inl h⟩

theorem DKeep.of_eq {d cd : DomainId} {R : Addr → Prop} {σ σ' : MachineState}
    (h : σ' = σ) (hro : RegionsOwn σ) (hfo : ForeignOff d R σ) :
    DKeep d cd R σ σ' := by rw [h]; exact DKeep.refl hro hfo

theorem DKeep.trans {d cd : DomainId} {R : Addr → Prop} {σ σ₁ σ₂ : MachineState}
    (h1 : DKeep d cd R σ σ₁) (h2 : DKeep d cd R σ₁ σ₂) : DKeep d cd R σ σ₂ where
  ddoms := h2.ddoms.trans h1.ddoms
  mem := fun a ha => (h2.mem a ha).trans (h1.mem a ha)
  gcfg := fun g => (h2.gcfg g).trans (h1.gcfg g)
  acts := fun g a h => by
    rcases h2.acts g a h with h' | h'
    · exact h1.acts g a h'
    · exact Or.inr h'
  mover := fun job h => by
    rcases h2.mover job h with h' | h'
    · exact h1.mover job h'
    · exact Or.inr h'
  ro := h2.ro
  fo := h2.fo
  regR := fun e he r rg h => by
    rcases h2.regR e he r rg h with h' | h'
    · exact h1.regR e he r rg h'
    · exact Or.inr h'

/-- The context transports along the sweep's own output. -/
theorem DCtx.transport {d cd : DomainId} {R : Addr → Prop} {σ σ' : MachineState}
    (hctx : DCtx d R σ) (hne : cd ≠ d) (hk : DKeep d cd R σ σ') :
    DCtx d R σ' where
  dfull := fun s => by rw [hk.ddoms]; exact hctx.dfull s
  dlin := fun l => by rw [hk.ddoms]; exact hctx.dlin l
  dent := fun s e h => hctx.dent s e (by rw [← hk.ddoms]; exact h)
  dgates := fun s e g h => hctx.dgates s e g (by rw [← hk.ddoms]; exact h)
  dserv := by rw [hk.ddoms]; exact hctx.dserv
  dnoblk := fun g => by rw [hk.ddoms]; exact hctx.dnoblk g
  dreg := fun r rg h => by
    rw [hk.ddoms] at h ⊢
    exact hctx.dreg r rg h
  ro := hk.ro
  fo := hk.fo
  covOff := fun e he a need hcov => by
    unfold MachineState.domCovers at hcov
    rw [decide_eq_true_iff] at hcov
    obtain ⟨r, rg, hrg, hc⟩ := hcov
    unfold Region.covers at hc
    simp only [Bool.and_eq_true, decide_eq_true_iff] at hc
    rcases hk.regR e he r rg hrg with hold | hoff
    · refine hctx.covOff e he a need ?_
      unfold MachineState.domCovers
      rw [decide_eq_true_iff]
      refine ⟨r, rg, hold, ?_⟩
      unfold Region.covers
      simp only [Bool.and_eq_true, decide_eq_true_iff]
      exact hc
    · exact hoff a hc.1.1 hc.1.2
  movOff := fun job h => by
    rcases hk.mover job h with h' | h'
    · exact hctx.movOff job h'
    · rw [h']; exact hne
  ncallee := fun g => by rw [hk.gcfg]; exact hctx.ncallee g
  acaller := fun g a h => by
    rcases hk.acts g a h with h' | h'
    · exact hctx.acaller g a h'
    · rw [h']; exact hne

/-! ## Record-rebuild helpers (structure eta) -/

theorem setLineage_self (ds : DomainState) (f : LineageId → Option LineageCell)
    (hf : f = ds.lineage) : ({ ds with lineage := f } : DomainState) = ds := by
  rw [hf]

theorem setCapsLineage_self (ds : DomainState) (fc : Slot → Option CapEntry)
    (fl : LineageId → Option LineageCell)
    (hfc : fc = ds.caps) (hfl : fl = ds.lineage) :
    ({ ds with caps := fc, lineage := fl } : DomainState) = ds := by
  rw [hfc, hfl]

theorem setRegions_self (ds : DomainState) (f : RegionId → Option Region)
    (hf : f = ds.regions) : ({ ds with regions := f } : DomainState) = ds := by
  rw [hf]

theorem setCapsLineageGen_self (ds : DomainState) (fc : Slot → Option CapEntry)
    (fl : LineageId → Option LineageCell) (fg : Slot → Gen)
    (hfc : fc = ds.caps) (hfl : fl = ds.lineage) (hfg : fg = ds.slotGen) :
    ({ ds with caps := fc, lineage := fl, slotGen := fg } : DomainState) = ds := by
  rw [hfc, hfl, hfg]

/-! ## Kernel-function frame lemmas -/

section Kernel

variable {d cd : DomainId} {R : Addr → Prop} {σ : MachineState}

/-- Dropping the lineage index never changes an entry's kind. -/
theorem kind_ite (c : Prop) [Decidable c] (e : CapEntry) :
    (if c then ({ e with lineage := none } : CapEntry) else e).kind = e.kind := by
  split <;> rfl

/-- `setDom` at a foreign domain with a caps/regions-preserving update. -/
theorem dkeep_setDom (hctx : DCtx d R σ) (e : DomainId) (f : DomainState → DomainState)
    (he : e ≠ d)
    (hcaps : (f (σ.doms e)).caps = (σ.doms e).caps)
    (hreg : (f (σ.doms e)).regions = (σ.doms e).regions) :
    DKeep d cd R σ (σ.setDom e f) where
  ddoms := setDom_doms_ne σ e f d (fun h => he h.symm)
  mem := fun _ _ => rfl
  gcfg := fun _ => rfl
  acts := fun _ _ h => Or.inl h
  mover := fun _ h => Or.inl h
  ro := fun e' r rg h => by
    by_cases hee : e' = e
    · subst hee
      rw [setDom_doms_same, hreg] at h
      exact hctx.ro e' r rg h
    · rw [setDom_doms_ne _ _ _ _ hee] at h
      exact hctx.ro e' r rg h
  fo := fun e' he' s entry b l p hc hkind => by
    by_cases hee : e' = e
    · subst hee
      rw [setDom_doms_same, hcaps] at hc
      exact hctx.fo e' he' s entry b l p hc hkind
    · rw [setDom_doms_ne _ _ _ _ hee] at hc
      exact hctx.fo e' he' s entry b l p hc hkind
  regR := fun e' _ r rg h => by
    by_cases hee : e' = e
    · subst hee
      rw [setDom_doms_same, hreg] at h
      exact Or.inl h
    · rw [setDom_doms_ne _ _ _ _ hee] at h
      exact Or.inl h

/-- A memory write at an address covered by a foreign domain. -/
theorem dkeep_write (hctx : DCtx d R σ) (e : DomainId) (he : e ≠ d)
    (a : Addr) (v : Loom.Word32) (need : Perms)
    (hcov : σ.domCovers e a need = true) :
    DKeep d cd R σ (σ.write a v) where
  ddoms := rfl
  mem := fun a' ha' => by
    show Loom.Fun.update σ.mem a v a' = σ.mem a'
    exact Loom.Fun.update_ne _ _ _ _
      (fun h => hctx.covOff e he a need hcov (h ▸ ha'))
  gcfg := fun _ => rfl
  acts := fun _ _ h => Or.inl h
  mover := fun _ h => Or.inl h
  ro := hctx.ro
  fo := hctx.fo
  regR := fun _ _ _ _ h => Or.inl h

/-- `reparent` never touches `d` (no lineage cells) nor any kind/region. -/
theorem dkeep_reparent (hctx : DCtx d R σ) (old new : CapRef) :
    DKeep d cd R σ (σ.reparent old new) where
  ddoms := by
    show ({ σ.doms d with lineage := _ } : DomainState) = σ.doms d
    refine setLineage_self _ _ (funext fun l => ?_)
    rw [hctx.dlin l]
  mem := fun _ _ => rfl
  gcfg := fun _ => rfl
  acts := fun _ _ h => Or.inl h
  mover := fun _ h => Or.inl h
  ro := fun e r rg h => hctx.ro e r rg h
  fo := fun e he s entry b l p hc hkind => hctx.fo e he s entry b l p hc hkind
  regR := fun _ _ _ _ h => Or.inl h

/-- `orphanChildren` never touches `d` (root entries, no cells) and only
drops lineage indices elsewhere. -/
theorem dkeep_orphanChildren (hctx : DCtx d R σ) (old : CapRef) :
    DKeep d cd R σ (σ.orphanChildren old) where
  ddoms := by
    show ({ σ.doms d with caps := _, lineage := _ } : DomainState) = σ.doms d
    refine setCapsLineage_self _ _ _ (funext fun s => ?_) (funext fun l => ?_)
    · cases hc : (σ.doms d).caps s with
      | none => simp only [hc]
      | some e => simp only [hc, hctx.dent s e hc]
    · simp [hctx.dlin l]
  mem := fun _ _ => rfl
  gcfg := fun _ => rfl
  acts := fun _ _ h => Or.inl h
  mover := fun _ h => Or.inl h
  ro := fun e r rg h => hctx.ro e r rg (by rw [← orphanChildren_regions σ old e]; exact h)
  fo := fun e he s entry b l p hc hkind => by
    rw [orphanChildren_caps] at hc
    cases hc0 : (σ.doms e).caps s with
    | none => simp [hc0] at hc
    | some e0 =>
        simp only [hc0] at hc
        cases hl0 : e0.lineage with
        | none =>
            simp only [hl0, Option.some.injEq] at hc
            subst hc
            exact hctx.fo e he s e0 b l p hc0 hkind
        | some l0 =>
            simp only [hl0, Option.some.injEq] at hc
            have hkk : entry.kind = e0.kind := by
              rw [← hc]
              exact kind_ite _ e0
            exact hctx.fo e he s e0 b l p hc0 (hkk.symm.trans hkind)
  regR := fun e _ r rg h => Or.inl (by rw [← orphanChildren_regions σ old e]; exact h)

/-- `clearSlot` at a foreign domain. -/
theorem dkeep_clearSlot (hctx : DCtx d R σ) (e : DomainId) (s : Slot) (he : e ≠ d) :
    DKeep d cd R σ (σ.clearSlot e s) where
  ddoms := by
    unfold MachineState.clearSlot
    exact setDom_doms_ne _ _ _ _ (fun h => he h.symm)
  mem := fun _ _ => rfl
  gcfg := fun _ => rfl
  acts := fun _ _ h => Or.inl h
  mover := fun _ h => Or.inl h
  ro := fun e' r rg h => hctx.ro e' r rg (by rw [← clearSlot_regions σ e s e']; exact h)
  fo := fun e' he' s' entry b l p hc hkind => by
    rw [clearSlot_caps] at hc
    split at hc
    · cases hc
    · exact hctx.fo e' he' s' entry b l p hc hkind
  regR := fun e' _ r rg h => Or.inl (by rw [← clearSlot_regions σ e s e']; exact h)

/-- `destroyMarked` with `d` unmarked. -/
theorem dkeep_destroyMarked (hctx : DCtx d R σ) (mk : DomainId → Slot → Bool)
    (hd : ∀ s, mk d s = false) :
    DKeep d cd R σ (σ.destroyMarked mk) where
  ddoms := by
    show ({ σ.doms d with caps := _, lineage := _, slotGen := _ } : DomainState) = σ.doms d
    refine setCapsLineageGen_self _ _ _ _ (funext fun s => ?_) (funext fun l => ?_)
      (funext fun s => ?_)
    · show (if mk d s then none else (σ.doms d).caps s) = (σ.doms d).caps s
      rw [hd s]
      rfl
    · show (if _ then none else (σ.doms d).lineage l) = (σ.doms d).lineage l
      rw [hctx.dlin l]
      split <;> rfl
    · show (if mk d s && ((σ.doms d).caps s).isSome then bumpGen ((σ.doms d).slotGen s)
        else (σ.doms d).slotGen s) = (σ.doms d).slotGen s
      rw [hd s]
      rfl
  mem := fun _ _ => rfl
  gcfg := fun _ => rfl
  acts := fun _ _ h => Or.inl h
  mover := fun _ h => Or.inl h
  ro := fun e r rg h => hctx.ro e r rg (by rw [← destroyMarked_regions σ mk e]; exact h)
  fo := fun e he s entry b l p hc hkind => by
    rw [destroyMarked_caps] at hc
    split at hc
    · cases hc
    · exact hctx.fo e he s entry b l p hc hkind
  regR := fun e _ r rg h => Or.inl (by rw [← destroyMarked_regions σ mk e]; exact h)

/-- `d` is never marked by any revoke sweep: `d` owns no lineage cells, so
`parentOf d s = none` for every slot. -/
theorem marks_d_false (hctx : DCtx d R σ) (root : CapRef) (s : Slot) :
    σ.marks root d s = false := by
  have hpar : ∀ s' : Slot, σ.parentOf d s' = none := by
    intro s'
    unfold MachineState.parentOf
    cases hc : (σ.doms d).caps s' with
    | none => rfl
    | some e => simp [hctx.dent s' e hc]
  rw [marks_eq_iter]
  generalize numDomains * numSlots = k
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [iterMark_succ]
      unfold MachineState.markStep
      rw [ih, hpar s]
      rfl

/-- A region surviving `sweepRegions` was already there. -/
theorem sweepRegions_regions_sub (σ : MachineState) (e : DomainId) (r : RegionId)
    (rg : Region) (h : (σ.sweepRegions.doms e).regions r = some rg) :
    (σ.doms e).regions r = some rg := by
  have hred : (σ.sweepRegions.doms e).regions r = (match (σ.doms e).regions r with
    | some rg => if σ.liveRef rg.backing then some rg else none
    | none => none) := rfl
  rw [hred] at h
  cases hr : (σ.doms e).regions r with
  | none => simp [hr] at h
  | some rg0 =>
      simp only [hr] at h
      split at h
      · exact h
      · cases h

/-- `sweepRegions` keeps every region of `d` (live-backed by `d`'s own
capabilities). -/
theorem dkeep_sweepRegions (hctx : DCtx d R σ) :
    DKeep d cd R σ σ.sweepRegions where
  ddoms := by
    show ({ σ.doms d with regions := _ } : DomainState) = σ.doms d
    refine setRegions_self _ _ (funext fun r => ?_)
    cases hr : (σ.doms d).regions r with
    | none => simp only [hr]
    | some rg =>
        obtain ⟨hdom, hlive⟩ := hctx.dreg r rg hr
        have hlv : σ.liveRef rg.backing = true := by
          unfold MachineState.liveRef
          rw [hdom]
          exact hlive
        simp only [hr, hlv, if_true]
  mem := fun _ _ => rfl
  gcfg := fun _ => rfl
  acts := fun _ _ h => Or.inl h
  mover := fun _ h => Or.inl h
  ro := fun e r rg h => hctx.ro e r rg (sweepRegions_regions_sub σ e r rg h)
  fo := fun e he s entry b l p hc hkind =>
    hctx.fo e he s entry b l p (by rw [← sweepRegions_caps σ e]; exact hc) hkind
  regR := fun e _ r rg h => Or.inl (sweepRegions_regions_sub σ e r rg h)

/-- `sweepMover`: the status write goes through a foreign owner's coverage. -/
theorem dkeep_sweepMover (hctx : DCtx d R σ) :
    DKeep d cd R σ σ.sweepMover := by
  have base : ∀ σ' : MachineState, σ'.doms = σ.doms → σ'.gates = σ.gates →
      (∀ a, R a → σ'.mem a = σ.mem a) →
      (∀ job, σ'.mover = some job → σ.mover = some job) →
      DKeep d cd R σ σ' := by
    intro σ' hdoms hgates hmem hmov
    exact
      { ddoms := by rw [hdoms]
        mem := hmem
        gcfg := fun g => by rw [hgates]
        acts := fun g a h => Or.inl (by rw [← hgates]; exact h)
        mover := fun job h => Or.inl (hmov job h)
        ro := fun e r rg h => hctx.ro e r rg (by rw [← hdoms]; exact h)
        fo := fun e he s entry b l p hc hkind =>
          hctx.fo e he s entry b l p (by rw [← hdoms]; exact hc) hkind
        regR := fun e _ r rg h => Or.inl (by rw [← hdoms]; exact h) }
  unfold MachineState.sweepMover
  cases hm : σ.mover with
  | none => exact base σ rfl rfl (fun _ _ => rfl) (fun _ h => h)
  | some job =>
      dsimp only
      have howner : job.owner ≠ d := hctx.movOff job hm
      by_cases hlive : σ.liveRef job.src && σ.liveRef job.dst
      · rw [if_pos hlive]
        exact base σ rfl rfl (fun _ _ => rfl) (fun _ h => h)
      · rw [if_neg hlive]
        by_cases hcov : ({ σ with mover := none } : MachineState).domCovers job.owner
            job.statusAddr { r := false, w := true, x := false } = true
        · rw [if_pos hcov]
          have hcov' : σ.domCovers job.owner job.statusAddr
              { r := false, w := true, x := false } = true := hcov
          refine base _ rfl rfl ?_ (fun job' h => by cases h)
          intro a ha
          show Loom.Fun.update σ.mem job.statusAddr _ a = σ.mem a
          exact Loom.Fun.update_ne _ _ _ _
            (fun h => hctx.covOff job.owner howner job.statusAddr _ hcov' (h ▸ ha))
        · rw [if_neg hcov]
          exact base { σ with mover := none } rfl rfl (fun _ _ => rfl)
            (fun _ h => by cases h)

/-- Installing a fresh capability entry at a foreign domain, provided the
new entry's range avoids `R`. Covers `installDerived` and the transfer
install. -/
theorem dkeep_installAt (hctx : DCtx d R σ) (to_ : DomainId) (hto : to_ ≠ d)
    (s' : Slot) (ent : CapEntry)
    (hk : ∀ b len p, ent.kind = .mem b len p → ∀ a : Addr, b.toNat ≤ a.toNat →
      a.toNat < b.toNat + len.toNat → ¬ R a)
    (f : DomainState → DomainState)
    (hf_caps : (f (σ.doms to_)).caps = Loom.Fun.update (σ.doms to_).caps s' (some ent))
    (hf_reg : (f (σ.doms to_)).regions = (σ.doms to_).regions) :
    DKeep d cd R σ (σ.setDom to_ f) where
  ddoms := setDom_doms_ne σ to_ f d (fun h => hto h.symm)
  mem := fun _ _ => rfl
  gcfg := fun _ => rfl
  acts := fun _ _ h => Or.inl h
  mover := fun _ h => Or.inl h
  ro := fun e r rg h => by
    by_cases hee : e = to_
    · subst hee
      rw [setDom_doms_same, hf_reg] at h
      exact hctx.ro e r rg h
    · rw [setDom_doms_ne _ _ _ _ hee] at h
      exact hctx.ro e r rg h
  fo := fun e he s0 entry b l p hc hkind => by
    by_cases hee : e = to_
    · subst hee
      rw [setDom_doms_same, hf_caps] at hc
      by_cases hs : s0 = s'
      · subst hs
        rw [Loom.Fun.update_same] at hc
        injection hc with hc
        subst hc
        exact hk b l p hkind
      · rw [Loom.Fun.update_ne _ _ _ _ hs] at hc
        exact hctx.fo e he s0 entry b l p hc hkind
    · rw [setDom_doms_ne _ _ _ _ hee] at hc
      exact hctx.fo e he s0 entry b l p hc hkind
  regR := fun e _ r rg h => by
    by_cases hee : e = to_
    · subst hee
      rw [setDom_doms_same, hf_reg] at h
      exact Or.inl h
    · rw [setDom_doms_ne _ _ _ _ hee] at h
      exact Or.inl h

/-- `transferCap` between two foreign domains. -/
theorem dkeep_transferCap (hctx : DCtx d R σ) (hcd : cd ≠ d)
    (from_ : DomainId) (s : Slot) (to_ : DomainId) (σ' : MachineState) (ref : CapRef)
    (hfrom : from_ ≠ d) (hto : to_ ≠ d)
    (ht : σ.transferCap from_ s to_ = some (σ', ref)) :
    DKeep d cd R σ σ' := by
  unfold MachineState.transferCap at ht
  cases he : (σ.doms from_).caps s with
  | none => rw [he] at ht; simp at ht
  | some e =>
      rw [he] at ht
      simp only [Option.bind_eq_bind, Option.bind_some] at ht
      cases hfs : σ.freeSlot to_ with
      | none => rw [hfs] at ht; simp at ht
      | some s2 =>
          rw [hfs] at ht
          simp only [Option.bind_some] at ht
          -- the new entry's kind is `e.kind`, off `R` because `from_ ≠ d`
          have hkoff : ∀ (ent : CapEntry), ent.kind = e.kind →
              ∀ b len p, ent.kind = .mem b len p → ∀ a : Addr, b.toNat ≤ a.toNat →
              a.toNat < b.toNat + len.toNat → ¬ R a := by
            intro ent hent b len p hkind a h1 h2
            exact hctx.fo from_ hfrom s e b len p he (by rw [← hent]; exact hkind) a h1 h2
          -- the tail after the install: reparent → clearSlot → sweeps
          have tail : ∀ (σ₁ : MachineState), DKeep d cd R σ σ₁ →
              some ((((σ₁.reparent ⟨from_, s, (σ.doms from_).slotGen s⟩
                  ⟨to_, s2, (σ.doms to_).slotGen s2⟩).clearSlot from_ s).sweepRegions).sweepMover,
                (⟨to_, s2, (σ.doms to_).slotGen s2⟩ : CapRef)) = some (σ', ref) →
              DKeep d cd R σ σ' := by
            intro σ₁ h1 heq
            injection heq with heq
            injection heq with hσ' _
            subst hσ'
            have hctx1 := hctx.transport hcd h1
            have h2 := dkeep_reparent (cd := cd) hctx1 ⟨from_, s, (σ.doms from_).slotGen s⟩
              ⟨to_, s2, (σ.doms to_).slotGen s2⟩
            have hctx2 := hctx1.transport hcd h2
            have h3 := dkeep_clearSlot (cd := cd) hctx2 from_ s hfrom
            have hctx3 := hctx2.transport hcd h3
            have h4 := dkeep_sweepRegions (cd := cd) hctx3
            have hctx4 := hctx3.transport hcd h4
            have h5 := dkeep_sweepMover (cd := cd) hctx4
            exact ((((h1.trans h2).trans h3).trans h4).trans h5)
          cases hl : e.lineage with
          | none =>
              rw [hl] at ht
              simp only [Option.pure_def, Option.bind_some] at ht
              refine tail _ ?_ ht
              exact dkeep_installAt hctx to_ hto s2 { kind := e.kind, lineage := none }
                (hkoff _ rfl) _ rfl rfl
          | some l =>
              rw [hl] at ht
              simp only [Option.bind_eq_bind, Option.bind_some] at ht
              cases hc : (σ.doms from_).lineage l with
              | none => rw [hc] at ht; simp at ht
              | some cell =>
                  rw [hc] at ht
                  simp only [Option.bind_some] at ht
                  cases hfc : σ.freeCell to_ with
                  | none => rw [hfc] at ht; simp at ht
                  | some l' =>
                      rw [hfc] at ht
                      simp only [Option.pure_def, Option.bind_some] at ht
                      refine tail _ ?_ ht
                      exact dkeep_installAt hctx to_ hto s2
                        { kind := e.kind, lineage := some l' } (hkoff _ rfl) _
                        rfl rfl

/-- `haltBase` at a foreign domain. -/
theorem dkeep_haltBase (hctx : DCtx d R σ) (e : DomainId) (cv : Loom.Word32)
    (he : e ≠ d) : DKeep d cd R σ (σ.haltBase e cv) := by
  unfold MachineState.haltBase
  exact dkeep_setDom hctx e _ he rfl rfl

/-- Updating one gate record (config kept, activation accounted for). -/
theorem dkeep_gateUpd (hctx : DCtx d R σ) (g : GateId) (G : GateState)
    (hcfg : G.config = (σ.gates g).config)
    (hact : ∀ a, G.act = some a → (σ.gates g).act = some a ∨ a.caller = cd) :
    DKeep d cd R σ { σ with gates := Loom.Fun.update σ.gates g G } where
  ddoms := rfl
  mem := fun _ _ => rfl
  gcfg := fun g' => by
    show (Loom.Fun.update σ.gates g G g').config = _
    by_cases hgg : g' = g
    · subst hgg
      rw [Loom.Fun.update_same, hcfg]
    · rw [Loom.Fun.update_ne _ _ _ _ hgg]
  acts := fun g' a h => by
    have h' : (Loom.Fun.update σ.gates g G g').act = some a := h
    by_cases hgg : g' = g
    · subst hgg
      rw [Loom.Fun.update_same] at h'
      exact hact a h'
    · rw [Loom.Fun.update_ne _ _ _ _ hgg] at h'
      exact Or.inl h'
  mover := fun _ h => Or.inl h
  ro := hctx.ro
  fo := hctx.fo
  regR := fun _ _ _ _ h => Or.inl h

/-- `unwindGate` resuming a foreign caller. -/
theorem dkeep_unwindGate (hctx : DCtx d R σ) (hcd : cd ≠ d) (g : GateId)
    (cl : DomainId) (rd : RegId) (hcl : cl ≠ d) :
    DKeep d cd R σ (σ.unwindGate g cl rd) := by
  unfold MachineState.unwindGate
  have hg : DKeep d cd R σ
      { σ with gates := Loom.Fun.update σ.gates g { (σ.gates g) with act := none } } :=
    dkeep_gateUpd hctx g _ rfl (fun a h => by cases h)
  have hctx1 := hctx.transport hcd hg
  refine hg.trans ?_
  exact dkeep_setDom hctx1 cl _ hcl (setReg_caps _ _ _) (setReg_regions _ _ _)

/-- `haltDom` of a foreign domain (the unwound caller, if any, is foreign
too). -/
theorem dkeep_haltDom (hctx : DCtx d R σ) (hcd : cd ≠ d) (e : DomainId)
    (cv : Loom.Word32) (he : e ≠ d) : DKeep d cd R σ (σ.haltDom e cv) := by
  cases hs : (σ.doms e).serving with
  | none => rw [haltDom_base σ e cv hs]; exact dkeep_haltBase hctx e cv he
  | some g =>
      cases ha : (σ.gates g).act with
      | none => rw [haltDom_base' σ e cv g hs ha]; exact dkeep_haltBase hctx e cv he
      | some a =>
          rw [haltDom_unwind σ e cv g a hs ha]
          have hcaller : a.caller ≠ d := hctx.acaller g a ha
          have h1 : DKeep d cd R σ (σ.haltBase e cv) := dkeep_haltBase hctx e cv he
          have hctx1 := hctx.transport hcd h1
          refine h1.trans ?_
          exact dkeep_unwindGate hctx1 hcd g a.caller a.callerRd hcaller

end Kernel

/-! ## The `SpecM` combinator kit -/

/-- The per-fragment obligation: from any context state, both `ok` and
`err` outcomes satisfy `DKeep`. -/
def DKLe (d cd : DomainId) (R : Addr → Prop) {α : Type} (mm : SpecM α) : Prop :=
  ∀ σ, DCtx d R σ → cd ≠ d →
    (∀ a σ', mm σ = .ok a σ' → DKeep d cd R σ σ') ∧
    (∀ er σ', mm σ = .err er σ' → DKeep d cd R σ σ')

section Kit

variable {d cd : DomainId} {R : Addr → Prop}

theorem DKLe.of_state_eq {α : Type} {mm : SpecM α}
    (hok : ∀ σ a σ', mm σ = .ok a σ' → σ' = σ)
    (herr : ∀ σ e σ', mm σ = .err e σ' → σ' = σ) : DKLe d cd R mm :=
  fun σ hctx _ =>
    ⟨fun a σ' he => DKeep.of_eq (hok σ a σ' he) hctx.ro hctx.fo,
     fun e σ' he => DKeep.of_eq (herr σ e σ' he) hctx.ro hctx.fo⟩

theorem DKLe.pure {α : Type} (a : α) : DKLe d cd R (Pure.pure a : SpecM α) :=
  DKLe.of_state_eq
    (fun σ a' σ' he => by rw [specM_pure] at he; injection he with _ h2; exact h2.symm)
    (fun σ e σ' he => by rw [specM_pure] at he; simp at he)

theorem DKLe.bind {α β : Type} {m : SpecM α} {f : α → SpecM β}
    (hm : DKLe d cd R m) (hf : ∀ a, DKLe d cd R (f a)) : DKLe d cd R (m >>= f) := by
  intro σ hctx hne
  refine ⟨?_, ?_⟩
  · intro b σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 =>
        rw [hmσ] at he
        have h1 := (hm σ hctx hne).1 a σ1 hmσ
        exact h1.trans ((hf a σ1 (hctx.transport hne h1) hne).1 b σ' he)
    | err e σ1 => rw [hmσ] at he; simp at he
    | fault g => rw [hmσ] at he; simp at he
  · intro e σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 =>
        rw [hmσ] at he
        have h1 := (hm σ hctx hne).1 a σ1 hmσ
        exact h1.trans ((hf a σ1 (hctx.transport hne h1) hne).2 e σ' he)
    | err e1 σ1 =>
        rw [hmσ] at he
        injection he with _ h2
        subst h2
        exact (hm σ hctx hne).2 e1 σ1 hmσ
    | fault g => rw [hmσ] at he; simp at he

theorem DKLe.iteBool {α : Type} (b : Bool) {m1 m2 : SpecM α}
    (h1 : DKLe d cd R m1) (h2 : DKLe d cd R m2) :
    DKLe d cd R (if b then m1 else m2) := by
  cases b <;> simp only [Bool.false_eq_true, if_true, if_false]
  · exact h2
  · exact h1

theorem DKLe.reg (d' : DomainId) (r : RegId) : DKLe d cd R (SpecM.reg d' r) :=
  DKLe.of_state_eq
    (fun σ a σ' he => by unfold SpecM.reg at he; injection he with _ h2; exact h2.symm)
    (fun σ e σ' he => by unfold SpecM.reg at he; simp at he)

theorem DKLe.get : DKLe d cd R SpecM.get :=
  DKLe.of_state_eq
    (fun σ a σ' he => by unfold SpecM.get at he; injection he with _ h2; exact h2.symm)
    (fun σ e σ' he => by unfold SpecM.get at he; simp at he)

theorem DKLe.raise {α : Type} (e : Errno) : DKLe d cd R (SpecM.raise e : SpecM α) :=
  DKLe.of_state_eq
    (fun σ a σ' he => by unfold SpecM.raise at he; simp at he)
    (fun σ e' σ' he => by unfold SpecM.raise at he; injection he with _ h2; exact h2.symm)

theorem DKLe.require (cond : Bool) (e : Errno) : DKLe d cd R (SpecM.require cond e) :=
  DKLe.of_state_eq
    (fun σ a σ' he => by cases a; exact require_ok cond e σ he)
    (fun σ e' σ' he => require_err_state cond e σ he)

theorem DKLe.demand (cond : Bool) (f : Fault) : DKLe d cd R (SpecM.demand cond f) :=
  DKLe.of_state_eq
    (fun σ a σ' he => by cases a; exact demand_ok cond f σ he)
    (fun σ e σ' he => by
      unfold SpecM.demand at he
      split at he
      · simp [specM_pure] at he
      · simp [SpecM.fatal] at he)

theorem DKLe.load (d' : DomainId) (a : Addr) : DKLe d cd R (SpecM.load d' a) :=
  DKLe.of_state_eq
    (fun σ v σ' he => load_ok d' a σ he)
    (fun σ e σ' he => load_err_state d' a σ he)

theorem DKLe.capLive (d' : DomainId) (hw : Loom.Word32) :
    DKLe d cd R (Machines.Lnp64u.Isa.capLive d' hw) :=
  DKLe.of_state_eq
    (fun σ r σ' he => (Machines.Lnp64u.Isa.Wip.capLive_ok d' hw σ he).1)
    (fun σ e σ' he => Machines.Lnp64u.Isa.Wip.capLive_err_state d' hw σ he)

theorem DKLe.narrow (base : Addr) (len : BitVec 13) (perms : Perms)
    (dw : Loom.Word32) : DKLe d cd R (Machines.Lnp64u.Isa.narrow base len perms dw) :=
  DKLe.of_state_eq
    (fun σ k σ' he => (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms dw σ he).1)
    (fun σ e σ' he => Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms dw σ he)

/-- `updDom` at the executing domain, provided the update leaves the
capability table and the region registers alone. -/
theorem DKLe.updDomExec (f : DomainState → DomainState)
    (hcaps : ∀ ds, (f ds).caps = ds.caps)
    (hreg : ∀ ds, (f ds).regions = ds.regions) :
    DKLe d cd R (SpecM.updDom cd f) := by
  intro σ hctx hne
  refine ⟨?_, ?_⟩
  · intro a σ' he
    unfold SpecM.updDom SpecM.modify at he
    injection he with _ h2
    subst h2
    exact dkeep_setDom hctx cd f hne (hcaps _) (hreg _)
  · intro e σ' he
    unfold SpecM.updDom SpecM.modify at he
    simp at he

theorem DKLe.setReg (r : RegId) (v : Loom.Word32) :
    DKLe d cd R (SpecM.setReg cd r v) :=
  DKLe.updDomExec _ (fun ds => setReg_caps ds r v) (fun ds => setReg_regions ds r v)

theorem DKLe.store (a : Addr) (v : Loom.Word32) :
    DKLe d cd R (SpecM.store cd a v) := by
  intro σ hctx hne
  unfold SpecM.store
  refine ⟨?_, ?_⟩
  · intro x σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers cd a { r := false, w := true, x := false }
    · simp only [SpecM.demand, hc, if_true, specM_pure, specM_bind, SpecM.set] at he
      injection he with _ h2
      subst h2
      exact dkeep_write hctx cd hne a v _ hc
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he
  · intro e σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers cd a { r := false, w := true, x := false }
    · simp [SpecM.demand, hc, specM_pure, specM_bind, SpecM.set] at he
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he

/-- `d`'s slot table being full, `freeSlot d` fails. -/
theorem freeSlot_d_none {σ : MachineState} (hctx : DCtx d R σ) :
    σ.freeSlot d = none := by
  unfold MachineState.freeSlot
  rw [List.find?_eq_none]
  intro s _
  cases hc : (σ.doms d).caps s with
  | none => exact absurd hc (hctx.dfull s)
  | some e => simp [hc]

/-- `allocDerived`: grants into `d` fail at the granter; installs elsewhere
carry a kind that avoids `R`. -/
theorem DKLe.allocDerived (owner : DomainId) (kind : CapKind) (parent : CapRef)
    (hk : owner ≠ d → ∀ b len p, kind = .mem b len p → ∀ a : Addr,
      b.toNat ≤ a.toNat → a.toNat < b.toNat + len.toNat → ¬ R a) :
    DKLe d cd R (Machines.Lnp64u.Isa.allocDerived owner kind parent) := by
  intro σ hctx hne
  refine ⟨?_, ?_⟩
  · intro hw σ' he
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
            subst h2
            have howner : owner ≠ d := by
              intro hod
              subst hod
              rw [freeSlot_d_none hctx] at hfs
              cases hfs
            exact dkeep_installAt hctx owner howner s
              { kind := kind, lineage := some l } (hk howner)
              (fun ds => { ds with
                caps := Loom.Fun.update ds.caps s
                  (some { kind := kind, lineage := some l })
                lineage := Loom.Fun.update ds.lineage l
                  (some { parent := parent }) }) rfl rfl
  · intro e σ' he
    exact DKeep.of_eq
      (Machines.Lnp64u.Isa.Wip.allocDerived_err_state owner kind parent σ he)
      hctx.ro hctx.fo

/-- Case on the observed state first (for state-derived continuations). -/
theorem DKLe.getD {α : Type} (f : MachineState → SpecM α)
    (hf : ∀ σ0, DCtx d R σ0 → cd ≠ d →
      (∀ a σ', f σ0 σ0 = .ok a σ' → DKeep d cd R σ0 σ') ∧
      (∀ er σ', f σ0 σ0 = .err er σ' → DKeep d cd R σ0 σ')) :
    DKLe d cd R (SpecM.get >>= f) := by
  intro σ hctx hne
  have hred : (SpecM.get >>= f) σ = f σ σ := rfl
  rw [hred]
  exact hf σ hctx hne

/-- **The base opcodes are `DKLe`**: they only write the executing
domain's registers/pc and store through its own coverage. -/
theorem base_dkle : ∀ instr ∈ Machines.Lnp64u.Isa.base, ∀ c : Ctx, c.d = cd →
    DKLe d cd R (instr.sem.exec c) := by
  intro instr hmem c hc
  subst hc
  fin_cases hmem
  · exact DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.setReg _ _))
  · exact DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.setReg _ _))
  · exact DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.setReg _ _))
  · exact DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.setReg _ _))
  · exact DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.setReg _ _))
  · exact DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.setReg _ _))
  · exact DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.setReg _ _))
  · exact DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.setReg _ _)
  · exact DKLe.setReg _ _
  · exact DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.bind (DKLe.load _ _) (fun _ => DKLe.setReg _ _))
  · exact DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.store _ _))
  · exact DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.bind (DKLe.reg _ _) (fun _ =>
      DKLe.iteBool _ (DKLe.updDomExec _ (fun _ => rfl) (fun _ => rfl)) (DKLe.pure ())))
  · exact DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.bind (DKLe.reg _ _) (fun _ =>
      DKLe.iteBool _ (DKLe.updDomExec _ (fun _ => rfl) (fun _ => rfl)) (DKLe.pure ())))
  · exact DKLe.bind (DKLe.reg _ _) (fun _ => DKLe.bind (DKLe.setReg _ _) (fun _ =>
      DKLe.updDomExec _ (fun _ => rfl) (fun _ => rfl)))

end Kit

/-! ## System-op helpers -/

section SysHelpers

variable {d cd : DomainId} {R : Addr → Prop} {σ : MachineState}

/-- `setReg` at any foreign domain (the errno write-back / reply write). -/
theorem dkeep_setRegOther (hctx : DCtx d R σ) (e : DomainId) (he : e ≠ d)
    (r : RegId) (v : Loom.Word32) :
    DKeep d cd R σ (σ.setDom e (fun ds => ds.setReg r v)) :=
  dkeep_setDom hctx e _ he (setReg_caps _ r v) (setReg_regions _ r v)

/-- Programming the Mover with a job owned by the executing domain. -/
theorem dkeep_setMover (hctx : DCtx d R σ) (job : MoverJob)
    (hj : job.owner = cd) :
    DKeep d cd R σ { σ with mover := some job } where
  ddoms := rfl
  mem := fun _ _ => rfl
  gcfg := fun _ => rfl
  acts := fun _ _ h => Or.inl h
  mover := fun job' h => by
    have : some job = some job' := h
    injection this with hjj
    exact Or.inr (hjj ▸ hj)
  ro := hctx.ro
  fo := hctx.fo
  regR := fun _ _ _ _ h => Or.inl h

/-- Writing one region register of the executing domain (`map`/`unmap`):
an installed region must be own-backed and, when `cd ≠ d`, cover only
non-`R` addresses. -/
theorem dkeep_regionsSet (hctx : DCtx d R σ) (hne : cd ≠ d) (ri : RegionId)
    (v : Option Region)
    (hv : ∀ rg, v = some rg → rg.backing.dom = cd ∧
      ∀ a : Addr, rg.base.toNat ≤ a.toNat →
        a.toNat < rg.base.toNat + rg.len.toNat → ¬ R a) :
    DKeep d cd R σ (σ.setDom cd
      (fun ds => { ds with regions := Loom.Fun.update ds.regions ri v })) where
  ddoms := setDom_doms_ne σ cd _ d (fun h => hne h.symm)
  mem := fun _ _ => rfl
  gcfg := fun _ => rfl
  acts := fun _ _ h => Or.inl h
  mover := fun _ h => Or.inl h
  ro := fun e r rg h => by
    by_cases hee : e = cd
    · subst hee
      rw [setDom_doms_same] at h
      have h' : Loom.Fun.update (σ.doms e).regions ri v r = some rg := h
      by_cases hr : r = ri
      · subst hr
        rw [Loom.Fun.update_same] at h'
        exact (hv rg h').1
      · rw [Loom.Fun.update_ne _ _ _ _ hr] at h'
        exact hctx.ro e r rg h'
    · rw [setDom_doms_ne _ _ _ _ hee] at h
      exact hctx.ro e r rg h
  fo := fun e he s entry b l p hc hkind => by
    by_cases hee : e = cd
    · subst hee
      rw [setDom_doms_same] at hc
      exact hctx.fo e he s entry b l p hc hkind
    · rw [setDom_doms_ne _ _ _ _ hee] at hc
      exact hctx.fo e he s entry b l p hc hkind
  regR := fun e _ r rg h => by
    by_cases hee : e = cd
    · subst hee
      rw [setDom_doms_same] at h
      have h' : Loom.Fun.update (σ.doms e).regions ri v r = some rg := h
      by_cases hr : r = ri
      · subst hr
        rw [Loom.Fun.update_same] at h'
        exact Or.inr (hv rg h').2
      · rw [Loom.Fun.update_ne _ _ _ _ hr] at h'
        exact Or.inl h'
    · rw [setDom_doms_ne _ _ _ _ hee] at h
      exact Or.inl h

/-- A kind narrowed from a range that avoids `R` avoids `R`. -/
theorem narrow_off_R {base : Addr} {len : BitVec 13} {perms : Perms} {dw : Loom.Word32}
    {kind : CapKind} {σ σ' : MachineState}
    (hn : Machines.Lnp64u.Isa.narrow base len perms dw σ = .ok kind σ')
    (hR : ∀ a : Addr, base.toNat ≤ a.toNat → a.toNat < base.toNat + len.toNat → ¬ R a) :
    ∀ b ln p, kind = .mem b ln p → ∀ a : Addr, b.toNat ≤ a.toNat →
      a.toNat < b.toNat + ln.toNat → ¬ R a := by
  intro b ln p hkind a h1 h2
  unfold Machines.Lnp64u.Isa.narrow at hn
  simp only [SpecM.require, specM_bind, specM_pure] at hn
  split_ifs at hn with hc1 hc2 hc3 hc4
  · injection hn with hk hσ
    rw [hkind] at hk
    injection hk with hb hln hp
    have hoff : (Machines.Lnp64u.Isa.descOff dw).toNat +
        (Machines.Lnp64u.Isa.descLen dw).toNat ≤ len.toNat := by simpa using hc1
    have hlt : base.toNat + (Machines.Lnp64u.Isa.descOff dw).toNat < memWords := by
      simpa using hc2
    have hmw : memWords = 4096 := rfl
    have hadd : (base + Machines.Lnp64u.Isa.descOff dw).toNat =
        base.toNat + (Machines.Lnp64u.Isa.descOff dw).toNat := by
      rw [BitVec.toNat_add,
        Nat.mod_eq_of_lt (by omega : base.toNat + (Machines.Lnp64u.Isa.descOff dw).toNat < 2 ^ 12)]
    have hbn : b.toNat = base.toNat + (Machines.Lnp64u.Isa.descOff dw).toNat := by
      rw [← hb]; exact hadd
    have hlnn : ln.toNat = (Machines.Lnp64u.Isa.descLen dw).toNat := by rw [← hln]
    exact hR a (by omega) (by omega)
  all_goals simp [SpecM.raise] at hn

/-- The range of a live entry of the executing domain avoids `R`. -/
theorem entry_off_R {s : Slot} {e : CapEntry} {base : Addr} {len : BitVec 13}
    {perms : Perms} (hctx : DCtx d R σ) (hne : cd ≠ d)
    (hcaps : (σ.doms cd).caps s = some e) (hek : e.kind = .mem base len perms) :
    ∀ a : Addr, base.toNat ≤ a.toNat → a.toNat < base.toNat + len.toNat → ¬ R a :=
  fun a hlo hhi => hctx.fo cd hne s e base len perms hcaps hek a hlo hhi

/-- `transferByHandle` from the executing domain to a foreign recipient. -/
theorem DKLe.transferByHandle (to_ : DomainId) (hw : Loom.Word32) (hto : to_ ≠ d) :
    DKLe d cd R (Machines.Lnp64u.Isa.transferByHandle cd to_ hw) := by
  intro σ hctx hne
  unfold Machines.Lnp64u.Isa.transferByHandle
  by_cases hz : hw = 0
  · rw [if_pos hz]
    refine ⟨fun a σ' he => ?_, fun e σ' he => ?_⟩
    · simp only [specM_pure] at he
      obtain ⟨-, rfl⟩ := he
      exact DKeep.refl hctx.ro hctx.fo
    · simp [specM_pure] at he
  · simp only [if_neg hz, specM_bind]
    refine ⟨?_, ?_⟩
    · intro a σ' he
      cases hcl : Machines.Lnp64u.Isa.capLive cd hw σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, -⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok cd _ σ hcl
          subst σ0
          rw [hcl] at he
          obtain ⟨sslot, gg, ee⟩ := r
          simp only [SpecM.get, specM_bind] at he
          cases htc : σ.transferCap cd sslot to_ with
          | none => rw [htc] at he; simp [SpecM.raise] at he
          | some pr =>
              obtain ⟨σ2, ref⟩ := pr
              rw [htc] at he
              simp only [SpecM.set, specM_bind, specM_pure] at he
              injection he with _ h2
              subst h2
              exact dkeep_transferCap hctx hne cd sslot to_ σ2 ref hne hto htc
    · intro er σ' he
      cases hcl : Machines.Lnp64u.Isa.capLive cd hw σ with
      | err e0 σ0 =>
          have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state cd _ σ hcl
          rw [hcl] at he
          injection he with _ h2
          subst h2
          exact DKeep.of_eq hs hctx.ro hctx.fo
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, -⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok cd _ σ hcl
          subst σ0
          rw [hcl] at he
          obtain ⟨sslot, gg, ee⟩ := r
          simp only [SpecM.get, specM_bind] at he
          cases htc : σ.transferCap cd sslot to_ with
          | none =>
              rw [htc] at he
              simp only [SpecM.raise] at he
              injection he with _ h2
              subst h2
              exact DKeep.refl hctx.ro hctx.fo
          | some pr =>
              obtain ⟨σ2, ref⟩ := pr
              rw [htc] at he
              simp [SpecM.set, specM_bind, specM_pure] at he

end SysHelpers

/-! ## The gate ops and `move` -/

section BigOps

variable {d : DomainId} {R : Addr → Prop}

/-- `gate_call` is `DKLe`: err paths are pre-mutation; the ok path is the
capability transfer (to the foreign callee), the activation record (caller =
executing domain), and three `setDom`s that never touch caps/regions. -/
theorem gatecall_dkle (c : Ctx) :
    DKLe d c.d R (Machines.Lnp64u.Isa.Wip.gateCallExec c) := by
  intro σ hctx hne
  have body : ∀ (out : Res Unit), Machines.Lnp64u.Isa.Wip.gateCallExec c σ = out →
      (∀ a σ', out = .ok a σ' → DKeep d c.d R σ σ') ∧
      (∀ er σ', out = .err er σ' → DKeep d c.d R σ σ') := by
    intro out hout
    unfold Machines.Lnp64u.Isa.Wip.gateCallExec at hout
    simp only [SpecM.reg, specM_bind] at hout
    cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 =>
        have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
        rw [hcl] at hout; subst hout
        exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
          simp only [Res.err.injEq] at h; obtain ⟨-, rfl⟩ := h
          exact DKeep.of_eq hs hctx.ro hctx.fo⟩
    | fault f =>
        rw [hcl] at hout; subst hout
        exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
    | ok r σ0 =>
        obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl
        subst σ0
        rw [hcl] at hout; obtain ⟨s0, g0, e⟩ := r
        simp only at hout
        cases hk : e.kind with
        | mem base len perms =>
            rw [hk] at hout; simp only [SpecM.raise] at hout; subst hout
            exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
              simp only [Res.err.injEq] at h; obtain ⟨-, rfl⟩ := h
              exact DKeep.refl hctx.ro hctx.fo⟩
        | gate gid =>
            rw [hk] at hout; simp only [SpecM.get, specM_bind] at hout
            set cal := (σ.gates gid).config.callee with hcaldef
            have hcalne : cal ≠ d := hctx.ncallee gid
            cases hr1 : SpecM.require (σ.gates gid).act.isNone .gateBusy σ with
            | err e1 σ1 =>
                have hst := require_err_state _ _ σ hr1
                rw [hr1] at hout; simp only [specM_bind] at hout; subst hout
                exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                  simp only [Res.err.injEq] at h; obtain ⟨-, rfl⟩ := h
                  exact DKeep.of_eq hst hctx.ro hctx.fo⟩
            | fault f =>
                rw [hr1] at hout; simp only [specM_bind] at hout; subst hout
                exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
            | ok u1 σ1 =>
                have hst := require_ok _ _ σ hr1; subst σ1
                rw [hr1] at hout; simp only [specM_bind] at hout
                cases hr2 : SpecM.require (decide (cal ≠ c.d)) .gateBusy σ with
                | err e2 σ2 =>
                    have hst := require_err_state _ _ σ hr2
                    rw [hr2] at hout; simp only [specM_bind] at hout; subst hout
                    exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                      simp only [Res.err.injEq] at h; obtain ⟨-, rfl⟩ := h
                      exact DKeep.of_eq hst hctx.ro hctx.fo⟩
                | fault f =>
                    rw [hr2] at hout; simp only [specM_bind] at hout; subst hout
                    exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
                | ok u2 σ2 =>
                    have hst := require_ok _ _ σ hr2; subst σ2
                    rw [hr2] at hout; simp only [specM_bind] at hout
                    cases hr3 : SpecM.require (decide ((σ.doms cal).run = .running)) .gateBusy σ with
                    | err e3 σ3 =>
                        have hst := require_err_state _ _ σ hr3
                        rw [hr3] at hout; simp only [specM_bind] at hout; subst hout
                        exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                          simp only [Res.err.injEq] at h; obtain ⟨-, rfl⟩ := h
                          exact DKeep.of_eq hst hctx.ro hctx.fo⟩
                    | fault f =>
                        rw [hr3] at hout; simp only [specM_bind] at hout; subst hout
                        exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
                    | ok u3 σ3 =>
                        have hst := require_ok _ _ σ hr3; subst σ3
                        rw [hr3] at hout; simp only [specM_bind] at hout
                        cases hr4 : SpecM.require (σ.doms cal).serving.isNone .gateBusy σ with
                        | err e4 σ4 =>
                            have hst := require_err_state _ _ σ hr4
                            rw [hr4] at hout; simp only [specM_bind] at hout; subst hout
                            exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                              simp only [Res.err.injEq] at h; obtain ⟨-, rfl⟩ := h
                              exact DKeep.of_eq hst hctx.ro hctx.fo⟩
                        | fault f =>
                            rw [hr4] at hout; simp only [specM_bind] at hout; subst hout
                            exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
                        | ok u4 σ4 =>
                            have hst := require_ok _ _ σ hr4; subst σ4
                            rw [hr4] at hout; simp only [specM_bind] at hout
                            cases hr5 : SpecM.require
                                (decide (Machines.Lnp64u.Isa.Wip.gateDepth c σ ≤ maxChainDepth))
                                .gateBusy σ with
                            | err e5 σ5 =>
                                have hst := require_err_state _ _ σ hr5
                                rw [hr5] at hout; simp only [specM_bind] at hout; subst hout
                                exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                                  simp only [Res.err.injEq] at h; obtain ⟨-, rfl⟩ := h
                                  exact DKeep.of_eq hst hctx.ro hctx.fo⟩
                            | fault f =>
                                rw [hr5] at hout; simp only [specM_bind] at hout; subst hout
                                exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
                            | ok u5 σ5 =>
                                have hst := require_ok _ _ σ hr5; subst σ5
                                rw [hr5] at hout; simp only [specM_bind, SpecM.reg] at hout
                                cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d cal
                                    ((σ.doms c.d).reg c.op.rs2) σ with
                                | fault f =>
                                    rw [htbh] at hout; subst hout
                                    exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
                                | err e6 τ =>
                                    rw [htbh] at hout; subst hout
                                    have hτ := ((DKLe.transferByHandle (d := d) (R := R)
                                      cal _ hcalne) σ hctx hne).2 e6 τ htbh
                                    exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                                      simp only [Res.err.injEq] at h; obtain ⟨-, rfl⟩ := h
                                      exact hτ⟩
                                | ok argHandle τ =>
                                    rw [htbh] at hout
                                    have h1 := ((DKLe.transferByHandle (d := d) (R := R)
                                      cal _ hcalne) σ hctx hne).1 argHandle τ htbh
                                    have hctx1 := hctx.transport hne h1
                                    simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom,
                                      SpecM.modify] at hout
                                    subst hout
                                    refine ⟨fun a σ' h => ?_, fun er σ' h => by simp at h⟩
                                    simp only [Res.ok.injEq] at h; obtain ⟨-, rfl⟩ := h
                                    have h2 := dkeep_gateUpd (cd := c.d) hctx1 gid
                                      { σ.gates gid with act := some ({ caller := c.d, callerRd := c.op.rd, savedRegs := (τ.doms cal).regs, savedPc := (τ.doms cal).pc, savedServing := (τ.doms cal).serving, depth := Machines.Lnp64u.Isa.Wip.gateDepth c σ, donated := (τ.doms c.d).maxDonation } : Activation) }
                                      ((h1.gcfg gid).symm)
                                      (fun a0 ha0 => by
                                        injection ha0 with ha0
                                        exact Or.inr (by rw [← ha0]))
                                    have hctx2 := hctx1.transport hne h2
                                    have h3 := dkeep_setDom (cd := c.d) hctx2 cal
                                      (fun ds => { ds with regs := fun r => if r = (1 : Fin numRegs) then argHandle else 0, pc := (σ.gates gid).config.entry, serving := some gid }) hcalne rfl rfl
                                    have hctx3 := hctx2.transport hne h3
                                    have h4 := dkeep_setDom (cd := c.d) hctx3 c.d
                                      (fun ds => { ds with run := .blocked gid }) hne rfl rfl
                                    exact ((h1.trans h2).trans h3).trans h4
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun er σ' h => (body _ h).2 er σ' rfl⟩

/-- `gate_return` is `DKLe`: outside an activation it faults; inside one it
transfers the reply to the (foreign, blocked) caller, frees the gate, and
restores/resumes via caps/regions-preserving `setDom`s. -/
theorem gatereturn_dkle (c : Ctx) :
    DKLe d c.d R ((do
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
  intro σ hctx hne
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
      (∀ a σ', out = .ok a σ' → DKeep d c.d R σ σ') ∧
      (∀ er σ', out = .err er σ' → DKeep d c.d R σ σ') := by
    intro out hout
    simp only [SpecM.get, specM_bind] at hout
    cases hserv : (σ.doms c.d).serving with
    | none =>
        rw [hserv] at hout; simp only [SpecM.fatal] at hout; subst hout
        exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
    | some gid =>
        simp only [hserv] at hout
        cases hgact : (σ.gates gid).act with
        | none =>
            simp only [hgact] at hout; simp only [SpecM.fatal] at hout; subst hout
            exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
        | some act =>
            have hcallerne : act.caller ≠ d := hctx.acaller gid act hgact
            simp only [hgact, SpecM.reg, specM_bind] at hout
            cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d act.caller
                ((σ.doms c.d).reg c.op.rs1) σ with
            | fault f =>
                rw [htbh] at hout; subst hout
                exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
            | err e1 τ =>
                rw [htbh] at hout; subst hout
                have hτ := ((DKLe.transferByHandle (d := d) (R := R)
                  act.caller _ hcallerne) σ hctx hne).2 e1 τ htbh
                exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                  simp only [Res.err.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hτ⟩
            | ok reply τ =>
                rw [htbh] at hout
                have h1 := ((DKLe.transferByHandle (d := d) (R := R)
                  act.caller _ hcallerne) σ hctx hne).1 reply τ htbh
                have hctx1 := hctx.transport hne h1
                simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom, SpecM.modify,
                  SpecM.setReg] at hout
                subst hout
                refine ⟨fun a σ' h => ?_, fun er σ' h => by simp at h⟩
                simp only [Res.ok.injEq] at h; obtain ⟨-, rfl⟩ := h
                have h2 := dkeep_gateUpd (cd := c.d) hctx1 gid
                  { (τ.gates gid) with act := none } rfl (fun a0 ha0 => by cases ha0)
                have hctx2 := hctx1.transport hne h2
                have h3 := dkeep_setDom (cd := c.d) hctx2 c.d
                  (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing }) hne rfl rfl
                have hctx3 := hctx2.transport hne h3
                have h4 := dkeep_setDom (cd := c.d) hctx3 act.caller
                  (fun ds => { ds with run := .running }) hcallerne rfl rfl
                have hctx4 := hctx3.transport hne h4
                have h5 := dkeep_setRegOther (cd := c.d) hctx4 act.caller hcallerne
                  act.callerRd reply
                exact (((h1.trans h2).trans h3).trans h4).trans h5
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun er σ' h => (body _ h).2 er σ' rfl⟩

/-- `move` is `DKLe`: a read-only prefix, then a Mover job owned by the
executing domain plus the `rd` write. -/
theorem move_dkle (c : Ctx) :
    DKLe d c.d R (Machines.Lnp64u.Isa.Wip.moveExec c) := by
  intro σ hctx hne
  refine ⟨fun x σ' he => ?_, fun x σ' he => ?_⟩
  ·
    simp only [Machines.Lnp64u.Isa.Wip.moveExec, SpecM.get, specM_bind] at he
    cases hr0 : SpecM.require σ.mover.isNone .moverBusy σ with
    | err e0 σ0 => rw [hr0] at he; simp at he
    | fault f => rw [hr0] at he; simp at he
    | ok u0 σ0 =>
        have hh0 := require_ok _ _ σ hr0; subst σ0
        rw [hr0] at he; simp only [SpecM.reg] at he
        set B : Addr := ((σ.doms c.d).reg c.op.rs1).setWidth 12 with hB
        cases hl1 : SpecM.load c.d B σ with
        | err e σe => rw [hl1] at he; simp at he
        | fault f => rw [hl1] at he; simp at he
        | ok srcH σ1 =>
            have hh1 := load_ok _ _ σ hl1; subst σ1; rw [hl1] at he; simp only [specM_bind] at he
            cases hl2 : SpecM.load c.d (B + 1) σ with
            | err e σe => rw [hl2] at he; simp at he
            | fault f => rw [hl2] at he; simp at he
            | ok dstH σ2 =>
                have hh2 := load_ok _ _ σ hl2; subst σ2; rw [hl2] at he; simp only [specM_bind] at he
                cases hl3 : SpecM.load c.d (B + 2) σ with
                | err e σe => rw [hl3] at he; simp at he
                | fault f => rw [hl3] at he; simp at he
                | ok lenW σ3 =>
                    have hh3 := load_ok _ _ σ hl3; subst σ3; rw [hl3] at he; simp only [specM_bind] at he
                    cases hl4 : SpecM.load c.d (B + 3) σ with
                    | err e σe => rw [hl4] at he; simp at he
                    | fault f => rw [hl4] at he; simp at he
                    | ok stW σ4 =>
                        have hh4 := load_ok _ _ σ hl4; subst σ4; rw [hl4] at he; simp only [specM_bind] at he
                        cases hc1 : Machines.Lnp64u.Isa.capLive c.d srcH σ with
                        | err e σe => rw [hc1] at he; simp at he
                        | fault f => rw [hc1] at he; simp at he
                        | ok rs σ5 =>
                            have hcs := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hc1
                            obtain ⟨hhs, hslive⟩ := hcs; subst σ5
                            rw [hc1] at he; obtain ⟨ss, gs_, es⟩ := rs; simp only at he hslive
                            cases hc2 : Machines.Lnp64u.Isa.capLive c.d dstH σ with
                            | err e σe => rw [hc2] at he; simp at he
                            | fault f => rw [hc2] at he; simp at he
                            | ok rdd σ6 =>
                                have hcd := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hc2
                                obtain ⟨hhd, hdlive⟩ := hcd; subst σ6
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
                                                    cases hd0 : SpecM.demand (σ.domCovers c.d (stW.setWidth 12) { r := false, w := true, x := false }) .memoryAuthority σ with
                                                    | err e σe => rw [hd0] at he; simp at he
                                                    | fault f => rw [hd0] at he; simp at he
                                                    | ok _ σdd =>
                                                        have := demand_ok _ _ σ hd0; subst σdd; rw [hd0] at he
                                                        simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
                                                        injection he with _ h2; subst h2
                                                        have h1 := dkeep_setMover (cd := c.d) hctx
                                                          { owner := c.d, src := ⟨c.d, ss, gs_⟩, dst := ⟨c.d, sd, gd⟩
                                                            srcCur := sb, dstCur := db, remaining := lenW.toNat
                                                            statusAddr := stW.setWidth 12 } rfl
                                                        have hctx1 := hctx.transport hne h1
                                                        exact h1.trans
                                                          (dkeep_setRegOther (cd := c.d) hctx1 c.d hne c.op.rd 0)
  ·
    simp only [Machines.Lnp64u.Isa.Wip.moveExec, SpecM.get, specM_bind] at he
    have keep_of : ∀ {σe : MachineState}, σe = σ → (Res.err (α := Unit) x σe = .err x σ') → DKeep d c.d R σ σ' := by
      intro σe hq hee
      injection hee with _ h2
      subst h2
      exact DKeep.of_eq hq hctx.ro hctx.fo
    cases hr0 : SpecM.require σ.mover.isNone .moverBusy σ with
    | err e0 σ0 =>
        have hq := require_err_state _ _ σ hr0
        rw [hr0] at he
        injection he with h1 h2; subst h1; subst h2; subst hq
        exact DKeep.refl hctx.ro hctx.fo
    | fault f => rw [hr0] at he; simp at he
    | ok u0 σ0 =>
        have hh0 := require_ok _ _ σ hr0; subst σ0
        rw [hr0] at he; simp only [SpecM.reg] at he
        set B : Addr := ((σ.doms c.d).reg c.op.rs1).setWidth 12 with hB
        cases hl1 : SpecM.load c.d B σ with
        | err e σe =>
            have hq := load_err_state _ _ σ hl1
            rw [hl1] at he; injection he with h1 h2; subst h1; subst h2; subst hq
            exact DKeep.refl hctx.ro hctx.fo
        | fault f => rw [hl1] at he; simp at he
        | ok srcH σ1 =>
            have hh1 := load_ok _ _ σ hl1; subst σ1; rw [hl1] at he; simp only [specM_bind] at he
            cases hl2 : SpecM.load c.d (B + 1) σ with
            | err e σe =>
                have hq := load_err_state _ _ σ hl2
                rw [hl2] at he; injection he with h1 h2; subst h1; subst h2; subst hq
                exact DKeep.refl hctx.ro hctx.fo
            | fault f => rw [hl2] at he; simp at he
            | ok dstH σ2 =>
                have hh2 := load_ok _ _ σ hl2; subst σ2; rw [hl2] at he; simp only [specM_bind] at he
                cases hl3 : SpecM.load c.d (B + 2) σ with
                | err e σe =>
                    have hq := load_err_state _ _ σ hl3
                    rw [hl3] at he; injection he with h1 h2; subst h1; subst h2; subst hq
                    exact DKeep.refl hctx.ro hctx.fo
                | fault f => rw [hl3] at he; simp at he
                | ok lenW σ3 =>
                    have hh3 := load_ok _ _ σ hl3; subst σ3; rw [hl3] at he; simp only [specM_bind] at he
                    cases hl4 : SpecM.load c.d (B + 3) σ with
                    | err e σe =>
                        have hq := load_err_state _ _ σ hl4
                        rw [hl4] at he; injection he with h1 h2; subst h1; subst h2; subst hq
                        exact DKeep.refl hctx.ro hctx.fo
                    | fault f => rw [hl4] at he; simp at he
                    | ok stW σ4 =>
                        have hh4 := load_ok _ _ σ hl4; subst σ4; rw [hl4] at he; simp only [specM_bind] at he
                        cases hc1 : Machines.Lnp64u.Isa.capLive c.d srcH σ with
                        | err e σe =>
                            have hq := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hc1
                            rw [hc1] at he; injection he with h1 h2; subst h1; subst h2; subst hq
                            exact DKeep.refl hctx.ro hctx.fo
                        | fault f => rw [hc1] at he; simp at he
                        | ok rs σ5 =>
                            have hcs := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hc1
                            obtain ⟨hhs, hslive⟩ := hcs; subst σ5
                            rw [hc1] at he; obtain ⟨ss, gs_, es⟩ := rs; simp only at he hslive
                            cases hc2 : Machines.Lnp64u.Isa.capLive c.d dstH σ with
                            | err e σe =>
                                have hq := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hc2
                                rw [hc2] at he; injection he with h1 h2; subst h1; subst h2; subst hq
                                exact DKeep.refl hctx.ro hctx.fo
                            | fault f => rw [hc2] at he; simp at he
                            | ok rdd σ6 =>
                                have hcd := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hc2
                                obtain ⟨hhd, hdlive⟩ := hcd; subst σ6
                                rw [hc2] at he; obtain ⟨sd, gd, ed⟩ := rdd; simp only at he hdlive
                                cases hks : es.kind with
                                | gate _ =>
                                    rw [hks] at he
                                    cases hkd : ed.kind with
                                    | gate _ =>
                                        rw [hkd] at he; simp only [SpecM.raise] at he
                                        injection he with h1 h2; subst h1; subst h2
                                        exact DKeep.refl hctx.ro hctx.fo
                                    | mem _ _ _ =>
                                        rw [hkd] at he; simp only [SpecM.raise] at he
                                        injection he with h1 h2; subst h1; subst h2
                                        exact DKeep.refl hctx.ro hctx.fo
                                | mem sb sl sp =>
                                    cases hkd : ed.kind with
                                    | gate _ =>
                                        rw [hks, hkd] at he; simp only [SpecM.raise] at he
                                        injection he with h1 h2; subst h1; subst h2
                                        exact DKeep.refl hctx.ro hctx.fo
                                    | mem db dl dp =>
                                        rw [hks, hkd] at he; simp only [specM_bind] at he
                                        cases hq1 : SpecM.require sp.r .permDenied σ with
                                        | err e σe =>
                                            have hq := require_err_state _ _ σ hq1
                                            rw [hq1] at he; injection he with h1 h2; subst h1; subst h2; subst hq
                                            exact DKeep.refl hctx.ro hctx.fo
                                        | fault f => rw [hq1] at he; simp at he
                                        | ok _ σq1 =>
                                            have := require_ok _ _ σ hq1; subst σq1; rw [hq1] at he; simp only [specM_bind] at he
                                            cases hq2 : SpecM.require dp.w .permDenied σ with
                                            | err e σe =>
                                                have hq := require_err_state _ _ σ hq2
                                                rw [hq2] at he; injection he with h1 h2; subst h1; subst h2; subst hq
                                                exact DKeep.refl hctx.ro hctx.fo
                                            | fault f => rw [hq2] at he; simp at he
                                            | ok _ σq2 =>
                                                have := require_ok _ _ σ hq2; subst σq2; rw [hq2] at he; simp only [specM_bind] at he
                                                cases hq3 : SpecM.require (decide (lenW.toNat ≤ sl.toNat) && decide (lenW.toNat ≤ dl.toNat)) .outOfRange σ with
                                                | err e σe =>
                                                    have hq := require_err_state _ _ σ hq3
                                                    rw [hq3] at he; injection he with h1 h2; subst h1; subst h2; subst hq
                                                    exact DKeep.refl hctx.ro hctx.fo
                                                | fault f => rw [hq3] at he; simp at he
                                                | ok _ σq3 =>
                                                    have := require_ok _ _ σ hq3; subst σq3; rw [hq3] at he; simp only [SpecM.get, specM_bind] at he
                                                    cases hd0 : SpecM.demand (σ.domCovers c.d (stW.setWidth 12) { r := false, w := true, x := false }) .memoryAuthority σ with
                                                    | err e σe => exact absurd hd0 (by simp [SpecM.demand]; split <;> simp [SpecM.fatal])
                                                    | fault f => rw [hd0] at he; simp at he
                                                    | ok _ σdd =>
                                                        have := demand_ok _ _ σ hd0; subst σdd; rw [hd0] at he
                                                        simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he

end BigOps

/-! ## The system-op dispatch -/

section Dispatch

variable {d : DomainId} {R : Addr → Prop}

/-- **The system opcodes are `DKLe`.** -/
theorem system_dkle : ∀ instr ∈ Machines.Lnp64u.Isa.system, ∀ c : Ctx,
    DKLe d c.d R (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  case _ => -- cap_dup
    intro σ hctx hne
    have hstep : ∀ (kd : CapKind)
        (hk : c.d ≠ d → ∀ b len p, kd = .mem b len p → ∀ a : Addr, b.toNat ≤ a.toNat →
          a.toNat < b.toNat + len.toNat → ¬ R a)
        (sl : Slot) (gg : Gen) (x : Unit) (σ' : MachineState),
        ((Machines.Lnp64u.Isa.allocDerived c.d kd ⟨c.d, sl, gg⟩ >>=
          fun h => SpecM.setReg c.d c.op.rd h) σ = .ok x σ' → DKeep d c.d R σ σ') ∧
        (∀ er, (Machines.Lnp64u.Isa.allocDerived c.d kd ⟨c.d, sl, gg⟩ >>=
          fun h => SpecM.setReg c.d c.op.rd h) σ = .err er σ' → DKeep d c.d R σ σ') := by
      intro kd hk sl gg x σ'
      have htail := DKLe.bind (DKLe.allocDerived (d := d) (cd := c.d) (R := R)
          c.d kd ⟨c.d, sl, gg⟩ (fun h => hk h))
        (fun h => DKLe.setReg (d := d) (cd := c.d) (R := R) c.op.rd h) σ hctx hne
      exact ⟨fun he => htail.1 x σ' he, fun er he => htail.2 er σ' he⟩
    refine ⟨fun x σ' he => ?_, fun er σ' he => ?_⟩
    · simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl
          subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he hlc
          cases hk : e.kind with
          | gate g =>
              rw [hk] at he; simp only [specM_pure, specM_bind] at he
              cases hal : Machines.Lnp64u.Isa.allocDerived c.d (.gate g) ⟨c.d, sl, gg⟩ σ with
              | err e1 σ1 => rw [hal] at he; simp at he
              | fault f => rw [hal] at he; simp at he
              | ok hh τ =>
                  refine (hstep (.gate g) (fun _ b len p hcontra => by cases hcontra)
                    sl gg x σ').1 ?_
                  rw [specM_bind, hal]
                  rw [hal] at he
                  exact he
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : Machines.Lnp64u.Isa.narrow base len perms
                  ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => rw [hn] at he; simp at he
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1
                  subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  refine (hstep kd (fun hnd => narrow_off_R hn
                    (entry_off_R hctx hnd (caps_of_liveCap hlc) hk)) sl gg x σ').1 ?_
                  rw [specM_bind]
                  exact he
    · simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 =>
          have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
          rw [hcl] at he; injection he with _ h2; subst h2
          exact DKeep.of_eq hs hctx.ro hctx.fo
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl
          subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he hlc
          cases hk : e.kind with
          | gate g =>
              rw [hk] at he; simp only [specM_pure, specM_bind] at he
              refine (hstep (.gate g) (fun _ b len p hcontra => by cases hcontra)
                sl gg () σ').2 er ?_
              rw [specM_bind]
              exact he
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : Machines.Lnp64u.Isa.narrow base len perms
                  ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 =>
                  have hs := Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms _ σ hn
                  rw [hn] at he; injection he with _ h2; subst h2
                  exact DKeep.of_eq hs hctx.ro hctx.fo
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1
                  subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  refine (hstep kd (fun hnd => narrow_off_R hn
                    (entry_off_R hctx hnd (caps_of_liveCap hlc) hk)) sl gg () σ').2 er ?_
                  rw [specM_bind]
                  exact he
  case _ => -- cap_drop
    intro σ hctx hne
    refine ⟨fun x σ' he => ?_, fun er σ' he => ?_⟩
    · simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl
          subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          simp only [SpecM.get, specM_bind, SpecM.set, SpecM.setReg, SpecM.modify] at he
          injection he with _ h2
          subst h2
          have h1 : DKeep d c.d R σ (match σ.parentOf c.d sl with
              | some p => σ.reparent ⟨c.d, sl, gg⟩ p
              | none => σ.orphanChildren ⟨c.d, sl, gg⟩) := by
            cases hpar : σ.parentOf c.d sl with
            | some p => exact dkeep_reparent hctx _ p
            | none => exact dkeep_orphanChildren hctx _
          have hctx1 := hctx.transport hne h1
          have h2 := dkeep_clearSlot (cd := c.d) hctx1 c.d sl hne
          have hctx2 := hctx1.transport hne h2
          have h3 := dkeep_sweepRegions (cd := c.d) hctx2
          have hctx3 := hctx2.transport hne h3
          have h4 := dkeep_sweepMover (cd := c.d) hctx3
          have hctx4 := hctx3.transport hne h4
          have h5 := dkeep_setRegOther (cd := c.d) hctx4 c.d hne c.op.rd 0
          exact (((h1.trans h2).trans h3).trans h4).trans h5
    · simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 =>
          have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
          rw [hcl] at he; injection he with _ h2; subst h2
          exact DKeep.of_eq hs hctx.ro hctx.fo
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl
          subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          simp [SpecM.get, specM_bind, SpecM.set, SpecM.setReg, SpecM.modify] at he
  case _ => -- cap_revoke
    intro σ hctx hne
    refine ⟨fun x σ' he => ?_, fun er σ' he => ?_⟩
    · simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl
          subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hr1 : SpecM.require (e.kind.cls = .mem) .badCap σ with
          | err e1 σ1 => rw [hr1] at he; simp at he
          | fault f => rw [hr1] at he; simp at he
          | ok u1 σ1 =>
              have hst := require_ok _ _ σ hr1; subst σ1
              rw [hr1] at he
              simp only [SpecM.get, specM_bind, SpecM.set, SpecM.setReg, SpecM.modify] at he
              injection he with _ h2
              subst h2
              have h1 := dkeep_destroyMarked (cd := c.d) hctx (σ.marks ⟨c.d, sl, gg⟩)
                (fun s => marks_d_false hctx _ s)
              have hctx1 := hctx.transport hne h1
              have h2 := dkeep_sweepRegions (cd := c.d) hctx1
              have hctx2 := hctx1.transport hne h2
              have h3 := dkeep_sweepMover (cd := c.d) hctx2
              have hctx3 := hctx2.transport hne h3
              have h4 := dkeep_setRegOther (cd := c.d) hctx3 c.d hne c.op.rd 0
              exact ((h1.trans h2).trans h3).trans h4
    · simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 =>
          have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
          rw [hcl] at he; injection he with _ h2; subst h2
          exact DKeep.of_eq hs hctx.ro hctx.fo
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl
          subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hr1 : SpecM.require (e.kind.cls = .mem) .badCap σ with
          | err e1 σ1 =>
              have hs := require_err_state _ _ σ hr1
              rw [hr1] at he; simp only [specM_bind] at he
              injection he with _ h2; subst h2
              exact DKeep.of_eq hs hctx.ro hctx.fo
          | fault f => rw [hr1] at he; simp at he
          | ok u1 σ1 =>
              have hst := require_ok _ _ σ hr1; subst σ1
              rw [hr1] at he
              simp [SpecM.get, specM_bind, SpecM.set, SpecM.setReg, SpecM.modify] at he
  case _ => -- mem_grant
    intro σ hctx hne
    have hstep : ∀ (kd : CapKind) (owner : DomainId)
        (hk : owner ≠ d → ∀ b len p, kd = .mem b len p → ∀ a : Addr, b.toNat ≤ a.toNat →
          a.toNat < b.toNat + len.toNat → ¬ R a)
        (sl : Slot) (gg : Gen) (x : Unit) (σ' : MachineState),
        ((Machines.Lnp64u.Isa.allocDerived owner kd ⟨c.d, sl, gg⟩ >>=
          fun h => SpecM.setReg c.d c.op.rd h) σ = .ok x σ' → DKeep d c.d R σ σ') ∧
        (∀ er, (Machines.Lnp64u.Isa.allocDerived owner kd ⟨c.d, sl, gg⟩ >>=
          fun h => SpecM.setReg c.d c.op.rd h) σ = .err er σ' → DKeep d c.d R σ σ') := by
      intro kd owner hk sl gg x σ'
      have htail := DKLe.bind (DKLe.allocDerived (d := d) (cd := c.d) (R := R)
          owner kd ⟨c.d, sl, gg⟩ hk)
        (fun h => DKLe.setReg (d := d) (cd := c.d) (R := R) c.op.rd h) σ hctx hne
      exact ⟨fun he => htail.1 x σ' he, fun er he => htail.2 er σ' he⟩
    refine ⟨fun x σ' he => ?_, fun er σ' he => ?_⟩
    · simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl
          subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he hlc
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp [SpecM.raise] at he
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : Machines.Lnp64u.Isa.narrow base len perms
                  ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => rw [hn] at he; simp at he
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1
                  subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  refine (hstep kd (Machines.Lnp64u.Isa.descDom ((σ.doms c.d).reg c.op.rs2))
                    (fun _ => narrow_off_R hn
                      (entry_off_R hctx hne (caps_of_liveCap hlc) hk)) sl gg x σ').1 ?_
                  rw [specM_bind]
                  exact he
    · simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 =>
          have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
          rw [hcl] at he; injection he with _ h2; subst h2
          exact DKeep.of_eq hs hctx.ro hctx.fo
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl
          subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he hlc
          cases hk : e.kind with
          | gate g =>
              rw [hk] at he; simp only [SpecM.raise] at he
              injection he with _ h2; subst h2
              exact DKeep.refl hctx.ro hctx.fo
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : Machines.Lnp64u.Isa.narrow base len perms
                  ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 =>
                  have hs := Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms _ σ hn
                  rw [hn] at he; injection he with _ h2; subst h2
                  exact DKeep.of_eq hs hctx.ro hctx.fo
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1
                  subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  refine (hstep kd (Machines.Lnp64u.Isa.descDom ((σ.doms c.d).reg c.op.rs2))
                    (fun _ => narrow_off_R hn
                      (entry_off_R hctx hne (caps_of_liveCap hlc) hk)) sl gg () σ').2 er ?_
                  rw [specM_bind]
                  exact he
  case _ => -- map
    intro σ hctx hne
    refine ⟨fun x σ' he => ?_, fun er σ' he => ?_⟩
    · simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl
          subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he hlc
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp [SpecM.raise] at he
          | mem base len perms =>
              rw [hk] at he
              simp only [SpecM.updDom, SpecM.modify, specM_bind, SpecM.setReg] at he
              injection he with _ h2
              subst h2
              have h1 := dkeep_regionsSet (cd := c.d) hctx hne
                ⟨(c.op.imm.extractLsb' 0 2).toNat, (c.op.imm.extractLsb' 0 2).isLt⟩
                (some { base := base, len := len, perms := perms
                        backing := ⟨c.d, sl, gg⟩ })
                (fun rg hrg => by
                  injection hrg with hrg
                  subst hrg
                  exact ⟨rfl, entry_off_R hctx hne (caps_of_liveCap hlc) hk⟩)
              have hctx1 := hctx.transport hne h1
              exact h1.trans (dkeep_setRegOther (cd := c.d) hctx1 c.d hne c.op.rd 0)
    · simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 =>
          have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
          rw [hcl] at he; injection he with _ h2; subst h2
          exact DKeep.of_eq hs hctx.ro hctx.fo
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, hlc⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl
          subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g =>
              rw [hk] at he; simp only [SpecM.raise] at he
              injection he with _ h2; subst h2
              exact DKeep.refl hctx.ro hctx.fo
          | mem base len perms =>
              rw [hk] at he
              simp [SpecM.updDom, SpecM.modify, specM_bind, SpecM.setReg] at he
  case _ => -- unmap
    intro σ hctx hne
    refine ⟨fun x σ' he => ?_, fun er σ' he => ?_⟩
    · simp only [SpecM.updDom, SpecM.modify, specM_bind, SpecM.setReg] at he
      injection he with _ h2
      subst h2
      have h1 := dkeep_regionsSet (cd := c.d) hctx hne
        ⟨(c.op.imm.extractLsb' 0 2).toNat, (c.op.imm.extractLsb' 0 2).isLt⟩
        none (fun rg hrg => by cases hrg)
      have hctx1 := hctx.transport hne h1
      exact h1.trans (dkeep_setRegOther (cd := c.d) hctx1 c.d hne c.op.rd 0)
    · simp [SpecM.updDom, SpecM.modify, specM_bind, SpecM.setReg] at he
  case _ => exact fun σ hctx hne => gatecall_dkle c σ hctx hne
  case _ => exact fun σ hctx hne => gatereturn_dkle c σ hctx hne
  case _ => exact fun σ hctx hne => move_dkle c σ hctx hne
  case _ => -- yield
    exact DKLe.bind (DKLe.updDomExec _ (fun _ => rfl) (fun _ => rfl))
      (fun _ => DKLe.setReg _ _)
  case _ => -- halt
    intro σ hctx hne
    refine ⟨fun a σ' he => ?_, fun e σ' he => by simp [SpecM.modify] at he⟩
    simp only [SpecM.modify] at he
    injection he with _ h2
    subst h2
    exact dkeep_haltDom hctx hne c.d 0 hne

/-- **Every instruction of the ISA is `DKLe`.** -/
theorem exec_dkle : ∀ instr ∈ isa, ∀ c : Ctx, DKLe d c.d R (instr.sem.exec c) := by
  intro instr hmem c
  have hmem' : instr ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
    have hiseq : Machines.Lnp64u.isa =
      (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray := rfl
    rw [hiseq, Array.mem_toArray] at hmem
    exact hmem
  rcases List.mem_append.mp hmem' with hb | hs
  · exact base_dkle instr hb c rfl
  · exact system_dkle instr hs c

end Dispatch

/-! ## Cycle-level assembly: `retire` and `corePhase` -/

/-- The cycle-level frame at `d`, with the executing domain abstracted. -/
structure DCycle (d : DomainId) (R : Addr → Prop) (σ σ' : MachineState) : Prop where
  ddoms : σ'.doms d = σ.doms d
  mem : ∀ a, R a → σ'.mem a = σ.mem a
  gcfg : ∀ g, (σ'.gates g).config = (σ.gates g).config
  acts : ∀ g a, (σ'.gates g).act = some a → (σ.gates g).act = some a ∨ a.caller ≠ d
  mover : ∀ job, σ'.mover = some job → σ.mover = some job ∨ job.owner ≠ d
  ro : RegionsOwn σ'
  fo : ForeignOff d R σ'

section Cycle

variable {d : DomainId} {R : Addr → Prop} {σ : MachineState}

theorem DKeep.toCycle {cd : DomainId} {σ' : MachineState} (hne : cd ≠ d)
    (h : DKeep d cd R σ σ') : DCycle d R σ σ' :=
  ⟨h.ddoms, h.mem, h.gcfg,
   fun g a ha => (h.acts g a ha).imp id (fun hc => by rw [hc]; exact hne),
   fun job hj => (h.mover job hj).imp id (fun hc => by rw [hc]; exact hne),
   h.ro, h.fo⟩

theorem DCycle.refl (hro : RegionsOwn σ) (hfo : ForeignOff d R σ) : DCycle d R σ σ :=
  ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ h => Or.inl h, fun _ h => Or.inl h, hro, hfo⟩

/-- Setting only the in-flight latch on the left is transparent. -/
theorem DCycle.castInflight {σ' : MachineState} {i : Option InFlight}
    (h : DCycle d R { σ with inflight := i } σ') : DCycle d R σ σ' :=
  ⟨h.ddoms, h.mem, h.gcfg, h.acts, h.mover, h.ro, h.fo⟩

/-- The context ignores the in-flight latch. -/
theorem DCtx.setInflight (hctx : DCtx d R σ) (i : Option InFlight) :
    DCtx d R { σ with inflight := i } :=
  ⟨hctx.dfull, hctx.dlin, hctx.dent, hctx.dgates, hctx.dserv, hctx.dnoblk, hctx.dreg,
   hctx.ro, hctx.fo, hctx.covOff, hctx.movOff, hctx.ncallee, hctx.acaller⟩

/-- No serving chain from a foreign domain ends at `d` (`d` is never a
recorded caller). -/
theorem chainOrigin_ne (hctx : DCtx d R σ) :
    ∀ (fuel : Nat) (e : DomainId), e ≠ d → σ.chainOrigin fuel e ≠ d := by
  intro fuel
  induction fuel with
  | zero => intro e he; exact he
  | succ n ih =>
      intro e he
      unfold MachineState.chainOrigin
      cases hs : (σ.doms e).serving with
      | none => simp only [hs]; exact he
      | some g =>
          simp only [hs]
          cases ha : (σ.gates g).act with
          | some a => simp only [ha]; exact ih a.caller (hctx.acaller g a ha)
          | none => simp only [ha]; exact he

theorem payer_ne (hctx : DCtx d R σ) (e : DomainId) (he : e ≠ d) : σ.payer e ≠ d :=
  chainOrigin_ne hctx maxChainDepth e he

/-- Charging a payer's budget (and latching) is a `DCycle`. -/
theorem dcycle_charge (hctx : DCtx d R σ) (p : DomainId) (hp : p ≠ d)
    (f : DomainState → DomainState)
    (hcaps : (f (σ.doms p)).caps = (σ.doms p).caps)
    (hreg : (f (σ.doms p)).regions = (σ.doms p).regions)
    (i : Option InFlight) :
    DCycle d R σ { σ.setDom p f with inflight := i } := by
  have hk : DKeep d p R σ (σ.setDom p f) := dkeep_setDom hctx p f hp hcaps hreg
  exact
    { ddoms := hk.ddoms, mem := hk.mem, gcfg := hk.gcfg
      acts := fun g a ha => (hk.acts g a ha).imp id (fun hc => by rw [hc]; exact hp)
      mover := fun job hj => (hk.mover job hj).imp id (fun hc => by rw [hc]; exact hp)
      ro := hk.ro, fo := hk.fo }

/-- **`retire` of a foreign instruction is a `DCycle`.** -/
theorem retire_dcycle (σ : MachineState) (e : DomainId) (w : Loom.Word32)
    (hctx : DCtx d R σ) (hne : e ≠ d) :
    DCycle d R σ (retire σ e w) := by
  unfold retire
  split
  · exact (dkeep_haltDom (cd := e) hctx hne e _ hne).toCycle hne
  · rename_i instr hdec
    set σ1 := σ.setDom e (fun ds => { ds with pc := ds.pc + 1 }) with hσ1
    have h1 : DKeep d e R σ σ1 := dkeep_setDom hctx e _ hne rfl rfl
    have hctx1 : DCtx d R σ1 := hctx.transport hne h1
    have hexk := exec_dkle instr (Loom.Isa.decode_mem isa hdec)
      { d := e, pc := (σ.doms e).pc, op := operandsOf w } σ1 hctx1 hne
    cases hexr : instr.sem.exec { d := e, pc := (σ.doms e).pc, op := operandsOf w } σ1 with
    | ok a σ' =>
        simp only [hexr]
        exact (h1.trans (hexk.1 a σ' hexr)).toCycle hne
    | err er σ' =>
        simp only [hexr]
        have h2 := hexk.2 er σ' hexr
        have hctx2 := hctx1.transport hne h2
        exact ((h1.trans h2).trans
          (dkeep_setRegOther (cd := e) hctx2 e hne (operandsOf w).rd er.toWord)).toCycle hne
    | fault f =>
        simp only [hexr]
        exact (dkeep_haltDom (cd := e) hctx hne e _ hne).toCycle hne

/-- **A `corePhase` cycle with no `d`-event is a `DCycle`.** -/
theorem corePhase_dcycle (m : Manifest) (σ : MachineState) (hctx : DCtx d R σ)
    (hnr : ∀ fl, σ.inflight = some fl → fl.dom = d → 1 < fl.cyclesLeft)
    (hni : σ.inflight = none → schedule m σ ≠ some d) :
    DCycle d R σ (corePhase m σ) := by
  unfold corePhase
  cases hinf : σ.inflight with
  | some fl =>
      by_cases hcl : fl.cyclesLeft ≤ 1
      · simp only [hcl, if_true]
        have hfld : fl.dom ≠ d := by
          intro hcontra
          have := hnr fl hinf hcontra
          omega
        have hctxI : DCtx d R { σ with inflight := none } := hctx.setInflight none
        exact (retire_dcycle { σ with inflight := none } fl.dom fl.word
          hctxI hfld).castInflight
      · simp only [hcl, if_false]
        exact
          { ddoms := rfl, mem := fun _ _ => rfl, gcfg := fun _ => rfl
            acts := fun _ _ h => Or.inl h, mover := fun _ h => Or.inl h
            ro := hctx.ro, fo := hctx.fo }
  | none =>
      simp only []
      split
      · exact DCycle.refl hctx.ro hctx.fo
      · rename_i e hsched
        have hne : e ≠ d := by
          intro hcontra
          subst hcontra
          exact hni hinf hsched
        split
        · exact (dkeep_haltDom (cd := e) hctx hne e _ hne).toCycle hne
        · rename_i w hfetch
          split
          · exact (dkeep_haltDom (cd := e) hctx hne e _ hne).toCycle hne
          · rename_i instr hdec
            have hpne : σ.payer e ≠ d := payer_ne hctx e hne
            by_cases hbud : instr.cost.cost ≤ (σ.doms (σ.payer e)).budget
            · simp only [hbud, if_true]
              cases hservd : (σ.doms e).serving with
              | none =>
                  simp only [hservd]
                  exact dcycle_charge hctx (σ.payer e) hpne _ rfl rfl _
              | some g =>
                  simp only [hservd]
                  cases hactg : (σ.gates g).act with
                  | none => exact (dkeep_haltDom (cd := e) hctx hne e _ hne).toCycle hne
                  | some a =>
                      simp only [hactg]
                      by_cases hdon : instr.cost.cost ≤ a.donated
                      · simp only [hdon, if_true]
                        have hcaller : a.caller ≠ d := hctx.acaller g a hactg
                        set σ' := σ.setDom (σ.payer e)
                          (fun ds => { ds with budget := ds.budget - instr.cost.cost })
                          with hσ'
                        have h1 : DKeep d (σ.payer e) R σ σ' :=
                          dkeep_setDom hctx (σ.payer e) _ hpne rfl rfl
                        have hcy1 : DCycle d R σ σ' := h1.toCycle hpne
                        refine
                          { ddoms := hcy1.ddoms, mem := hcy1.mem
                            gcfg := fun g' => ?_, acts := fun g' a' ha' => ?_
                            mover := hcy1.mover, ro := hcy1.ro, fo := hcy1.fo }
                        · show (Loom.Fun.update σ'.gates g _ g').config = _
                          by_cases hgg : g' = g
                          · subst hgg
                            rw [Loom.Fun.update_same]
                            exact hcy1.gcfg g'
                          · rw [Loom.Fun.update_ne _ _ _ _ hgg]
                            exact hcy1.gcfg g'
                        · have ha'' : (Loom.Fun.update σ'.gates g
                              { σ'.gates g with act := some { a with
                                donated := a.donated - instr.cost.cost } } g').act
                              = some a' := ha'
                          by_cases hgg : g' = g
                          · subst hgg
                            rw [Loom.Fun.update_same] at ha''
                            refine Or.inr ?_
                            injection ha'' with ha''
                            rw [← ha'']
                            exact hcaller
                          · rw [Loom.Fun.update_ne _ _ _ _ hgg] at ha''
                            exact hcy1.acts g' a' ha''
                      · simp only [hdon, if_false]
                        exact (dkeep_haltDom (cd := e) hctx hne e _ hne).toCycle hne
            · simp only [hbud, if_false]
              exact DCycle.refl hctx.ro hctx.fo

end Cycle

end Machines.Lnp64u.DFrame
