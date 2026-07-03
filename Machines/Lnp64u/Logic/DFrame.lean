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

end Kernel

end Machines.Lnp64u.DFrame
