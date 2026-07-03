import Machines.Lnp64u.Kernel
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

/-!
# Kernel-function lemmas (L1 support)

Basic facts about the pure capability-kernel functions, proved once and
reused across T2/T3/T8/T9. Kept separate from the theorem files so the
statements there stay clean.
-/

namespace Machines.Lnp64u

open Loom

private theorem genRetired_toNat : genRetired.toNat = 255 := rfl

/-- `bumpGen` strictly increases a non-retired generation. -/
theorem bumpGen_gt (g : Gen) (h : g ≠ genRetired) : g.toNat < (bumpGen g).toNat := by
  unfold bumpGen
  simp only [h, if_false]
  have hne : g.toNat ≠ 255 := fun hc => h (BitVec.eq_of_toNat_eq (by
    rw [genRetired_toNat]; exact hc))
  have hlt := g.isLt
  have hadd : (g + 1).toNat = g.toNat + 1 := by
    rw [BitVec.toNat_add]
    have : (1 : Gen).toNat = 1 := rfl
    rw [this, Nat.mod_eq_of_lt (by omega)]
  omega

/-- `bumpGen` never decreases a generation. -/
theorem bumpGen_ge (g : Gen) : g.toNat ≤ (bumpGen g).toNat := by
  by_cases h : g = genRetired
  · subst h; unfold bumpGen; simp
  · exact Nat.le_of_lt (bumpGen_gt g h)

/-- `clearSlot` bumps exactly the cleared slot's generation and leaves
others (and other domains) untouched. -/
theorem clearSlot_slotGen (σ : MachineState) (d : DomainId) (s : Slot)
    (d' : DomainId) (s' : Slot) :
    ((σ.clearSlot d s).doms d').slotGen s' =
      if d' = d ∧ s' = s then bumpGen ((σ.doms d).slotGen s)
      else (σ.doms d').slotGen s' := by
  unfold MachineState.clearSlot MachineState.setDom
  by_cases hd : d' = d
  · subst hd
    by_cases hs : s' = s
    · subst hs; simp [Loom.Fun.update]
    · simp [Loom.Fun.update, hs]
  · simp [Loom.Fun.update, hd]


/-! ## setReg and haltDom structural lemmas -/

@[simp] theorem setReg_caps (ds : DomainState) (r : RegId) (v : Loom.Word32) :
    (ds.setReg r v).caps = ds.caps := by unfold DomainState.setReg; split <;> rfl
@[simp] theorem setReg_lineage (ds : DomainState) (r : RegId) (v : Loom.Word32) :
    (ds.setReg r v).lineage = ds.lineage := by unfold DomainState.setReg; split <;> rfl
@[simp] theorem setReg_slotGen (ds : DomainState) (r : RegId) (v : Loom.Word32) :
    (ds.setReg r v).slotGen = ds.slotGen := by unfold DomainState.setReg; split <;> rfl
@[simp] theorem setReg_regions (ds : DomainState) (r : RegId) (v : Loom.Word32) :
    (ds.setReg r v).regions = ds.regions := by unfold DomainState.setReg; split <;> rfl
@[simp] theorem setReg_run (ds : DomainState) (r : RegId) (v : Loom.Word32) :
    (ds.setReg r v).run = ds.run := by unfold DomainState.setReg; split <;> rfl
@[simp] theorem setReg_serving (ds : DomainState) (r : RegId) (v : Loom.Word32) :
    (ds.setReg r v).serving = ds.serving := by unfold DomainState.setReg; split <;> rfl


section HaltDom
variable (σ : MachineState) (d : DomainId) (c : Loom.Word32)

/-! ### haltBase projections (setDom of the halted domain) -/

@[simp] theorem haltBase_caps (d' : DomainId) :
    ((σ.haltBase d c).doms d').caps = (σ.doms d').caps := by
  unfold MachineState.haltBase MachineState.setDom
  by_cases hd : d' = d
  · subst hd; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd]
@[simp] theorem haltBase_lineage (d' : DomainId) :
    ((σ.haltBase d c).doms d').lineage = (σ.doms d').lineage := by
  unfold MachineState.haltBase MachineState.setDom
  by_cases hd : d' = d
  · subst hd; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd]
@[simp] theorem haltBase_slotGen (d' : DomainId) :
    ((σ.haltBase d c).doms d').slotGen = (σ.doms d').slotGen := by
  unfold MachineState.haltBase MachineState.setDom
  by_cases hd : d' = d
  · subst hd; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd]
@[simp] theorem haltBase_regions (d' : DomainId) :
    ((σ.haltBase d c).doms d').regions = (σ.doms d').regions := by
  unfold MachineState.haltBase MachineState.setDom
  by_cases hd : d' = d
  · subst hd; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd]
@[simp] theorem haltBase_run (d' : DomainId) :
    ((σ.haltBase d c).doms d').run = if d' = d then .halted else (σ.doms d').run := by
  unfold MachineState.haltBase MachineState.setDom
  by_cases hd : d' = d
  · subst hd; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd, hd]
@[simp] theorem haltBase_serving (d' : DomainId) :
    ((σ.haltBase d c).doms d').serving = if d' = d then none else (σ.doms d').serving := by
  unfold MachineState.haltBase MachineState.setDom
  by_cases hd : d' = d
  · subst hd; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd, hd]
@[simp] theorem haltBase_gates (g : GateId) : (σ.haltBase d c).gates g = σ.gates g := rfl
@[simp] theorem haltBase_mover : (σ.haltBase d c).mover = σ.mover := rfl
@[simp] theorem haltBase_inflight : (σ.haltBase d c).inflight = σ.inflight := rfl
@[simp] theorem haltBase_liveRef (r : CapRef) : (σ.haltBase d c).liveRef r = σ.liveRef r := by
  unfold MachineState.liveRef DomainState.liveCap; rw [haltBase_caps, haltBase_slotGen]

/-! ### unwindGate projections -/

variable (g : GateId) (cl : DomainId) (rd : RegId)

@[simp] theorem unwindGate_caps (d' : DomainId) :
    ((σ.unwindGate g cl rd).doms d').caps = (σ.doms d').caps := by
  unfold MachineState.unwindGate MachineState.setDom
  by_cases hd : d' = cl
  · subst hd; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd]
@[simp] theorem unwindGate_lineage (d' : DomainId) :
    ((σ.unwindGate g cl rd).doms d').lineage = (σ.doms d').lineage := by
  unfold MachineState.unwindGate MachineState.setDom
  by_cases hd : d' = cl
  · subst hd; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd]
@[simp] theorem unwindGate_slotGen (d' : DomainId) :
    ((σ.unwindGate g cl rd).doms d').slotGen = (σ.doms d').slotGen := by
  unfold MachineState.unwindGate MachineState.setDom
  by_cases hd : d' = cl
  · subst hd; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd]
@[simp] theorem unwindGate_regions (d' : DomainId) :
    ((σ.unwindGate g cl rd).doms d').regions = (σ.doms d').regions := by
  unfold MachineState.unwindGate MachineState.setDom
  by_cases hd : d' = cl
  · subst hd; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd]
@[simp] theorem unwindGate_run (d' : DomainId) :
    ((σ.unwindGate g cl rd).doms d').run = if d' = cl then .running else (σ.doms d').run := by
  unfold MachineState.unwindGate MachineState.setDom
  by_cases hd : d' = cl
  · subst hd; simp [Loom.Fun.update_same, setReg_run]
  · simp [Loom.Fun.update_ne _ _ _ _ hd, hd]
@[simp] theorem unwindGate_serving (d' : DomainId) :
    ((σ.unwindGate g cl rd).doms d').serving = (σ.doms d').serving := by
  unfold MachineState.unwindGate MachineState.setDom
  by_cases hd : d' = cl
  · subst hd; simp [Loom.Fun.update_same, setReg_serving]
  · simp [Loom.Fun.update_ne _ _ _ _ hd]
@[simp] theorem unwindGate_gates_act (g' : GateId) :
    ((σ.unwindGate g cl rd).gates g').act = if g' = g then none else (σ.gates g').act := by
  unfold MachineState.unwindGate MachineState.setDom
  by_cases hg : g' = g
  · subst hg; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hg, hg]
@[simp] theorem unwindGate_gates_config (g' : GateId) :
    ((σ.unwindGate g cl rd).gates g').config = (σ.gates g').config := by
  unfold MachineState.unwindGate MachineState.setDom
  by_cases hg : g' = g
  · subst hg; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hg]
@[simp] theorem unwindGate_mover : (σ.unwindGate g cl rd).mover = σ.mover := rfl
@[simp] theorem unwindGate_inflight : (σ.unwindGate g cl rd).inflight = σ.inflight := rfl
@[simp] theorem unwindGate_liveRef (r : CapRef) :
    (σ.unwindGate g cl rd).liveRef r = σ.liveRef r := by
  unfold MachineState.liveRef DomainState.liveCap; rw [unwindGate_caps, unwindGate_slotGen]


/-- Equation lemma: with no active served gate, `haltDom` is just `haltBase`. -/
theorem haltDom_base (hs : (σ.doms d).serving = none) :
    σ.haltDom d c = σ.haltBase d c := by simp only [MachineState.haltDom, hs]
theorem haltDom_base' (g : GateId) (hs : (σ.doms d).serving = some g)
    (ha : (σ.gates g).act = none) : σ.haltDom d c = σ.haltBase d c := by
  simp only [MachineState.haltDom, hs, ha]
/-- Equation lemma: unwinding the served gate's activation. -/
theorem haltDom_unwind (g : GateId) (a : Activation)
    (hs : (σ.doms d).serving = some g) (ha : (σ.gates g).act = some a) :
    σ.haltDom d c = (σ.haltBase d c).unwindGate g a.caller a.callerRd := by
  simp only [MachineState.haltDom, hs, ha]

end HaltDom


/-- `clearSlot` changes `caps` only at the cleared slot. -/
theorem clearSlot_caps (σ : MachineState) (d : DomainId) (s : Slot)
    (d' : DomainId) (s' : Slot) :
    ((σ.clearSlot d s).doms d').caps s' =
      if d' = d ∧ s' = s then none else (σ.doms d').caps s' := by
  unfold MachineState.clearSlot MachineState.setDom
  by_cases hd : d' = d
  · subst hd
    by_cases hs : s' = s
    · subst hs; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ hs, hs]
  · simp [Loom.Fun.update_ne _ _ _ _ hd, hd]

/-- `clearSlot` preserves the gates/mover/inflight. -/
@[simp] theorem clearSlot_gates (σ : MachineState) (d : DomainId) (s : Slot) :
    (σ.clearSlot d s).gates = σ.gates := rfl
@[simp] theorem clearSlot_mover (σ : MachineState) (d : DomainId) (s : Slot) :
    (σ.clearSlot d s).mover = σ.mover := rfl
@[simp] theorem clearSlot_inflight (σ : MachineState) (d : DomainId) (s : Slot) :
    (σ.clearSlot d s).inflight = σ.inflight := rfl
@[simp] theorem clearSlot_run (σ : MachineState) (d : DomainId) (s : Slot) (d' : DomainId) :
    ((σ.clearSlot d s).doms d').run = (σ.doms d').run := by
  unfold MachineState.clearSlot MachineState.setDom
  by_cases hd : d' = d
  · subst hd; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd]
@[simp] theorem clearSlot_serving (σ : MachineState) (d : DomainId) (s : Slot) (d' : DomainId) :
    ((σ.clearSlot d s).doms d').serving = (σ.doms d').serving := by
  unfold MachineState.clearSlot MachineState.setDom
  by_cases hd : d' = d
  · subst hd; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd]

/-- `clearSlot` preserves the live capability at any ref other than the cleared
slot (its caps and generation are untouched). -/
theorem clearSlot_liveCap_of_ne (σ : MachineState) (d : DomainId) (s : Slot)
    (dd : DomainId) (ss : Slot) (gg : Gen) (e : CapEntry)
    (hne : ¬ (dd = d ∧ ss = s)) (hlc : (σ.doms dd).liveCap ss gg = some e) :
    ((σ.clearSlot d s).doms dd).liveCap ss gg = some e := by
  unfold DomainState.liveCap at hlc ⊢
  rw [clearSlot_caps, if_neg hne, clearSlot_slotGen]
  rw [if_neg (fun hc => hne ⟨hc.1, hc.2⟩)]; exact hlc


/-! ### sweepRegions / sweepMover projections -/

@[simp] theorem sweepRegions_caps (σ : MachineState) (d : DomainId) :
    (σ.sweepRegions.doms d).caps = (σ.doms d).caps := rfl
@[simp] theorem sweepRegions_lineage (σ : MachineState) (d : DomainId) :
    (σ.sweepRegions.doms d).lineage = (σ.doms d).lineage := rfl
@[simp] theorem sweepRegions_slotGen (σ : MachineState) (d : DomainId) :
    (σ.sweepRegions.doms d).slotGen = (σ.doms d).slotGen := rfl
@[simp] theorem sweepRegions_run (σ : MachineState) (d : DomainId) :
    (σ.sweepRegions.doms d).run = (σ.doms d).run := rfl
@[simp] theorem sweepRegions_serving (σ : MachineState) (d : DomainId) :
    (σ.sweepRegions.doms d).serving = (σ.doms d).serving := rfl
@[simp] theorem sweepRegions_gates (σ : MachineState) : σ.sweepRegions.gates = σ.gates := rfl
@[simp] theorem sweepRegions_mover (σ : MachineState) : σ.sweepRegions.mover = σ.mover := rfl
@[simp] theorem sweepRegions_inflight (σ : MachineState) : σ.sweepRegions.inflight = σ.inflight := rfl

@[simp] theorem sweepMover_doms (σ : MachineState) (d : DomainId) :
    (σ.sweepMover.doms d) = σ.doms d := by
  unfold MachineState.sweepMover
  cases σ.mover with
  | none => rfl
  | some job =>
      by_cases h1 : σ.liveRef job.src && σ.liveRef job.dst
      · simp [h1]
      · simp only [h1, if_false]
        by_cases h2 : ({ σ with mover := none } : MachineState).domCovers job.owner
            job.statusAddr { r := false, w := true, x := false }
        · simp [h2, MachineState.write]
        · simp [h2]
@[simp] theorem sweepMover_gates (σ : MachineState) : σ.sweepMover.gates = σ.gates := by
  unfold MachineState.sweepMover
  cases σ.mover with
  | none => rfl
  | some job =>
      by_cases h1 : σ.liveRef job.src && σ.liveRef job.dst
      · simp [h1]
      · simp only [h1, if_false]
        by_cases h2 : ({ σ with mover := none } : MachineState).domCovers job.owner
            job.statusAddr { r := false, w := true, x := false }
        · simp [h2, MachineState.write]
        · simp [h2]
@[simp] theorem sweepMover_inflight (σ : MachineState) : σ.sweepMover.inflight = σ.inflight := by
  unfold MachineState.sweepMover
  cases σ.mover with
  | none => rfl
  | some job =>
      by_cases h1 : σ.liveRef job.src && σ.liveRef job.dst
      · simp [h1]
      · simp only [h1, if_false]
        by_cases h2 : ({ σ with mover := none } : MachineState).domCovers job.owner
            job.statusAddr { r := false, w := true, x := false }
        · simp [h2, MachineState.write]
        · simp [h2]


/-- Any bumped generation is at least 1 (bumping 0 gives 1; else it only
increases a positive value or saturates at 255). Needed for `gen_pos` after
`clearSlot` bumps a slot's generation. -/
theorem bumpGen_pos (g : Gen) : 1 ≤ (bumpGen g).toNat := by
  by_cases h : g = genRetired
  · subst h; decide
  · have := bumpGen_gt g h
    have hg := g.isLt
    omega


/-- The lineage cell freed by `clearSlot`: the removed capability's own cell. -/
def removedCell (σ : MachineState) (d : DomainId) (s : Slot) : Option LineageId :=
  ((σ.doms d).caps s).bind (·.lineage)

/-- `clearSlot` frees exactly the removed capability's lineage cell. -/
theorem clearSlot_lineage (σ : MachineState) (d : DomainId) (s : Slot)
    (d' : DomainId) (l : LineageId) :
    ((σ.clearSlot d s).doms d').lineage l =
      if d' = d ∧ removedCell σ d s = some l then none else (σ.doms d').lineage l := by
  unfold MachineState.clearSlot MachineState.setDom
  by_cases hd : d' = d
  · subst d'
    simp only [Loom.Fun.update_same, removedCell]
    cases hrc : (σ.doms d).caps s with
    | none => simp [hrc]
    | some e =>
        cases hrl : e.lineage with
        | none => simp [hrc, hrl]
        | some lr =>
            simp only [hrc, hrl, Option.bind_some, true_and]
            by_cases hll : lr = l
            · subst hll; simp [Loom.Fun.update_same]
            · rw [Loom.Fun.update_ne _ _ _ _ (fun h => hll h.symm)]
              rw [if_neg (by simp only [Option.some.injEq]; exact hll)]
  · simp [Loom.Fun.update_ne _ _ _ _ hd, hd, removedCell]


@[simp] theorem clearSlot_regions (σ : MachineState) (d : DomainId) (s : Slot) (d' : DomainId) :
    ((σ.clearSlot d s).doms d').regions = (σ.doms d').regions := by
  unfold MachineState.clearSlot MachineState.setDom
  by_cases hd : d' = d
  · subst d'; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd]


@[simp] theorem sweepRegions_liveRef (σ : MachineState) (r : CapRef) :
    σ.sweepRegions.liveRef r = σ.liveRef r := by
  unfold MachineState.liveRef DomainState.liveCap; rw [sweepRegions_caps, sweepRegions_slotGen]
@[simp] theorem sweepMover_liveRef (σ : MachineState) (r : CapRef) :
    σ.sweepMover.liveRef r = σ.liveRef r := by
  unfold MachineState.liveRef DomainState.liveCap; rw [sweepMover_doms]


/-- If the Mover survives a sweep, it was already present with live endpoints. -/
theorem sweepMover_mover_some (σ : MachineState) (job : MoverJob)
    (h : σ.sweepMover.mover = some job) :
    σ.mover = some job ∧ σ.liveRef job.src = true ∧ σ.liveRef job.dst = true := by
  unfold MachineState.sweepMover at h
  split at h
  · next hmov => rw [hmov] at h; exact absurd h (by simp)
  · next job0 hmov =>
      split at h
      · next hchk =>
          simp only [Bool.and_eq_true] at hchk
          have hjj : job0 = job := Option.some.inj (hmov ▸ h)
          subst hjj; exact ⟨hmov, hchk.1, hchk.2⟩
      · next =>
          simp only [MachineState.write] at h
          split at h <;> simp at h


/-- `orphanChildren` clears exactly the cells whose parent is `old`. -/
theorem orphanChildren_lineage (σ : MachineState) (old : CapRef) (d : DomainId)
    (l : LineageId) :
    ((σ.orphanChildren old).doms d).lineage l =
      if (match (σ.doms d).lineage l with
          | some cell => decide (cell.parent = old) | none => false)
      then none else (σ.doms d).lineage l := rfl

/-- `orphanChildren` drops the lineage index of exactly the orphaned caps;
kinds and generations are untouched. -/
theorem orphanChildren_caps (σ : MachineState) (old : CapRef) (d : DomainId) (s : Slot) :
    ((σ.orphanChildren old).doms d).caps s =
      match (σ.doms d).caps s with
      | some e => match e.lineage with
        | some l => some (if (match (σ.doms d).lineage l with
                              | some cell => decide (cell.parent = old) | none => false)
                          then { e with lineage := none } else e)
        | none => some e
      | none => none := rfl

@[simp] theorem orphanChildren_slotGen (σ : MachineState) (old : CapRef) (d : DomainId) :
    ((σ.orphanChildren old).doms d).slotGen = (σ.doms d).slotGen := rfl
@[simp] theorem orphanChildren_regions (σ : MachineState) (old : CapRef) (d : DomainId) :
    ((σ.orphanChildren old).doms d).regions = (σ.doms d).regions := rfl
@[simp] theorem orphanChildren_run (σ : MachineState) (old : CapRef) (d : DomainId) :
    ((σ.orphanChildren old).doms d).run = (σ.doms d).run := rfl
@[simp] theorem orphanChildren_serving (σ : MachineState) (old : CapRef) (d : DomainId) :
    ((σ.orphanChildren old).doms d).serving = (σ.doms d).serving := rfl
@[simp] theorem orphanChildren_gates (σ : MachineState) (old : CapRef) :
    (σ.orphanChildren old).gates = σ.gates := rfl
@[simp] theorem orphanChildren_mover (σ : MachineState) (old : CapRef) :
    (σ.orphanChildren old).mover = σ.mover := rfl
@[simp] theorem orphanChildren_inflight (σ : MachineState) (old : CapRef) :
    (σ.orphanChildren old).inflight = σ.inflight := rfl


/-- `liveCap` present-ness depends only on the slot's occupancy and generation,
not on the stored entry's contents. -/
theorem liveCap_isSome_congr (ds ds' : DomainState) (s : Slot) (g : Gen)
    (hp : (ds.caps s).isSome = (ds'.caps s).isSome) (hg : ds.slotGen s = ds'.slotGen s) :
    (ds.liveCap s g).isSome = (ds'.liveCap s g).isSome := by
  unfold DomainState.liveCap
  cases h1 : ds.caps s with
  | none => cases h2 : ds'.caps s with
            | none => rfl
            | some e2 => rw [h1, h2] at hp; simp at hp
  | some e1 => cases h2 : ds'.caps s with
               | none => rw [h1, h2] at hp; simp at hp
               | some e2 => rw [hg]; cases hc : (decide (ds'.slotGen s = g) && g != 0) <;> simp [hc]

/-- `orphanChildren` preserves each slot's occupancy. -/
theorem orphanChildren_caps_isSome (σ : MachineState) (old : CapRef) (d : DomainId) (s : Slot) :
    (((σ.orphanChildren old).doms d).caps s).isSome = (((σ.doms d).caps s).isSome) := by
  rw [orphanChildren_caps]
  cases hc : (σ.doms d).caps s with
  | none => simp [hc]
  | some e0 => cases hl : e0.lineage with
               | none => simp [hc, hl]
               | some l => simp only [hc, hl]; split <;> simp


/-! ### Descendant-marking monotonicity (`cap_revoke` support) -/

/-- `markStep` is inflationary: it only ever adds marks. -/
theorem markStep_infl (σ : MachineState) (root : CapRef) (m : DomainId → Slot → Bool)
    (d : DomainId) (s : Slot) : m d s = true → σ.markStep root m d s = true := by
  intro h; unfold MachineState.markStep; rw [h]; rfl

/-- `markStep` is monotone in the mark set. -/
theorem markStep_mono (σ : MachineState) (root : CapRef) (m m' : DomainId → Slot → Bool)
    (hle : ∀ d s, m d s = true → m' d s = true) (d : DomainId) (s : Slot) :
    σ.markStep root m d s = true → σ.markStep root m' d s = true := by
  unfold MachineState.markStep
  intro h
  rcases Bool.or_eq_true _ _ |>.mp h with h1 | h2
  · rw [hle d s h1]; rfl
  · cases hp : σ.parentOf d s with
    | none => rw [hp] at h2; simp at h2
    | some p =>
        rw [hp] at h2
        rcases Bool.or_eq_true _ _ |>.mp h2 with hr | hpm
        · simp [hr]
        · rcases Bool.and_eq_true _ _ |>.mp hpm with ⟨hg, hmm⟩
          simp [hg, hle p.dom p.slot hmm]


/-- The `k`-th marking iterate. `marks` is this at `k = numDomains * numSlots`. -/
def MachineState.iterMark (σ : MachineState) (root : CapRef) (k : Nat) : DomainId → Slot → Bool :=
  Nat.fold k (fun _ _ m => σ.markStep root m) (fun _ _ => false)

theorem iterMark_succ (σ : MachineState) (root : CapRef) (k : Nat) :
    σ.iterMark root (k + 1) = σ.markStep root (σ.iterMark root k) := by
  unfold MachineState.iterMark; rw [Nat.fold_succ]

theorem marks_eq_iter (σ : MachineState) (root : CapRef) :
    σ.marks root = σ.iterMark root (numDomains * numSlots) := by
  unfold MachineState.marks MachineState.iterMark; rfl

/-- Each iterate is contained in the next (marking only adds). -/
theorem iterMark_le_succ (σ : MachineState) (root : CapRef) (k : Nat)
    (d : DomainId) (s : Slot) :
    σ.iterMark root k d s = true → σ.iterMark root (k + 1) d s = true := by
  rw [iterMark_succ]; exact markStep_infl σ root _ d s

/-- Iterates are monotone in the step count. -/
theorem iterMark_mono (σ : MachineState) (root : CapRef) {k k' : Nat} (hk : k ≤ k')
    (d : DomainId) (s : Slot) :
    σ.iterMark root k d s = true → σ.iterMark root k' d s = true := by
  induction hk with
  | refl => exact id
  | step _ ih => intro h; exact iterMark_le_succ σ root _ d s (ih h)

/-- Once an iterate equals its successor, all later iterates agree. -/
theorem iterMark_stable (σ : MachineState) (root : CapRef) {k : Nat}
    (hfix : σ.iterMark root (k + 1) = σ.iterMark root k) (j : Nat) (hj : k ≤ j) :
    σ.iterMark root j = σ.iterMark root k := by
  induction hj with
  | refl => rfl
  | step _ ih => rw [iterMark_succ, ih, ← iterMark_succ, hfix]


/-- The count of marked slots at iterate `k`. -/
def MachineState.markCount (σ : MachineState) (root : CapRef) (k : Nat) : Nat :=
  (Finset.univ.filter (fun p : DomainId × Slot => σ.iterMark root k p.1 p.2 = true)).card

theorem markCount_mono (σ : MachineState) (root : CapRef) {k k' : Nat} (hk : k ≤ k') :
    σ.markCount root k ≤ σ.markCount root k' := by
  unfold MachineState.markCount; apply Finset.card_le_card
  intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact iterMark_mono σ root hk p.1 p.2 hp

theorem markCount_le (σ : MachineState) (root : CapRef) (k : Nat) :
    σ.markCount root k ≤ numDomains * numSlots := by
  unfold MachineState.markCount
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_univ]
  simp [Fintype.card_prod, numDomains, numSlots]

theorem markCount_zero (σ : MachineState) (root : CapRef) : σ.markCount root 0 = 0 := by
  unfold MachineState.markCount MachineState.iterMark
  simp [Nat.fold]

/-- A strict marking step strictly increases the count. -/
theorem markCount_lt_of_ne (σ : MachineState) (root : CapRef) (k : Nat)
    (hne : σ.iterMark root (k + 1) ≠ σ.iterMark root k) :
    σ.markCount root k < σ.markCount root (k + 1) := by
  unfold MachineState.markCount; apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · by_contra hc; push_neg at hc
    apply hne; funext d s
    by_cases hb : σ.iterMark root (k + 1) d s = true
    · have : (d, s) ∈ Finset.univ.filter
          (fun p : DomainId × Slot => σ.iterMark root (k + 1) p.1 p.2 = true) := by
        simp [hb]
      have hmem := hc (d, s) this
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      rw [hb, hmem]
    · simp only [Bool.not_eq_true] at hb
      have hk : σ.iterMark root k d s = false := by
        by_contra hh; simp only [Bool.not_eq_false] at hh
        have := iterMark_le_succ σ root k d s hh; rw [this] at hb; exact absurd hb (by decide)
      rw [hb, hk]
  · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact iterMark_le_succ σ root k p.1 p.2 hp

/-- If the count strictly increases at every step up to `j`, then `j ≤ count j`. -/
theorem le_markCount_of_strict (σ : MachineState) (root : CapRef) (j : Nat)
    (hstrict : ∀ k, k < j → σ.markCount root k < σ.markCount root (k + 1)) :
    j ≤ σ.markCount root j := by
  induction j with
  | zero => omega
  | succ n ih =>
      have h1 := hstrict n (by omega)
      have h2 := ih (fun k hk => hstrict k (by omega))
      omega

/-- **The marking fixpoint.** After `numDomains * numSlots` iterations, `markStep`
adds nothing: `marks` is a fixpoint. (A strict chain would exceed the slot count.) -/
theorem marks_fixpoint (σ : MachineState) (root : CapRef) :
    σ.markStep root (σ.marks root) = σ.marks root := by
  set N := numDomains * numSlots with hN
  -- some step ≤ N is already a fixpoint
  have hfix : ∃ k ≤ N, σ.iterMark root (k + 1) = σ.iterMark root k := by
    by_contra hc; push_neg at hc
    have hstrict : ∀ k, k < N + 1 → σ.markCount root k < σ.markCount root (k + 1) :=
      fun k hk => markCount_lt_of_ne σ root k (hc k (by omega))
    have := le_markCount_of_strict σ root (N + 1) hstrict
    have hle := markCount_le σ root (N + 1)
    omega
  obtain ⟨k, hkN, hkfix⟩ := hfix
  rw [marks_eq_iter, ← iterMark_succ,
    iterMark_stable σ root hkfix (N + 1) (by omega),
    iterMark_stable σ root hkfix N hkN]


/-- **Marking closure.** If a slot's parent is a live, marked capability, the
slot is marked too. The downward-closure `wf_destroyMarked`'s parent_live needs:
no surviving cell points at a destroyed (marked) capability. -/
theorem marks_closed (σ : MachineState) (root : CapRef) (d : DomainId) (s : Slot)
    (p : CapRef) (hp : σ.parentOf d s = some p)
    (hlive : (σ.doms p.dom).slotGen p.slot = p.gen)
    (hpm : σ.marks root p.dom p.slot = true) : σ.marks root d s = true := by
  have hstep : σ.markStep root (σ.marks root) d s = true := by
    unfold MachineState.markStep
    simp only [hp, ← hlive, hpm, decide_true, Bool.and_true, Bool.or_true]
  rw [marks_fixpoint σ root] at hstep; exact hstep

end Machines.Lnp64u
