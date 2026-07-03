import Machines.Lnp64u.Kernel

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

end Machines.Lnp64u
