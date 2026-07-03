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

/-- `haltDom` preserves every domain's caps/lineage/slotGen/regions. -/
private theorem haltDom_dom_proj (d' : DomainId) :
    ((σ.haltDom d c).doms d').caps = (σ.doms d').caps ∧
    ((σ.haltDom d c).doms d').lineage = (σ.doms d').lineage ∧
    ((σ.haltDom d c).doms d').slotGen = (σ.doms d').slotGen ∧
    ((σ.haltDom d c).doms d').regions = (σ.doms d').regions := by
  unfold MachineState.haltDom MachineState.setDom
  split
  · next =>
      by_cases hd : d' = d
      · subst hd; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hd]
  · next g _ =>
      split
      · next =>
          by_cases hd : d' = d
          · subst hd; simp [Loom.Fun.update_same]
          · simp [Loom.Fun.update_ne _ _ _ _ hd]
      · next a _ =>
          by_cases hcl : d' = a.caller
          · subst hcl
            simp only [Loom.Fun.update_same, setReg_caps, setReg_lineage,
              setReg_slotGen, setReg_regions]
            by_cases hd : a.caller = d
            · rw [hd]; simp [Loom.Fun.update_same]
            · simp [Loom.Fun.update_ne _ _ _ _ hd]
          · simp only [Loom.Fun.update_ne _ _ _ _ hcl]
            by_cases hd : d' = d
            · subst hd; simp [Loom.Fun.update_same]
            · simp [Loom.Fun.update_ne _ _ _ _ hd]

@[simp] theorem haltDom_caps (d' : DomainId) :
    ((σ.haltDom d c).doms d').caps = (σ.doms d').caps := (haltDom_dom_proj σ d c d').1
@[simp] theorem haltDom_lineage (d' : DomainId) :
    ((σ.haltDom d c).doms d').lineage = (σ.doms d').lineage := (haltDom_dom_proj σ d c d').2.1
@[simp] theorem haltDom_slotGen (d' : DomainId) :
    ((σ.haltDom d c).doms d').slotGen = (σ.doms d').slotGen := (haltDom_dom_proj σ d c d').2.2.1
@[simp] theorem haltDom_regions (d' : DomainId) :
    ((σ.haltDom d c).doms d').regions = (σ.doms d').regions := (haltDom_dom_proj σ d c d').2.2.2

@[simp] theorem haltDom_mover : (σ.haltDom d c).mover = σ.mover := by
  unfold MachineState.haltDom; split
  · rfl
  · split
    · rfl
    · rfl

@[simp] theorem haltDom_inflight : (σ.haltDom d c).inflight = σ.inflight := by
  unfold MachineState.haltDom; split
  · rfl
  · split
    · rfl
    · rfl

@[simp] theorem haltDom_liveRef (r : CapRef) : (σ.haltDom d c).liveRef r = σ.liveRef r := by
  unfold MachineState.liveRef DomainState.liveCap; rw [haltDom_caps, haltDom_slotGen]

@[simp] theorem haltDom_gates_config (g : GateId) :
    ((σ.haltDom d c).gates g).config = (σ.gates g).config := by
  unfold MachineState.haltDom; split
  · rfl
  · rename_i g' _
    split
    · rfl
    · by_cases hg : g = g'
      · subst hg; simp [MachineState.setDom, Loom.Fun.update_same]
      · simp [MachineState.setDom, Loom.Fun.update_ne _ _ _ _ hg]

end HaltDom

end Machines.Lnp64u
