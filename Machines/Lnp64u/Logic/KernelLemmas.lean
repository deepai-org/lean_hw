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

end Machines.Lnp64u
