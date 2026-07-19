-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics

/-!
# Action write footprints

Stable, compiler-independent syntax and frame lemmas for hardware actions.
Keeping this layer separate lets semantic developments use write footprints
without importing the model-to-µVerilog compiler or being rebuilt when release
certificate internals change.
-/

namespace Loom.Hw

/-- Names of the memories an action may write (with multiplicity). -/
def Act.memWrites : Act → List String
  | .skip => []
  | .seq a b => a.memWrites ++ b.memWrites
  | .ite _ t e => t.memWrites ++ e.memWrites
  | .write .. => []
  | .memWrite _ _ m _ _ _ => [m]

/-- `(name, width)` pairs of the registers an action may write. -/
def Act.regWrites : Act → List (String × Nat)
  | .skip => []
  | .seq a b => a.regWrites ++ b.regWrites
  | .ite _ t e => t.regWrites ++ e.regWrites
  | .write w r _ => [(r, w)]
  | .memWrite .. => []

/-- Running an action that never writes register `rn` at width `w` leaves
that entry untouched. -/
theorem Act.run_regs_notin (rn : String) (w : Nat) : ∀ (a : Act),
    (rn, w) ∉ a.regWrites →
    ∀ (σ acc : St), (a.run σ acc).regs rn w = acc.regs rn w := by
  intro a
  induction a with
  | skip => intro _ σ acc; rfl
  | seq x y ihx ihy =>
      intro h σ acc
      simp only [Act.regWrites, List.mem_append, not_or] at h
      show (y.run σ (x.run σ acc)).regs rn w = _
      rw [ihy h.2, ihx h.1]
  | ite c t e iht ihe =>
      intro h σ acc
      simp only [Act.regWrites, List.mem_append, not_or] at h
      show (if c.eval σ = 1#1 then t.run σ acc else e.run σ acc).regs rn w = _
      by_cases hc : c.eval σ = 1#1
      · rw [if_pos hc]; exact iht h.1 σ acc
      · rw [if_neg hc]; exact ihe h.2 σ acc
  | write w' r' v =>
      intro h σ acc
      have hp : ¬(r' = rn ∧ w' = w) := by
        intro ⟨h1, h2⟩
        exact h (by simp [Act.regWrites, h1, h2])
      show (acc.regs.set r' (v.eval σ)) rn w = _
      unfold RegEnv.set
      by_cases hr : rn = r'
      · rw [if_pos hr]
        have hw : w' ≠ w := fun hw => hp ⟨hr.symm, hw⟩
        rw [dif_neg hw]
      · rw [if_neg hr]
  | memWrite => intro _ σ acc; rfl

/-- Running an action that never writes memory `mn` leaves `mn`'s contents
(at every address and width) untouched. -/
theorem Act.run_mems_notin (mn : String) : ∀ (a : Act), mn ∉ a.memWrites →
    ∀ (σ acc : St) (ad w : Nat),
      (a.run σ acc).mems mn ad w = acc.mems mn ad w := by
  intro a
  induction a with
  | skip => intro _ σ acc ad w; rfl
  | seq x y ihx ihy =>
      intro h σ acc ad w
      simp only [Act.memWrites, List.mem_append, not_or] at h
      show (y.run σ (x.run σ acc)).mems mn ad w = _
      rw [ihy h.2, ihx h.1]
  | ite c t e iht ihe =>
      intro h σ acc ad w
      simp only [Act.memWrites, List.mem_append, not_or] at h
      show (if c.eval σ = 1#1 then t.run σ acc else e.run σ acc).mems mn ad w = _
      by_cases hc : c.eval σ = 1#1
      · rw [if_pos hc]; exact iht h.1 σ acc ad w
      · rw [if_neg hc]; exact ihe h.2 σ acc ad w
  | write => intro _ σ acc ad w; rfl
  | memWrite aw' dw' m' p' addr v =>
      intro h σ acc ad w
      have hm : mn ≠ m' := by
        simpa [Act.memWrites] using h
      show (acc.mems.set m' (addr.eval σ).toNat (v.eval σ)) mn ad w = _
      unfold MemEnv.set
      rw [if_neg (fun hc => hm hc.1)]

end Loom.Hw
