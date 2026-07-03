import Machines.Lnp64u.Step
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Tauto

/-!
# Authority, sub-authority, and resource counting (L1 definitions)

The vocabulary T2/T3/T8/T9 are stated in. Per the charter's L1 discipline,
these definitions are shared terms: the sub-authority order here is the
closure T2 quantifies over, the counting functions here are T9's conserved
quantities, and both reuse the machine's own `CapKind`/`Perms` — one set of
terms, no parallel formalization.
-/

namespace Machines.Lnp64u

open Loom

/-- Sub-authority: `k ≤ k'`. Memory: subrange with non-escalating
permissions. Gate: the same gate. This is the order the T2 closure is the
downward closure under. -/
def CapKind.le : CapKind → CapKind → Prop
  | .mem b l p, .mem b' l' p' =>
      b'.toNat ≤ b.toNat ∧ b.toNat + l.toNat ≤ b'.toNat + l'.toNat ∧ p.le p' = true
  | .gate g, .gate g' => g = g'
  | _, _ => False

instance : ∀ k k' : CapKind, Decidable (k.le k')
  | .mem _ _ _, .mem _ _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .mem _ _ _, .gate _ => inferInstanceAs (Decidable False)
  | .gate _, .mem _ _ _ => inferInstanceAs (Decidable False)
  | .gate _, .gate _ => inferInstanceAs (Decidable (_ = _))

theorem CapKind.le_refl (k : CapKind) : k.le k := by
  cases k with
  | mem b l p => exact ⟨Nat.le_refl _, Nat.le_refl _, by cases p; simp [Perms.le]⟩
  | gate g => rfl

private theorem bimp_trans {a b c : Bool}
    (h₁ : a = false ∨ b = true) (h₂ : b = false ∨ c = true) :
    a = false ∨ c = true := by
  rcases h₁ with h | h
  · exact .inl h
  · rcases h₂ with h' | h'
    · rw [h] at h'; cases h'
    · exact .inr h'

theorem Perms.le_trans {p q r : Perms} (h₁ : p.le q = true) (h₂ : q.le r = true) :
    p.le r = true := by
  cases p; cases q; cases r
  simp only [Perms.le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at *
  exact ⟨⟨bimp_trans h₁.1.1 h₂.1.1, bimp_trans h₁.1.2 h₂.1.2⟩,
         bimp_trans h₁.2 h₂.2⟩

theorem CapKind.le_trans {k₁ k₂ k₃ : CapKind} (h₁ : k₁.le k₂) (h₂ : k₂.le k₃) :
    k₁.le k₃ := by
  cases k₁ <;> cases k₂ <;> cases k₃ <;> simp_all [CapKind.le]
  · exact ⟨by omega, by omega, Perms.le_trans h₁.2.2 h₂.2.2⟩

/-- `Perms.le` is antisymmetric: mutual containment forces equality. `Perms`
is finite, so this is decidable. -/
theorem Perms.le_antisymm {p q : Perms} (h₁ : p.le q = true) (h₂ : q.le p = true) :
    p = q := by
  obtain ⟨r, w, x⟩ := p; obtain ⟨r', w', x'⟩ := q
  revert h₁ h₂
  cases r <;> cases w <;> cases x <;> cases r' <;> cases w' <;> cases x' <;> decide

/-- `CapKind.le` is antisymmetric — the authority order is a genuine partial
order, so the T2 authority closure has no cycles that could smuggle in extra
authority. -/
theorem CapKind.le_antisymm {k₁ k₂ : CapKind} (h₁ : k₁.le k₂) (h₂ : k₂.le k₁) :
    k₁ = k₂ := by
  cases k₁ <;> cases k₂ <;> simp_all [CapKind.le]
  · obtain ⟨hb1, hl1, hp1⟩ := h₁; obtain ⟨hb2, hl2, hp2⟩ := h₂
    refine ⟨?_, ?_, Perms.le_antisymm hp1 hp2⟩
    · apply BitVec.eq_of_toNat_eq; omega
    · apply BitVec.eq_of_toNat_eq; omega

/-- A root authority: some manifest initial capability dominates `k`. The
right-hand side of T2 — the closure of the manifest under the five
operations never escapes the downward closure of the roots. -/
def IsRootAuth (m : Manifest) (k : CapKind) : Prop :=
  ∃ (d : DomainId) (s : Slot) (k₀ : CapKind),
    (m.doms d).initCaps s = some k₀ ∧ k.le k₀

/-- T2's per-state property: every live capability anywhere is within the
downward closure of the manifest roots. -/
def AuthorityConfined (m : Manifest) (σ : MachineState) : Prop :=
  ∀ (d : DomainId) (s : Slot) (e : CapEntry),
    (σ.doms d).caps s = some e → IsRootAuth m e.kind

/-! ## T9 resource counting -/

/-- Occupied lineage cells of one domain. -/
def cellCount (ds : DomainState) : Nat :=
  (Finset.univ.filter fun l : LineageId => (ds.lineage l).isSome).card

/-- Occupied capability slots of one domain. -/
def slotCount (ds : DomainState) : Nat :=
  (Finset.univ.filter fun s : Slot => (ds.caps s).isSome).card

/-- Derived (non-root) capabilities of one domain — the entries that must
each own exactly one lineage cell. -/
def derivedCount (ds : DomainState) : Nat :=
  (Finset.univ.filter fun s : Slot => ((ds.caps s).bind CapEntry.lineage).isSome).card

/-! ## Access predicates (T3/T8 vocabulary) -/

/-- Some agent writes word `a` during `step m σ` under authority descending
from reference `r`: the core through a region backed by `r`, or the Mover
through a destination capability `r`. The T3/T8 statements quantify over
this. -/
def WritesUnder (σ : MachineState) (r : CapRef) (a : Addr) : Prop :=
  -- Mover channel: the active job's destination is r and this cycle's word is a
  (∃ job, σ.mover = some job ∧ job.dst = r ∧ job.dstCur = a ∧ job.remaining ≠ 0) ∨
  -- Core channel: a store retiring this cycle whose authorizing region is backed by r
  (∃ fl rg reg, σ.inflight = some fl ∧ fl.cyclesLeft ≤ 1 ∧
     (σ.doms fl.dom).regions reg = some rg ∧ rg.backing = r ∧
     rg.covers a { r := false, w := true, x := false } = true)

end Machines.Lnp64u
