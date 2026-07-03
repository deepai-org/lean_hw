import Mathlib.Order.Lattice

/-!
# µLog generic core: resource algebras and BI propositions (L1, task 3.6 seed)

The machine-generic half of µLog. A **resource algebra** is a partial
commutative monoid of resources (ownership fragments); a **BI proposition**
is a predicate on resources; separating conjunction `∗` splits a resource
between two claims, and the magic wand `-∗` is its right adjoint. Everything
that mentions LNP64-µ's concrete resources (memory ranges, capability slots,
lineage cells, budget time) lives machine-side in
`Machines/Lnp64u/Logic/Sep/Resource.lean` — one set of terms, no parallel
formalization (charter L1 discipline).

Design: partiality via a `Prop`-valued disjointness relation plus a total
join defined on disjoint pairs (the standard PCM presentation that avoids
`Option`-valued composition in every lemma). Laws are exactly the commutative
partial-monoid axioms; the BI layer proves the (affine) BI algebra laws:
`∗` commutative/associative with unit `emp`, monotone, and adjoint to `-∗`.
-/

namespace Loom.Logic

universe u

/-- A partial commutative monoid of resources: the carrier of ownership. -/
structure Pcm (α : Type u) where
  /-- Disjointness: `a ⊥ b` when both fragments can be held together. -/
  disj : α → α → Prop
  /-- Join of two disjoint fragments. -/
  op : α → α → α
  /-- The empty resource. -/
  unit : α
  disj_comm : ∀ {a b}, disj a b → disj b a
  op_comm : ∀ {a b}, disj a b → op a b = op b a
  unit_disj : ∀ a, disj unit a
  unit_op : ∀ a, op unit a = a
  /-- Associativity package (left-to-right). -/
  disj_assoc : ∀ {a b c}, disj a b → disj (op a b) c → disj b c
  disj_assoc' : ∀ {a b c}, disj a b → disj (op a b) c → disj a (op b c)
  op_assoc : ∀ {a b c}, disj a b → disj (op a b) c →
    op (op a b) c = op a (op b c)

namespace Pcm

variable {α : Type u} (M : Pcm α)

/-- A BI proposition: a predicate on resources. (Affine presentation: no
persistence modality yet — added when the logical relation needs it.) -/
def Prp (_M : Pcm α) := α → Prop

variable {M}

/-- Entailment. -/
def Prp.entails (P Q : Prp M) : Prop := ∀ a, P a → Q a

@[inherit_doc] scoped infixr:26 " ⊢ₛ " => Prp.entails

/-- The empty-resource assertion. -/
def Prp.emp : Prp M := fun a => a = M.unit

/-- Separating conjunction: the resource splits into disjoint parts
satisfying each conjunct. -/
def Prp.sep (P Q : Prp M) : Prp M :=
  fun c => ∃ a b, M.disj a b ∧ c = M.op a b ∧ P a ∧ Q b

@[inherit_doc] scoped infixr:35 " ∗ " => Prp.sep

/-- Magic wand: whatever disjoint resource satisfying `P` is joined in,
the combination satisfies `Q`. -/
def Prp.wand (P Q : Prp M) : Prp M :=
  fun a => ∀ b, M.disj a b → P b → Q (M.op a b)

@[inherit_doc] scoped infixr:30 " -∗ " => Prp.wand

/-- Pure (resource-free) assertion. -/
def Prp.pure (φ : Prop) : Prp M := fun _ => φ

theorem entails_refl (P : Prp M) : P ⊢ₛ P := fun _ h => h

theorem entails_trans {P Q R : Prp M} (h₁ : P ⊢ₛ Q) (h₂ : Q ⊢ₛ R) : P ⊢ₛ R :=
  fun a hp => h₂ a (h₁ a hp)

/-- `∗` is commutative. -/
theorem sep_comm (P Q : Prp M) : (P ∗ Q) ⊢ₛ (Q ∗ P) := by
  rintro c ⟨a, b, hd, rfl, hp, hq⟩
  exact ⟨b, a, M.disj_comm hd, (M.op_comm hd).symm ▸ rfl, hq, hp⟩

/-- `emp` is a left unit. -/
theorem emp_sep (P : Prp M) : (Prp.emp ∗ P) ⊢ₛ P := by
  rintro c ⟨a, b, _, rfl, rfl, hp⟩
  rw [M.unit_op]; exact hp

/-- `emp` introduces on the left. -/
theorem sep_emp_intro (P : Prp M) : P ⊢ₛ (Prp.emp ∗ P) := by
  intro a hp
  exact ⟨M.unit, a, M.unit_disj a, (M.unit_op a).symm ▸ rfl, rfl, hp⟩

/-- `∗` is associative (left-to-right). -/
theorem sep_assoc (P Q R : Prp M) : ((P ∗ Q) ∗ R) ⊢ₛ (P ∗ (Q ∗ R)) := by
  rintro c ⟨ab, r, hd₂, rfl, ⟨a, b, hd₁, rfl, hp, hq⟩, hr⟩
  refine ⟨a, M.op b r, M.disj_assoc' hd₁ hd₂, M.op_assoc hd₁ hd₂, hp,
          b, r, M.disj_assoc hd₁ hd₂, rfl, hq, hr⟩

/-- `∗` is monotone. -/
theorem sep_mono {P P' Q Q' : Prp M} (h₁ : P ⊢ₛ P') (h₂ : Q ⊢ₛ Q') :
    (P ∗ Q) ⊢ₛ (P' ∗ Q') := by
  rintro c ⟨a, b, hd, rfl, hp, hq⟩
  exact ⟨a, b, hd, rfl, h₁ a hp, h₂ b hq⟩

/-- Wand introduction (currying): the adjunction, one direction. -/
theorem wand_intro {P Q R : Prp M} (h : (P ∗ Q) ⊢ₛ R) : P ⊢ₛ (Q -∗ R) := by
  intro a hp b hd hq
  exact h _ ⟨a, b, hd, rfl, hp, hq⟩

/-- Wand elimination (modus ponens): the adjunction, other direction. -/
theorem wand_elim {P Q R : Prp M} (h : P ⊢ₛ (Q -∗ R)) : (P ∗ Q) ⊢ₛ R := by
  rintro c ⟨a, b, hd, rfl, hp, hq⟩
  exact h a hp b hd hq

/-- The pure fact carried by a `pure φ` conjunct extracts. -/
theorem sep_pure_extract {φ : Prop} {P : Prp M} :
    (Prp.pure φ ∗ P) ⊢ₛ Prp.pure φ := by
  rintro c ⟨_, _, _, rfl, hφ, _⟩
  exact hφ

end Pcm

end Loom.Logic
