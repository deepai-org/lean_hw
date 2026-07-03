import Mathlib.Order.Basic

/-!
# µLog generic core: step-indexed propositions (L1, task 3.6 seed)

Step-indexing for the Phase-3 logical relation (T2′/T4′): an `SProp` is a
`Nat`-indexed proposition, monotone downward (true at `n` stays true at
every `k ≤ n`), with the `later` modality and Löb induction. Generic — the
index will be instantiated with "cycles of execution remaining" machine-side.
-/

namespace Loom.Logic

/-- A step-indexed proposition: downward-closed in the index. -/
structure SProp where
  holds : Nat → Prop
  down : ∀ {n k}, k ≤ n → holds n → holds k

namespace SProp

/-- Entailment: pointwise implication. -/
def entails (P Q : SProp) : Prop := ∀ n, P.holds n → Q.holds n

@[inherit_doc] scoped infixr:26 " ⊢ᵢ " => SProp.entails

theorem entails_refl (P : SProp) : P ⊢ᵢ P := fun _ h => h

theorem entails_trans {P Q R : SProp} (h₁ : P ⊢ᵢ Q) (h₂ : Q ⊢ᵢ R) : P ⊢ᵢ R :=
  fun n hp => h₂ n (h₁ n hp)

/-- The always-true and always-false propositions. -/
def top : SProp := ⟨fun _ => True, fun _ _ => trivial⟩
def bot : SProp := ⟨fun _ => False, fun _ h => h⟩

/-- Conjunction and disjunction, pointwise. -/
def and (P Q : SProp) : SProp :=
  ⟨fun n => P.holds n ∧ Q.holds n,
   fun h hpq => ⟨P.down h hpq.1, Q.down h hpq.2⟩⟩

def or (P Q : SProp) : SProp :=
  ⟨fun n => P.holds n ∨ Q.holds n,
   fun h => Or.imp (P.down h) (Q.down h)⟩

/-- Step-indexed implication: must hold at every smaller index too (the
Kripke closure that keeps `imp` downward-closed). -/
def imp (P Q : SProp) : SProp :=
  ⟨fun n => ∀ k, k ≤ n → P.holds k → Q.holds k,
   fun hkn h k hk hp => h k (Nat.le_trans hk hkn) hp⟩

/-- The later modality: true one step earlier (vacuously at 0). -/
def later (P : SProp) : SProp :=
  ⟨fun n => ∀ k, k < n → P.holds k,
   fun hkn h j hj => h j (Nat.lt_of_lt_of_le hj hkn)⟩

@[inherit_doc] scoped prefix:max "▷" => SProp.later

/-- `P` entails `▷ P` (later is weaker). -/
theorem later_intro (P : SProp) : P ⊢ᵢ ▷P := by
  intro n hp
  show ∀ k, k < n → P.holds k
  exact fun k hk => P.down (Nat.le_of_lt hk) hp

/-- Later is monotone. -/
theorem later_mono {P Q : SProp} (h : P ⊢ᵢ Q) : ▷P ⊢ᵢ ▷Q := by
  intro n hp
  show ∀ k, k < n → Q.holds k
  exact fun k hk => h k (hp k hk)

/-- **Löb induction**: to prove `P` everywhere it suffices to prove `P`
under the assumption that it holds later. The engine of step-indexed
recursion — the logical relation's contractive definitions unfold with it. -/
theorem lob {P : SProp} (h : ▷P ⊢ᵢ P) : ∀ n, P.holds n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih => exact h n (fun k hk => ih k hk)

/-- Löb induction, entailment form. -/
theorem lob_entails {P : SProp} (h : ▷P ⊢ᵢ P) : top ⊢ᵢ P :=
  fun n _ => lob h n

end SProp

end Loom.Logic
