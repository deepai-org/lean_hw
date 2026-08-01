-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Core.Bounded
import Machines.Epoch.Protocol

/-!
# The bump-return bound (D23's first consumer)

`Machines/Epoch/Protocol.lean` (frozen) mechanizes §3's bump/ack/return
protocol and proves its safety theorems. Its acceptance criterion, however,
is a *bound*: "bump-return-to-fail-closed within the ack bound". This file
states and proves that bound with `Loom/Core/Bounded.lean`, without touching
the protocol file.

## The fairness/enabledness condition, stated explicitly

The protocol's `Ev` alphabet contains events that are **always enabled and
change nothing the bump waits on** — `use` is a pure observation (`stepEv s
(.use k r) = some s`, a self-loop), and `acquire`/`release` only move
`referent_count`. So the unrestricted system `Protocol.sys` admits runs that
never complete a bump, and `unbounded_without_fairness` below proves exactly
that: in `sys`, a bound of *any* size implies the bump had already returned.
No bound exists without a scheduling assumption. This is not a defect of the
model; it is §3's ack bound being a property of the *interconnect*, not of
the reference-checking instruction stream.

The assumption is therefore made first-class as a system: `ackSys`, whose
steps are exactly

* `ack k` for a volume `k` that **has not yet acked** (each volume acks once
  — the broadcast is not re-delivered to a volume that already answered), and
* `bumpReturn`.

Every `ackSys` step is a genuine `Protocol.Step` (`ackStep_step`), so the
bound is a bound on real protocol runs (`T_E8_return_run`); the restriction
is a *fairness/scheduling* hypothesis, discharged in the implementation by
the ack-collection engine, not a weakening of the protocol.

## The bound

With `K` referent volumes: `bumpReturn` is enabled within `K` steps
(`T_E8_acks_complete_within`) and the bump has returned within `K + 1`
(`T_E8_bumpReturn_within`) — `K` acks plus the return itself, on **all**
paths, with no deadlock on the way (`Loom.TSys.MustReach`).
-/

namespace Machines.Epoch.Bounded

open Loom Machines.Epoch.Protocol

variable {W N K : Nat}

/-! ## The ack-phase system -/

/-- Volume `k`'s state after it adopts the broadcast and acks. -/
def ackedState (s : St W N K) (b : Bump W N K) (k : Fin K) : St W N K :=
  { s with
    repl := Function.update s.repl k (Function.update (s.repl k) b.cell b.target)
    pending := some { b with acked := Function.update b.acked k true } }

theorem stepEv_ack {s : St W N K} {b : Bump W N K} (k : Fin K)
    (hb : s.pending = some b) :
    stepEv s (.ack k) = some (ackedState s b k) := by
  simp only [stepEv, hb, ackedState]

theorem stepEv_bumpReturn {s : St W N K} {b : Bump W N K}
    (hb : s.pending = some b) (hall : ∀ k, b.acked k = true) :
    stepEv s .bumpReturn = some { s with pending := none } := by
  simp only [stepEv, hb, if_pos hall]

/-- The ack-phase step relation: one *fresh* ack, or the return. This is the
fairness assumption, written down. -/
def AckStep (s s' : St W N K) : Prop :=
  (∃ (k : Fin K) (b : Bump W N K),
      s.pending = some b ∧ b.acked k = false ∧ stepEv s (.ack k) = some s') ∨
    stepEv s .bumpReturn = some s'

/-- Every ack-phase step is a protocol step: the bound below is a bound on
runs of the real protocol. -/
theorem ackStep_step {s s' : St W N K} (h : AckStep s s') : Step s s' := by
  rcases h with ⟨k, _, _, _, he⟩ | he
  · exact ⟨.ack k, he⟩
  · exact ⟨.bumpReturn, he⟩

/-- The protocol under the ack-phase schedule, as a `TSys`. Initial states
are the ones with a bump in flight — the trigger. -/
def ackSys (W N K : Nat) : Loom.TSys where
  S := St W N K
  init := fun s => s.pending ≠ none
  step := AckStep

/-! ## The measure -/

/-- The volumes that have not yet acknowledged the in-flight bump. -/
def unacked (b : Bump W N K) : Finset (Fin K) :=
  Finset.univ.filter (fun k => b.acked k = false)

theorem mem_unacked {b : Bump W N K} {k : Fin K} :
    k ∈ unacked b ↔ b.acked k = false := by
  simp [unacked]

theorem card_unacked_le (b : Bump W N K) : (unacked b).card ≤ K := by
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin K))
    (fun k => b.acked k = false)
  simpa [unacked] using h

theorem unacked_update {b : Bump W N K} {k : Fin K} (hk : b.acked k = false) :
    unacked { b with acked := Function.update b.acked k true }
      = (unacked b).erase k := by
  ext k'
  by_cases h : k' = k
  · subst h; simp [unacked, Finset.mem_erase, Function.update_apply]
  · simp [unacked, Finset.mem_erase, Function.update_apply, h]

theorem card_unacked_update {b : Bump W N K} {k : Fin K} (hk : b.acked k = false) :
    (unacked { b with acked := Function.update b.acked k true }).card + 1
      = (unacked b).card := by
  have hmem : k ∈ unacked b := mem_unacked.2 hk
  have hpos : 0 < (unacked b).card := Finset.card_pos.2 ⟨k, hmem⟩
  rw [unacked_update hk, Finset.card_erase_of_mem hmem]
  omega

/-- Steps left before the bump has returned: one per outstanding ack, plus
the return itself. -/
def remaining (s : St W N K) : Nat :=
  match s.pending with
  | none => 0
  | some b => (unacked b).card + 1

/-- Acks left before `bumpReturn` is enabled. -/
def remainingAcks (s : St W N K) : Nat :=
  match s.pending with
  | none => 0
  | some b => (unacked b).card

theorem remaining_le (s : St W N K) : remaining s ≤ K + 1 := by
  cases hp : s.pending with
  | none => have h : remaining s = 0 := by simp [remaining, hp]
            omega
  | some b =>
    have h : remaining s = (unacked b).card + 1 := by simp [remaining, hp]
    have := card_unacked_le b
    omega

theorem remainingAcks_le (s : St W N K) : remainingAcks s ≤ K := by
  cases hp : s.pending with
  | none => have h : remainingAcks s = 0 := by simp [remainingAcks, hp]
            omega
  | some b =>
    have h : remainingAcks s = (unacked b).card := by simp [remainingAcks, hp]
    have := card_unacked_le b
    omega

/-! ## The ranking argument -/

/-- The in-flight bump, if any, is settled: `bumpReturn` is enabled (or the
bump has already returned). -/
def AcksComplete (s : St W N K) : Prop :=
  ∀ b, s.pending = some b → ∀ k, b.acked k = true

/-- `AcksComplete` is exactly `bumpReturn`-enabledness. -/
theorem bumpReturn_enabled_of {s : St W N K} {b : Bump W N K}
    (hb : s.pending = some b) (h : AcksComplete s) :
    stepEv s .bumpReturn = some { s with pending := none } :=
  stepEv_bumpReturn hb (h b hb)

/-- **The ack ranking.** Under the ack-phase schedule the outstanding-ack
count strictly decreases until every volume has acked, and the system is
never stuck before then. -/
theorem acks_ranking :
    (ackSys W N K).Ranking AcksComplete (fun _ => True) remainingAcks where
  progress := by
    intro s _ hq
    have hex : ∃ (b : Bump W N K) (k : Fin K), s.pending = some b ∧ b.acked k = false := by
      by_contra hcon
      apply hq
      intro b hb k
      by_contra hk
      exact hcon ⟨b, k, hb, by simpa using hk⟩
    obtain ⟨b, k, hb, hk⟩ := hex
    exact ⟨ackedState s b k, Or.inl ⟨k, b, hb, hk, stepEv_ack k hb⟩⟩
  closed := by intro _ _ _ _ _; trivial
  decrease := by
    intro s s' _ hq hstep
    rcases hstep with ⟨k, b, hb, hk, he⟩ | he
    · rw [stepEv_ack k hb, Option.some.injEq] at he
      subst he
      have h1 : remainingAcks (ackedState s b k) =
          (unacked { b with acked := Function.update b.acked k true }).card := by
        simp [remainingAcks, ackedState]
      have h2 : remainingAcks s = (unacked b).card := by simp [remainingAcks, hb]
      have h3 := card_unacked_update (b := b) (k := k) hk
      omega
    · exfalso
      cases hb : s.pending with
      | none =>
        simp only [stepEv, hb] at he
        exact absurd he (by simp)
      | some b =>
        simp only [stepEv, hb] at he
        split at he
        · exact hq (fun b' hb' k => by
            rw [hb, Option.some.injEq] at hb'; subst hb'; rename_i hall; exact hall k)
        · exact absurd he (by simp)

/-- **The return ranking.** Under the ack-phase schedule the bump returns:
each fresh ack removes one outstanding volume, and `bumpReturn` clears the
pending slot. -/
theorem return_ranking :
    (ackSys W N K).Ranking (fun s => s.pending = none) (fun _ => True) remaining where
  progress := by
    intro s _ hq
    by_cases hall : AcksComplete s
    · cases hb : s.pending with
      | none => exact absurd hb hq
      | some b =>
        exact ⟨{ s with pending := none }, Or.inr (bumpReturn_enabled_of hb hall)⟩
    · obtain ⟨b, k, hb, hk⟩ : ∃ (b : Bump W N K) (k : Fin K),
          s.pending = some b ∧ b.acked k = false := by
        by_contra hcon
        exact hall (fun b hb k => by
          by_contra hkk
          exact hcon ⟨b, k, hb, by simpa using hkk⟩)
      exact ⟨ackedState s b k, Or.inl ⟨k, b, hb, hk, stepEv_ack k hb⟩⟩
  closed := by intro _ _ _ _ _; trivial
  decrease := by
    intro s s' _ hq hstep
    rcases hstep with ⟨k, b, hb, hk, he⟩ | he
    · rw [stepEv_ack k hb, Option.some.injEq] at he
      subst he
      have h1 : remaining (ackedState s b k) =
          (unacked { b with acked := Function.update b.acked k true }).card + 1 := by
        simp [remaining, ackedState]
      have h2 : remaining s = (unacked b).card + 1 := by simp [remaining, hb]
      have h3 := card_unacked_update (b := b) (k := k) hk
      omega
    · cases hb : s.pending with
      | none => exact absurd hb hq
      | some b =>
        simp only [stepEv, hb] at he
        split at he
        · rw [Option.some.injEq] at he
          subst he
          have h1 : remaining { s with pending := (none : Option (Bump W N K)) } = 0 := by
            simp [remaining]
          have h2 : remaining s = (unacked b).card + 1 := by simp [remaining, hb]
          omega
        · exact absurd he (by simp)

/-! ## The theorems -/

namespace Theorems

open Machines.Epoch.Bounded

/-- **T-E8a.** Under the ack-phase schedule, from *any* state and on *every*
path, every volume has acknowledged — i.e. `bumpReturn` is enabled — within
`K` steps, where `K` is the number of referent volumes. -/
theorem T_E8_acks_complete_within (s : St W N K) :
    (ackSys W N K).MustReach AcksComplete K s :=
  acks_ranking.mustReach K s trivial (remainingAcks_le s)

/-- **T-E8b.** Under the ack-phase schedule, on every path the bump has
returned (`pending = none`) within `K + 1` steps: `K` acks plus the return.
No path deadlocks first — that is the content of `MustReach`. -/
theorem T_E8_bumpReturn_within (s : St W N K) :
    (ackSys W N K).MustReach (fun t => t.pending = none) (K + 1) s :=
  return_ranking.mustReach (K + 1) s trivial (remaining_le s)

/-- The same bound as a `BoundedResponse` of the ack-phase system: the
trigger is "a bump is in flight" (§3's `pending = some b`), the response is
the return, the bound is `K + 1`. -/
theorem T_E8_bounded_response :
    (ackSys W N K).BoundedResponse (fun s => s.pending ≠ none)
      (fun s => s.pending = none) (K + 1) :=
  Loom.TSys.boundedResponse_of_ranking return_ranking
    (fun s _ _ => ⟨trivial, remaining_le s⟩)

/-! ### Back to the protocol's own `Run` -/

theorem run_of_ackStepN : ∀ (m : Nat) (s t : St W N K),
    (ackSys W N K).StepN m s t → Run s t := by
  intro m
  induction m with
  | zero => intro s t h; exact h ▸ Relation.ReflTransGen.refl
  | succ m ih =>
    intro s t h
    obtain ⟨u, hsu, hrest⟩ := h
    exact Relation.ReflTransGen.head (ackStep_step hsu) (ih u t hrest)

/-- **T-E8c.** The bound is a statement about genuine protocol runs: from
any state there is a `Protocol.Run` of at most `K + 1` steps after which the
bump has returned. (`MustReach` gives the all-paths bound; this is its
witness, expressed in the protocol's own `Run` vocabulary.) -/
theorem T_E8_return_run (s : St W N K) :
    ∃ (t : St W N K) (m : Nat), m ≤ K + 1 ∧ Run s t ∧ t.pending = none := by
  obtain ⟨t, ⟨m, hm, hpath⟩, hq⟩ := (T_E8_bumpReturn_within s).mayReach
  exact ⟨t, m, hm, run_of_ackStepN m s t hpath, hq⟩

/-! ### The fairness hypothesis is not decorative -/

/-- **The non-theorem.** In the *unrestricted* protocol a bounded return is
provable only when the bump has already returned: `use` is an always-enabled
self-loop, so some path stalls forever. Any `K` for `Protocol.sys` is
therefore vacuous — the schedule in `ackSys` is doing real work. -/
theorem unbounded_without_fairness (s : St W N K) (k : Fin K) (r : Req W)
    (n : Nat) (h : (sys W N K).MustReach (fun t => t.pending = none) n s) :
    s.pending = none :=
  h.of_selfLoop (show Step s s from ⟨.use k r, rfl⟩)

/-! ### Axiom closures -/

#print axioms T_E8_acks_complete_within
#print axioms T_E8_bumpReturn_within
#print axioms T_E8_bounded_response
#print axioms T_E8_return_run
#print axioms unbounded_without_fairness

end Theorems
end Machines.Epoch.Bounded
