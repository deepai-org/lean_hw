-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Core.Ts

/-!
# Bounded response over `TSys` runs (D23)

`Loom/Core/Ts.lean` gives safety (`Invariant`) and nothing temporal. Every
real-time claim the LNP64 ISA prices — §3's acknowledgement bound, Law 5's
bounded instruction, all of Appendix C — has the same shape: *from a trigger,
the response happens within `K` steps*. That is bounded response, and this
file is its theory: the property forms, the ranking rule that discharges
them, and transport across `Simulation` / `StutterSimulation`.

## The quantifier structure, and why

`TSys.step` is a *relation*, so "within `K` steps" has two readings.

* **May** (`MayReach`, CTL `EF≤K`): *some* run of length `≤ K` reaches `Q`.
  Too weak to be a guarantee — it is the reachability form, kept because it
  is the useful lemma (it produces an actual witnessing run) and because the
  `Must` forms imply it.
* **Must** (`MustReach`, CTL `AF≤K` with a progress requirement): *every*
  run passes through `Q` within `K` steps. This is what "bump-return within
  the ack bound" means, and it is what we prove.

The `Must` form is defined inductively (`now` / `later`) rather than by
quantifying over path functions, because the inductive form is what the
ranking rule produces and what refinement transports; `MustReachOrBlock.
on_path` recovers the explicit "every path of length `n` from `s` contains a
`Q`-state" reading, so the definition is pinned to its intended meaning.

## Enabledness, handled explicitly

A relation may **block**: a state with no successor. Then "every run reaches
`Q` within `K`" is vacuously true at a deadlocked non-`Q` state, which is not
what a hardware bound should mean (a stuck engine is not a fast engine). So
there are two `Must` forms and the difference is stated, never silent:

* `MustReachOrBlock` — deadlock-tolerant `AF≤K`. Weaker, but it is the form
  that transports down a refinement *without side conditions*, because a
  forward simulation says nothing about concrete enabledness.
* `MustReach` — carries an `enabled` witness at every non-`Q` state on the
  way. This is the real bound: `Q` within `K` steps *and* no deadlock before
  it. Every transport theorem that produces this form takes the concrete
  enabledness hypothesis as an explicit argument.

## What this is not

Bounded response is not liveness. There is no fairness theory here and no
unbounded eventuality: a system that only responds "eventually" has no `K`
and nothing in this file applies to it. That is deliberate — a bound is the
hardware-honest substitute (it is WCET-shaped), and an obligation that cannot
name its `K` is not an obligation this stack accepts.
-/

namespace Loom
namespace TSys

/-! ## Finite runs -/

/-- Exactly-`n`-step reachability along the step relation. -/
def StepN (M : TSys) : Nat → M.S → M.S → Prop
  | 0, s, t => s = t
  | n + 1, s, t => ∃ u, M.step s u ∧ M.StepN n u t

/-- At-most-`n`-step reachability. -/
def StepLe (M : TSys) (n : Nat) (s t : M.S) : Prop :=
  ∃ m, m ≤ n ∧ M.StepN m s t

theorem StepN.zero {M : TSys} (s : M.S) : M.StepN 0 s s := rfl

theorem StepN.head {M : TSys} {n : Nat} {s u t : M.S}
    (h : M.step s u) (hrest : M.StepN n u t) : M.StepN (n + 1) s t :=
  ⟨u, h, hrest⟩

theorem StepLe.refl {M : TSys} {n : Nat} (s : M.S) : M.StepLe n s s :=
  ⟨0, Nat.zero_le _, rfl⟩

/-- Every finite run lands in a reachable state when it starts in one. -/
theorem reachable_of_stepN {M : TSys} : ∀ (n : Nat) (s t : M.S),
    M.Reachable s → M.StepN n s t → M.Reachable t := by
  intro n
  induction n with
  | zero => intro s t hr h; exact h ▸ hr
  | succ n ih =>
    intro s t hr h
    obtain ⟨u, hsu, hrest⟩ := h
    exact ih u t (.step hr hsu) hrest

/-- A path of length `n`: `σ 0, σ 1, …, σ n` with consecutive steps. -/
def IsPath (M : TSys) (σ : Nat → M.S) (n : Nat) : Prop :=
  ∀ i, i < n → M.step (σ i) (σ (i + 1))

/-! ## The property forms -/

/-- `Q` is reachable within `n` steps along *some* run (CTL `EF≤n`). -/
def MayReach (M : TSys) (Q : M.S → Prop) (n : Nat) (s : M.S) : Prop :=
  ∃ t, M.StepLe n s t ∧ Q t

/-- **Deadlock-tolerant bounded response** (CTL `AF≤n`, blocking allowed):
every run out of `s` either reaches a `Q`-state within `n` steps or blocks
first. The form that transports across a forward simulation with no side
condition — a simulation constrains the concrete system's steps, not its
ability to take one. -/
inductive MustReachOrBlock (M : TSys) (Q : M.S → Prop) : Nat → M.S → Prop where
  /-- The response has happened. Available at any remaining budget. -/
  | now {n : Nat} {s : M.S} (hq : Q s) : MustReachOrBlock M Q n s
  /-- Every successor responds within one less step. -/
  | later {n : Nat} {s : M.S}
      (next : ∀ t, M.step s t → MustReachOrBlock M Q n t) :
      MustReachOrBlock M Q (n + 1) s

/-- **Bounded response** (CTL `AF≤n` *plus* progress): every run out of `s`
reaches a `Q`-state within `n` steps, and the system never blocks before it
does. The `enabled` field is the explicit no-deadlock side condition: a
stuck non-`Q` state refutes the bound instead of vacuously satisfying it. -/
inductive MustReach (M : TSys) (Q : M.S → Prop) : Nat → M.S → Prop where
  /-- The response has happened. -/
  | now {n : Nat} {s : M.S} (hq : Q s) : MustReach M Q n s
  /-- The system can step, and every successor responds within one less. -/
  | later {n : Nat} {s : M.S} (enabled : ∃ t, M.step s t)
      (next : ∀ t, M.step s t → MustReach M Q n t) :
      MustReach M Q (n + 1) s

namespace MustReach

variable {M : TSys} {Q : M.S → Prop}

/-- Budgets weaken upward. -/
theorem mono {n m : Nat} {s : M.S} (h : M.MustReach Q n s) (hnm : n ≤ m) :
    M.MustReach Q m s := by
  induction h generalizing m with
  | now hq => exact .now hq
  | later en _ ih =>
    cases m with
    | zero => exact absurd hnm (by omega)
    | succ m' => exact .later en (fun t ht => ih t ht (by omega))

/-- Weakening the response predicate. -/
theorem imp {n : Nat} {s : M.S} {Q' : M.S → Prop} (h : M.MustReach Q n s)
    (hQ : ∀ u, Q u → Q' u) : M.MustReach Q' n s := by
  induction h with
  | now hq => exact .now (hQ _ hq)
  | later en _ ih => exact .later en (fun t ht => ih t ht)

/-- The no-deadlock content, isolated: before the response, the system can
always step. -/
theorem progress {n : Nat} {s : M.S} (h : M.MustReach Q n s) (hq : ¬ Q s) :
    ∃ t, M.step s t := by
  cases h with
  | now hq' => exact absurd hq' hq
  | later en _ => exact en

/-- Forget the progress requirement. -/
theorem toOrBlock {n : Nat} {s : M.S} (h : M.MustReach Q n s) :
    M.MustReachOrBlock Q n s := by
  induction h with
  | now hq => exact .now hq
  | later _ _ ih => exact .later (fun t ht => ih t ht)

/-- A bound produces an actual witnessing run: `Must` implies `May`. This is
where the `enabled` field pays — without it there need be no run at all. -/
theorem mayReach {n : Nat} {s : M.S} (h : M.MustReach Q n s) :
    M.MayReach Q n s := by
  induction h with
  | now hq => exact ⟨_, StepLe.refl _, hq⟩
  | later en _ ih =>
    obtain ⟨t, ht⟩ := en
    obtain ⟨u, ⟨m, hm, hpath⟩, hq⟩ := ih t ht
    exact ⟨u, ⟨m + 1, Nat.succ_le_succ hm, StepN.head ht hpath⟩, hq⟩

/-- A self-loop kills every bound: if `s` can step to itself, the only way
`Q` can be guaranteed within any budget is for it to hold already. The
formal reason a bound needs a scheduling/fairness restriction whenever the
model has always-enabled stutter events. -/
theorem of_selfLoop {n : Nat} {s : M.S} (h : M.MustReach Q n s) :
    M.step s s → Q s := by
  induction h with
  | now hq => exact fun _ => hq
  | later _ _ ih => exact fun hloop => ih _ hloop hloop

end MustReach

namespace MustReachOrBlock

variable {M : TSys} {Q : M.S → Prop}

theorem mono {n m : Nat} {s : M.S} (h : M.MustReachOrBlock Q n s) (hnm : n ≤ m) :
    M.MustReachOrBlock Q m s := by
  induction h generalizing m with
  | now hq => exact .now hq
  | later _ ih =>
    cases m with
    | zero => exact absurd hnm (by omega)
    | succ m' => exact .later (fun t ht => ih t ht (by omega))

/-- **The all-paths reading, made explicit.** Along any concrete path of
length `n` out of `s`, some position `j ≤ n` satisfies `Q`. This pins the
inductive definition to its intended meaning: not "some run reaches `Q`",
but "every run does". -/
theorem on_path (M : TSys) (Q : M.S → Prop) :
    ∀ (n : Nat) (σ : Nat → M.S), M.IsPath σ n →
      M.MustReachOrBlock Q n (σ 0) → ∃ j, j ≤ n ∧ Q (σ j) := by
  intro n
  induction n with
  | zero =>
    intro σ _ h
    cases h with
    | now hq => exact ⟨0, Nat.le_refl 0, hq⟩
  | succ n ih =>
    intro σ hp h
    cases h with
    | now hq => exact ⟨0, Nat.zero_le _, hq⟩
    | later next =>
      obtain ⟨j, hj, hq⟩ :=
        ih (fun i => σ (i + 1)) (fun i hi => hp (i + 1) (Nat.succ_lt_succ hi))
          (next _ (hp 0 (Nat.succ_pos n)))
      exact ⟨j + 1, Nat.succ_le_succ hj, hq⟩

end MustReachOrBlock

/-- The all-paths reading for the progress-carrying form. -/
theorem MustReach.on_path {M : TSys} {Q : M.S → Prop} (n : Nat) (σ : Nat → M.S)
    (hp : M.IsPath σ n) (h : M.MustReach Q n (σ 0)) : ∃ j, j ≤ n ∧ Q (σ j) :=
  MustReachOrBlock.on_path M Q n σ hp h.toOrBlock

/-! ## The response properties over a system -/

/-- **Bounded response**: from every reachable trigger state, `Q` within `K`
steps on all paths, with no deadlock before it. -/
def BoundedResponse (M : TSys) (P Q : M.S → Prop) (K : Nat) : Prop :=
  ∀ s, M.Reachable s → P s → M.MustReach Q K s

/-- The deadlock-tolerant variant. -/
def BoundedResponseOrBlock (M : TSys) (P Q : M.S → Prop) (K : Nat) : Prop :=
  ∀ s, M.Reachable s → P s → M.MustReachOrBlock Q K s

theorem BoundedResponse.toOrBlock {M : TSys} {P Q : M.S → Prop} {K : Nat}
    (h : M.BoundedResponse P Q K) : M.BoundedResponseOrBlock P Q K :=
  fun s hr hp => (h s hr hp).toOrBlock

theorem BoundedResponse.mono {M : TSys} {P Q : M.S → Prop} {K K' : Nat}
    (h : M.BoundedResponse P Q K) (hK : K ≤ K') : M.BoundedResponse P Q K' :=
  fun s hr hp => (h s hr hp).mono hK

/-! ## The workhorse: ranking functions

A measure that strictly decreases on every step until the response fires
gives the bound. `Dom` is the domain of the argument — in practice an
invariant, or `Reachable`, or `fun _ => True`; it is closed forward only
along the steps the rule actually uses (those out of non-`Q` states), which
is the weakest closure condition that works. -/

/-- A ranking (variant) argument for `Q` on the region `Dom`. -/
structure Ranking (M : TSys) (Q : M.S → Prop) (Dom : M.S → Prop)
    (μ : M.S → Nat) : Prop where
  /-- Off the response, the system can always step: the explicit
  no-deadlock obligation. -/
  progress : ∀ s, Dom s → ¬ Q s → ∃ t, M.step s t
  /-- The region is closed under the steps the argument traverses. -/
  closed : ∀ s t, Dom s → ¬ Q s → M.step s t → Dom t
  /-- Every step off the response strictly decreases the measure. -/
  decrease : ∀ s t, Dom s → ¬ Q s → M.step s t → μ t < μ s

namespace Ranking

variable {M : TSys} {Q Dom : M.S → Prop} {μ : M.S → Nat}

/-- **The induction principle.** A ranking bounded by `n` at the current
state yields the `n`-step response. -/
theorem mustReach (h : M.Ranking Q Dom μ) :
    ∀ (n : Nat) (s : M.S), Dom s → μ s ≤ n → M.MustReach Q n s := by
  intro n
  induction n with
  | zero =>
    intro s hd hμ
    by_cases hq : Q s
    · exact .now hq
    · obtain ⟨t, ht⟩ := h.progress s hd hq
      exact absurd (h.decrease s t hd hq ht) (by omega)
  | succ n ih =>
    intro s hd hμ
    by_cases hq : Q s
    · exact .now hq
    · exact .later (h.progress s hd hq) (fun t ht =>
        ih t (h.closed s t hd hq ht)
          (by have := h.decrease s t hd hq ht; omega))

/-- The measure *is* the bound: at any `Dom` state the response happens
within `μ s` steps. -/
theorem mustReach_measure (h : M.Ranking Q Dom μ) (s : M.S) (hd : Dom s) :
    M.MustReach Q (μ s) s :=
  h.mustReach (μ s) s hd (Nat.le_refl _)

end Ranking

/-- **The ergonomic entry point**: a ranking plus a trigger bound gives a
bounded-response property of the system. -/
theorem boundedResponse_of_ranking {M : TSys} {P Q Dom : M.S → Prop}
    {μ : M.S → Nat} {K : Nat} (h : M.Ranking Q Dom μ)
    (trigger : ∀ s, M.Reachable s → P s → Dom s ∧ μ s ≤ K) :
    M.BoundedResponse P Q K := by
  intro s hr hp
  obtain ⟨hd, hμ⟩ := trigger s hr hp
  exact h.mustReach K s hd hμ

end TSys

/-! ## Transport across refinement

A bound proved of the abstract protocol is only worth proving if it reaches
the implementation. Forward simulation carries the *deadlock-tolerant* form
for free (concrete steps map to abstract steps, so every concrete path is an
abstract path); recovering the progress-carrying form needs a concrete
enabledness hypothesis, which every theorem below takes explicitly. -/

namespace Simulation

open TSys

/-- Deadlock-tolerant bounded response pulls back with no side conditions. -/
theorem mustReachOrBlock_pullback {A C : TSys} (σ : Simulation A C)
    {Q : A.S → Prop} : ∀ (n : Nat) (s : C.S),
      A.MustReachOrBlock Q n (σ.abs s) →
      C.MustReachOrBlock (fun c => Q (σ.abs c)) n s := by
  intro n
  induction n with
  | zero =>
    intro s h
    cases h with
    | now hq => exact .now hq
  | succ n ih =>
    intro s h
    cases h with
    | now hq => exact .now hq
    | later next =>
      exact .later (fun t ht => ih t (next _ (σ.square s t ht)))

/-- The progress-carrying form pulls back given concrete enabledness on a
forward-closed region `Dom`. The hypothesis is exactly what a forward
simulation cannot supply: that the implementation is not stuck. -/
theorem mustReach_pullback {A C : TSys} (σ : Simulation A C)
    {Q : A.S → Prop} {Dom : C.S → Prop}
    (closed : ∀ s t, Dom s → C.step s t → Dom t)
    (enabled : ∀ s, Dom s → ¬ Q (σ.abs s) → ∃ t, C.step s t) :
    ∀ (n : Nat) (s : C.S), Dom s → A.MustReachOrBlock Q n (σ.abs s) →
      C.MustReach (fun c => Q (σ.abs c)) n s := by
  intro n
  induction n with
  | zero =>
    intro s _ h
    cases h with
    | now hq => exact .now hq
  | succ n ih =>
    intro s hd h
    by_cases hq : Q (σ.abs s)
    · exact .now hq
    cases h with
    | now hq' => exact absurd hq' hq
    | later next =>
      exact .later (enabled s hd hq)
        (fun t ht => ih t (closed s t hd ht) (next _ (σ.square s t ht)))

/-- Bounded response transports down a simulation at the **same bound**,
given implementation enabledness on reachable states. -/
theorem boundedResponse_pullback {A C : TSys} (σ : Simulation A C)
    {P Q : A.S → Prop} {K : Nat}
    (enabled : ∀ s, C.Reachable s → ¬ Q (σ.abs s) → ∃ t, C.step s t)
    (h : A.BoundedResponse P Q K) :
    C.BoundedResponse (fun c => P (σ.abs c)) (fun c => Q (σ.abs c)) K := by
  intro s hr hp
  exact mustReach_pullback σ (fun _ t _ hst => .step ‹C.Reachable _› hst) enabled
    K s hr (h _ (σ.reachable s hr) hp).toOrBlock

end Simulation

namespace StutterSimulation

open TSys

/-- **Bounded response across stuttering refinement.** If the implementation
takes at most `b` stutter steps in a row — witnessed by a `rank` bounded by
`b` that strictly decreases on every stuttering step — then an abstract
`n`-step bound becomes a concrete `n * (b+1) + rank s` bound.

The measure is `n * (b+1) + rank`: a real step spends one abstract unit and
resets the rank to at most `b` (net decrease, since `(b+1)` is paid and at
most `b` returned); a stutter step spends rank alone. -/
theorem mustReach_pullback {A C : TSys} (σ : StutterSimulation A C)
    {Q : A.S → Prop} {Dom : C.S → Prop} {rank : C.S → Nat} {b : Nat}
    (closed : ∀ s t, Dom s → C.step s t → Dom t)
    (rank_le : ∀ s, Dom s → rank s ≤ b)
    (stutter : ∀ s t, Dom s → C.step s t → σ.abs t = σ.abs s → rank t < rank s)
    (enabled : ∀ s, Dom s → ¬ Q (σ.abs s) → ∃ t, C.step s t)
    {n : Nat} {s : C.S} (hd : Dom s) (h : A.MustReachOrBlock Q n (σ.abs s)) :
    C.MustReach (fun c => Q (σ.abs c)) (n * (b + 1) + rank s) s := by
  have aux : ∀ (m n : Nat) (s : C.S), Dom s → n * (b + 1) + rank s ≤ m →
      A.MustReachOrBlock Q n (σ.abs s) →
      C.MustReach (fun c => Q (σ.abs c)) m s := by
    intro m
    induction m with
    | zero =>
      intro n s hd hle habs
      cases n with
      | zero => cases habs with | now hq => exact .now hq
      | succ n' =>
        cases habs with
        | now hq => exact .now hq
        | later _ =>
          have hmul : (n' + 1) * (b + 1) = n' * (b + 1) + (b + 1) :=
            Nat.succ_mul n' (b + 1)
          omega
    | succ m ih =>
      intro n s hd hle habs
      by_cases hq : Q (σ.abs s)
      · exact .now hq
      cases n with
      | zero => cases habs with | now hq' => exact absurd hq' hq
      | succ n' =>
        cases habs with
        | now hq' => exact absurd hq' hq
        | later next =>
          have hmul : (n' + 1) * (b + 1) = n' * (b + 1) + (b + 1) :=
            Nat.succ_mul n' (b + 1)
          refine .later (enabled s hd hq) (fun t ht => ?_)
          have hdt : Dom t := closed s t hd ht
          rcases σ.square s t ht with heq | hstep
          · have hlt : rank t < rank s := stutter s t hd ht heq
            refine ih (n' + 1) t hdt (by omega) ?_
            rw [heq]
            exact .later next
          · have hrb : rank t ≤ b := rank_le t hdt
            exact ih n' t hdt (by omega) (next _ hstep)
  exact aux (n * (b + 1) + rank s) n s hd (Nat.le_refl _) h

/-- The stated budget form: an abstract bound `K` becomes `K * (b+1) + b`. -/
theorem mustReach_pullback_budget {A C : TSys} (σ : StutterSimulation A C)
    {Q : A.S → Prop} {Dom : C.S → Prop} {rank : C.S → Nat} {b : Nat}
    (closed : ∀ s t, Dom s → C.step s t → Dom t)
    (rank_le : ∀ s, Dom s → rank s ≤ b)
    (stutter : ∀ s t, Dom s → C.step s t → σ.abs t = σ.abs s → rank t < rank s)
    (enabled : ∀ s, Dom s → ¬ Q (σ.abs s) → ∃ t, C.step s t)
    {K : Nat} {s : C.S} (hd : Dom s) (h : A.MustReachOrBlock Q K (σ.abs s)) :
    C.MustReach (fun c => Q (σ.abs c)) (K * (b + 1) + b) s :=
  (mustReach_pullback σ closed rank_le stutter enabled hd h).mono
    (by have := rank_le s hd; omega)

/-- **Bounded response across stuttering refinement**, at system level: the
spec bound `K` yields the implementation bound `K * (b+1) + b`. -/
theorem boundedResponse_pullback {A C : TSys} (σ : StutterSimulation A C)
    {P Q : A.S → Prop} {rank : C.S → Nat} {b K : Nat}
    (rank_le : ∀ s, C.Reachable s → rank s ≤ b)
    (stutter : ∀ s t, C.Reachable s → C.step s t → σ.abs t = σ.abs s →
      rank t < rank s)
    (enabled : ∀ s, C.Reachable s → ¬ Q (σ.abs s) → ∃ t, C.step s t)
    (h : A.BoundedResponse P Q K) :
    C.BoundedResponse (fun c => P (σ.abs c)) (fun c => Q (σ.abs c))
      (K * (b + 1) + b) := by
  intro s hr hp
  exact mustReach_pullback_budget σ (fun _ t hrs hst => .step hrs hst) rank_le
    stutter enabled hr (h _ (σ.reachable s hr) hp).toOrBlock

end StutterSimulation
end Loom
