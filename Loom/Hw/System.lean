-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics

/-!
# Multi-clock systems: synchronous islands under a schedule

`Design.cycle` is one synchronous step and stays exactly what it is. A
`System` composes several `Design` **islands**, each clocked by its own
domain, and a **schedule** decides which islands tick at each event. Nothing
here idealizes the clocks: a schedule is an arbitrary `Nat → ClockEvent`,
constrained only by the system's `admissible` predicate (drift, fairness, or
ratio bounds — or nothing).

The two load-bearing results, both **schedule-independent**:

* `advance_unticked` — an island that does not tick this event is unchanged.
  The per-event frame.
* `island_reachable` / `liftIsland` — the cumulative frame, and the payoff:
  **an island in a system only ever reaches states it could reach alone**, so
  any invariant proved of an island as an ordinary `Design` transports to the
  whole system, for *every* admissible schedule, in one line. This is the
  multi-clock generalization of `Frame.lean`'s single-cycle non-interference,
  and it is what keeps full-system proofs from scaling with the product of the
  domains: prove each island once, in plain `Design` land, and lift.

Channels, endpoint laws, and concrete CDC refinement (see `CdcSnapshot.lean`
for the stability→coherence vocabulary they will use) are separate increments
on top of this core; this file is only the island layer and its frame.
-/

namespace Loom.Hw

/-- Which islands tick at one clock event. A **set** of ticking domains, not a
single chosen one, so genuinely aligned edges — two islands clocked together —
are expressible, and a channel between co-ticking islands sees a same-event
exchange. -/
abbrev ClockEvent (n : Nat) := Fin n → Bool

/-- One clock event per time step. The `admissible` predicate below carves out
the legal schedules; the frame results here hold for *all* of them. -/
abbrev Schedule (n : Nat) := Nat → ClockEvent n

/-- A multi-clock system: `n` synchronous `Design` islands and a predicate
selecting admissible schedules (unconstrained by default — the frame theorems
never need it). -/
structure System where
  n : Nat
  islands : Fin n → Design
  admissible : Schedule n → Prop := fun _ => True

/-- System state: one island state vector plus the event index. All Loom
designs share the state *type* `St`; islands do not alias because each holds
its own full `St`. -/
abbrev System.State (sys : System) := (Fin sys.n → St) × Nat

/-- Advance one event. Every ticking island runs its own `cycle`; the rest
hold. Reads see the pre-event vector and all ticked updates commit together,
consistent with `Design.cycle`'s own edge semantics. -/
def System.advance (sys : System) (e : ClockEvent sys.n)
    (st : Fin sys.n → St) : Fin sys.n → St :=
  fun i => if e i then (sys.islands i).cycle (st i) else st i

/-- The transition system under one fixed schedule — deterministic given the
schedule. The schedule quantifier lives in `System.Invariant`, not here. -/
def System.tsysUnder (sys : System) (sched : Schedule sys.n) : Loom.TSys where
  S := sys.State
  init := fun s => s.2 = 0 ∧ ∀ i, s.1 i = (sys.islands i).reset
  step := fun s s' => s'.2 = s.2 + 1 ∧ s'.1 = sys.advance (sched s.2) s.1

/-- A system invariant holds in every reachable state, under **every**
admissible schedule. The user never writes a schedule: "for all interleavings"
is what the definition *means*, exactly as "reads see pre-cycle state" is what
`Design.cycle` means. -/
def System.Invariant (sys : System) (P : (Fin sys.n → St) → Prop) : Prop :=
  ∀ sched, sys.admissible sched →
    (sys.tsysUnder sched).Invariant (fun s => P s.1)

/-! ## The frame -/

/-- Per-event frame: an island that does not tick is unchanged. -/
@[simp] theorem System.advance_unticked (sys : System) (e : ClockEvent sys.n)
    (st : Fin sys.n → St) {i : Fin sys.n} (h : e i = false) :
    sys.advance e st i = st i := by
  simp [System.advance, h]

/-- A ticking island advances by exactly its own `cycle`. -/
@[simp] theorem System.advance_ticked (sys : System) (e : ClockEvent sys.n)
    (st : Fin sys.n → St) {i : Fin sys.n} (h : e i = true) :
    sys.advance e st i = (sys.islands i).cycle (st i) := by
  simp [System.advance, h]

/-- **The core theorem.** In any reachable system state, under any schedule,
each island's state is reachable by that island *alone* — the system never
fabricates an island state the island could not reach on its own clock. -/
theorem System.island_reachable (sys : System) (sched : Schedule sys.n)
    {s : sys.State} (hr : (sys.tsysUnder sched).Reachable s) (i : Fin sys.n) :
    (sys.islands i).toTSys.Reachable (s.1 i) := by
  -- Generalize the reachable state so the induction motive is over it.
  suffices h : ∀ t, (sys.tsysUnder sched).Reachable t →
      (sys.islands i).toTSys.Reachable (t.1 i) from h s hr
  intro t ht
  induction ht with
  | init h =>
      rw [h.2 i]
      exact Loom.TSys.Reachable.init (show (sys.islands i).reset = _ from rfl)
  | step _ hstep ih =>
      rename_i a a' _
      obtain ⟨_, hadv⟩ := hstep
      rw [hadv]
      by_cases he : sched a.2 i = true
      · rw [sys.advance_ticked _ _ he]
        exact Loom.TSys.Reachable.step ih (show (sys.islands i).cycle (a.1 i) = _ from rfl)
      · rw [sys.advance_unticked _ _ (by simpa using he)]
        exact ih

/-- **The payoff.** An invariant of an island as an ordinary `Design` lifts to
a system invariant — for every admissible schedule — in one application. This
is the multi-clock `invariant_pullback`: island proofs are written in plain
`Design` land and never mention schedules, clocks, or the other islands. -/
theorem System.liftIsland (sys : System) (i : Fin sys.n) {Q : St → Prop}
    (hQ : (sys.islands i).toTSys.Invariant Q) :
    sys.Invariant (fun st => Q (st i)) := by
  intro sched _ s hr
  exact hQ _ (sys.island_reachable sched hr i)

/-- A conjunction of lifted island invariants is a system invariant — the
shape a full-system safety property takes before channel obligations are
added: `∧` of local invariants, each transported for free. -/
theorem System.liftIsland₂ (sys : System) (i j : Fin sys.n)
    {Q R : St → Prop}
    (hQ : (sys.islands i).toTSys.Invariant Q)
    (hR : (sys.islands j).toTSys.Invariant R) :
    sys.Invariant (fun st => Q (st i) ∧ R (st j)) := by
  intro sched hadm s hr
  exact ⟨sys.liftIsland i hQ sched hadm s hr, sys.liftIsland j hR sched hadm s hr⟩

end Loom.Hw
