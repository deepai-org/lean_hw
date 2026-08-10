-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Hw.System
import Machines.Tutorial.SatCounter

/-!
# Multi-clock demonstration: two saturating counters, independent clocks

The first rung of the multi-clock ladder, and the proof that the layer keeps
its promise. Two `SatCounter` islands (from the tutorial) run on two
independent domains — any schedule, any relative rate, no assumption. The
tutorial already proved each counter's safety invariant `SatOk` as an ordinary
single-clock `Design`. Here that proof transports to the two-clock system in
**one application** of `liftIsland`, with the schedule quantifier — "for every
interleaving of the two clocks" — supplied by `System.Invariant` itself.

Nothing about the counters changed; no schedule appears in the proof; the
system-level theorem is exactly the conjunction of the two local ones.
-/

namespace Machines.Multiclock.TwoCounters

open Loom.Hw
open Machines.Tutorial.SatCounter (design SatOk satOk_invariant)

/-- Two independent SatCounter islands. `admissible := fun _ => True`: the two
clocks are entirely unconstrained — arbitrary relative rate, arbitrary phase,
either or both ticking at any event. -/
def twoCounters : System where
  n := 2
  islands := fun _ => design

/-- Island 0's counter satisfies `SatOk` in every reachable state of the
two-clock system, under every schedule — transported from the single-clock
proof in one line. -/
theorem counter0_ok : twoCounters.Invariant (fun st => SatOk (st ⟨0, by decide⟩)) :=
  twoCounters.liftIsland ⟨0, by decide⟩ satOk_invariant

/-- The full-system safety property: BOTH counters satisfy `SatOk`, under every
interleaving of the two independent clocks. It is exactly the conjunction of
the two local invariants — the shape every compositional system proof takes,
and each conjunct cost nothing beyond its single-clock proof. -/
theorem bothCounters_ok :
    twoCounters.Invariant (fun st => SatOk (st ⟨0, by decide⟩) ∧ SatOk (st ⟨1, by decide⟩)) :=
  twoCounters.liftIsland₂ ⟨0, by decide⟩ ⟨1, by decide⟩ satOk_invariant satOk_invariant

end Machines.Multiclock.TwoCounters
