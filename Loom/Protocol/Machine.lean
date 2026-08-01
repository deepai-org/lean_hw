-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Core.Ts
import Mathlib.Logic.Relation

/-!
# Protocol machines (D34)

`Loom/Core/Ts.lean` gives the transition-system spine: a state type, initial
states, and a step *relation*. Every mechanized protocol machine in this
repository (`Machines/Epoch/Protocol.lean` §3 epoch cells,
`Machines/CapWalk/Protocol.lean` §2.2 capabilities) reaches that spine the
same way, and hand-rolled the same skeleton to get there:

* an event alphabet `Ev`;
* a **partial** step `stepEv : S → Ev → Option S`, where `none` means
  "this event is disabled in this state";
* `Step s s' := ∃ e, stepEv s e = some s'`, and the `TSys` built from it;
* `Run := Relation.ReflTransGen Step`;
* a multi-field invariant structure with an `Init.inv` / `inv_step` pair,
  packaged into `TSys.Inductive` and then `TSys.Invariant`;
* run-level closures of step-level facts: monotone measures, sticky bits,
  quantities no step changes.

None of that is engine-specific. This file is that skeleton, once.

## What is here, and why each piece

The abstraction is `ProtocolSpec` (state, event alphabet, initial states,
partial step) and `InvSpec` (the invariant bundle). Everything else is a
derivation. The rule the ledger states — *unused generality is a cost* —
was applied literally: every lemma below is instantiated by at least one of
the two existing engines in `Machines/Epoch/ProtocolLib.lean` or
`Machines/CapWalk/ProtocolLib.lean`, and nothing else is offered.

`toTSys` is a plain structure literal, so a hand-written engine `sys` and
its reconstruction through this file are *definitionally* equal, and
everything already stated over `TSys` — refinement (`Simulation`,
`StutterSimulation`), bounded response (`Loom/Core/Bounded.lean`) — applies
to a `ProtocolSpec` with no glue at all.
-/

namespace Loom

/-- A protocol machine: a state space, an event alphabet, initial states,
and a **partial** step function. `stepEv s e = none` is the disabled event —
the shape every guard in a protocol spec takes ("`bump` is enabled only when
no bump is in flight"). -/
structure ProtocolSpec where
  /-- The state space. -/
  S : Type
  /-- The event alphabet. -/
  E : Type
  /-- Initial (reset) states. -/
  init : S → Prop
  /-- The partial transition function; `none` = the event is disabled. -/
  stepEv : S → E → Option S

namespace ProtocolSpec

variable {P : ProtocolSpec}

/-- The step relation: some event is enabled and takes `s` to `s'`. -/
def Step (P : ProtocolSpec) (s s' : P.S) : Prop := ∃ e, P.stepEv s e = some s'

/-- The protocol machine as a `Loom.TSys` — the spine every refinement,
invariance and bounded-response statement is made over. -/
def toTSys (P : ProtocolSpec) : Loom.TSys where
  S := P.S
  init := P.init
  step := P.Step

/-- Multi-step reachability *from a given state*: the "forever" of a
protocol guarantee. -/
abbrev Run (P : ProtocolSpec) (s t : P.S) : Prop :=
  Relation.ReflTransGen P.Step s t

/-- Reachability from a reset state. -/
abbrev Reachable (P : ProtocolSpec) (s : P.S) : Prop := P.toTSys.Reachable s

@[simp] theorem toTSys_step {s s' : P.S} : P.toTSys.step s s' ↔ P.Step s s' := Iff.rfl

/-! ### Enabled, disabled, stuttering -/

/-- An enabled event is a step. -/
theorem step_of_stepEv {s s' : P.S} {e : P.E} (h : P.stepEv s e = some s') :
    P.Step s s' := ⟨e, h⟩

/-- A disabled event contributes no step: nothing at all follows from it.
This is the glue that makes a protocol's case analysis discharge its
disabled branches. -/
theorem not_stepEv_of_disabled {s s' : P.S} {e : P.E} (h : P.stepEv s e = none) :
    P.stepEv s e ≠ some s' := by rw [h]; simp

/-- If every event is disabled, the state has no successor at all: this is
what "deadlock" means for a protocol machine, and it is the side condition
`Loom/Core/Bounded.lean`'s `MustReach` refuses to leave implicit. -/
theorem no_step_of_all_disabled {s : P.S} (h : ∀ e, P.stepEv s e = none) :
    ¬ ∃ s', P.Step s s' := by
  rintro ⟨s', e, he⟩
  exact not_stepEv_of_disabled (h e) he

/-- An event that is enabled but leaves the state alone **stutters**: it is
a genuine step of the system that no state predicate can observe. Both
engines model their pure-read observation (§3's `use`, §2.2's capability
check) exactly this way, which is what lets a run interleave observations
with real transitions. -/
theorem stutter {s : P.S} {e : P.E} (h : P.stepEv s e = some s) : P.Step s s :=
  step_of_stepEv h

/-! ### Running a list of events -/

/-- Run a list of events from `s`, stopping at the first disabled one. -/
def runEvents (P : ProtocolSpec) (s : P.S) : List P.E → Option P.S
  | [] => some s
  | e :: es => (P.stepEv s e).bind (fun s' => P.runEvents s' es)

@[simp] theorem runEvents_nil {s : P.S} : P.runEvents s [] = some s := rfl

@[simp] theorem runEvents_cons {s : P.S} {e : P.E} {es : List P.E} :
    P.runEvents s (e :: es) = (P.stepEv s e).bind (fun s' => P.runEvents s' es) := rfl

/-- A completed event list is a run. This is how an explicit multi-step
witness (a protocol's own bump/ack/return sequence, say) is turned into the
`Run` the theorems speak about, without hand-chaining `ReflTransGen`. -/
theorem run_of_runEvents {s t : P.S} : ∀ (es : List P.E),
    P.runEvents s es = some t → P.Run s t
  | [], h => by
      rw [runEvents_nil, Option.some.injEq] at h; exact h ▸ Relation.ReflTransGen.refl
  | e :: es, h => by
      rw [runEvents_cons] at h
      cases hs : P.stepEv s e with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some u =>
          rw [hs] at h
          exact Relation.ReflTransGen.head (step_of_stepEv hs) (run_of_runEvents es h)

/-! ### Run-level closures of step-level facts

Each of the four shapes below appears verbatim in both engines; they are
the whole content of their `RunLemmas` sections. -/

/-- A predicate preserved by every step is preserved along every run
(sticky bits: `poison`, `dead`). -/
theorem run_closure {p : P.S → Prop}
    (hstep : ∀ s s', P.Step s s' → p s → p s') {s t : P.S}
    (hrun : P.Run s t) (hp : p s) : p t := by
  induction hrun with
  | refl => exact hp
  | tail _ hst ih => exact hstep _ _ hst ih

/-- A measure no step decreases is non-decreasing along every run
(monotone counters: home epochs). -/
theorem run_mono (μ : P.S → Nat)
    (hstep : ∀ s s', P.Step s s' → μ s ≤ μ s') {s t : P.S}
    (hrun : P.Run s t) : μ s ≤ μ t :=
  run_closure (p := fun u => μ s ≤ μ u) (fun a b hab h => Nat.le_trans h (hstep a b hab))
    hrun (Nat.le_refl _)

/-- A quantity no step changes is constant along every run (slot
occupancy: not a transition target). -/
theorem run_const {α : Type} (f : P.S → α)
    (hstep : ∀ s s', P.Step s s' → f s' = f s) {s t : P.S}
    (hrun : P.Run s t) : f t = f s :=
  run_closure (p := fun u => f u = f s)
    (fun a b hab h => by show f b = f s; rw [hstep a b hab]; exact h) hrun rfl

/-! ## The invariant bundle -/

/-- An invariant bundle: the predicate, its reset obligation, and its
preservation obligation **stated against the partial step**, so the proof
is a case analysis on the event alphabet — which is how both engines
actually write it. -/
structure InvSpec (P : ProtocolSpec) where
  /-- The invariant. -/
  Inv : P.S → Prop
  /-- Every reset state satisfies it. -/
  init : ∀ s, P.init s → Inv s
  /-- Every enabled event preserves it. -/
  step : ∀ (s : P.S) (e : P.E) (s' : P.S), Inv s → P.stepEv s e = some s' → Inv s'

namespace InvSpec

variable {P : ProtocolSpec} (I : InvSpec P)

/-- The relational form of the preservation obligation. -/
theorem step_rel {s s' : P.S} (hi : I.Inv s) (h : P.Step s s') : I.Inv s' := by
  obtain ⟨e, he⟩ := h
  exact I.step s e s' hi he

/-- The bundle is exactly a `TSys.Inductive` predicate. -/
theorem inductive_ : P.toTSys.Inductive I.Inv where
  init := I.init
  step := fun _ _ hi h => I.step_rel hi h

/-- …hence an invariant of every reachable state. -/
theorem invariant : P.toTSys.Invariant I.Inv := I.inductive_.invariant

/-- …and it holds all along any run out of a state that satisfies it. -/
theorem run {s t : P.S} (hi : I.Inv s) (hrun : P.Run s t) : I.Inv t :=
  run_closure (p := I.Inv) (fun _ _ h hp => I.step_rel hp h) hrun hi

/-- The invariant-dependent monotone measure: a step-level bound that needs
the invariant at the *source* state still lifts to runs, because the
invariant holds all along them (`Machines/Epoch`'s replica monotonicity is
exactly this — a replica adopts the broadcast epoch, which only the
invariant places at or above it). -/
theorem run_mono (μ : P.S → Nat)
    (hstep : ∀ s s', I.Inv s → P.Step s s' → μ s ≤ μ s') {s t : P.S}
    (hi : I.Inv s) (hrun : P.Run s t) : μ s ≤ μ t := by
  induction hrun with
  | refl => exact Nat.le_refl _
  | tail hr hst ih => exact Nat.le_trans ih (hstep _ _ (I.run hi hr) hst)

end InvSpec
end ProtocolSpec
end Loom
