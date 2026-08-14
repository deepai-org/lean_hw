-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Chan

/-!
# Certified implementations of abstract channels

`Chan` deliberately says nothing about how a queue crosses a clock boundary.
This file is the semantic plug-in interface for implementations.  A concrete
machine may stall a request, but every transfer it reports must be exactly one
step of the abstract queue and its concrete state must continue to represent
the resulting queue.

The interface contains no vendor, synthesis-tool, pointer encoding, or RTL
choice.  Loom's synchronous adapter, stock toggle mailbox, and stock Gray FIFO
can implement it; users may implement it for a hardened macro or their own CDC
circuit without changing `Chan` or `System`.
-/

namespace Loom.Hw
namespace Chan

variable {w : Nat}

/-- Standard observation returned by a concrete channel implementation.
`accepted` contains the payload actually accepted, not merely requested. -/
structure ConcreteResult (ConcreteState : Type) (width : Nat) where
  state : ConcreteState
  accepted : Option (BitVec width)
  delivered : Option (BitVec width)

/-- Turn the successful transfers of a concrete step into the one abstract
event they claim to implement.  Conservative physical stalls simply produce
no abstract push or pop on that event. -/
def ConcreteResult.event {ConcreteState : Type} (result : ConcreteResult ConcreteState w) :
    Event w :=
  { push := result.accepted, pop := result.delivered.isSome }

/-- A concrete executable channel machine together with its checked forward
simulation to one abstract `Chan`.  This is the proof-facing interface behind
a physical realization choice; it is not stored in the abstract channel
handle. -/
structure Refinement (c : Chan w) where
  ConcreteState : Type
  Request : Type
  reset : ConcreteState
  step : ConcreteState → Request → ConcreteResult ConcreteState w
  Rep : State w → ConcreteState → Prop
  reset_refines : Rep [] reset
  step_refines : ∀ {queue concrete} (request : Request), Rep queue concrete →
    let physical := step concrete request
    let abstract := c.step queue physical.event
    Rep abstract.state physical.state ∧
      abstract.accepted = physical.accepted.isSome ∧
      abstract.delivered = physical.delivered

namespace Refinement

/-- Trace result common to every certified concrete implementation. -/
structure TraceResult (ConcreteState : Type) (width : Nat) where
  state : ConcreteState
  accepted : List (BitVec width)
  delivered : List (BitVec width)

def runConcrete {c : Chan w} (implementation : Refinement c) :
    implementation.ConcreteState → List implementation.Request →
      TraceResult implementation.ConcreteState w
  | state, [] => ⟨state, [], []⟩
  | state, request :: rest =>
      let one := implementation.step state request
      let later := implementation.runConcrete one.state rest
      ⟨later.state, one.accepted.toList ++ later.accepted,
        one.delivered.toList ++ later.delivered⟩

def observedEvents {c : Chan w} (implementation : Refinement c) :
    implementation.ConcreteState → List implementation.Request → List (Event w)
  | _, [] => []
  | state, request :: rest =>
      let one := implementation.step state request
      one.event :: implementation.observedEvents one.state rest

/-- The reusable finite-trace theorem supplied by the interface.  A certified
implementation cannot lose, duplicate, corrupt, or reorder accepted payloads,
regardless of how its request/adversary type represents clock timing. -/
theorem run_refines {c : Chan w} (implementation : Refinement c)
    (queue : State w) (concrete : implementation.ConcreteState)
    (requests : List implementation.Request) (rep : implementation.Rep queue concrete) :
    let abstract := c.runTrace queue
      (implementation.observedEvents concrete requests)
    let physical := implementation.runConcrete concrete requests
    implementation.Rep abstract.state physical.state ∧
      physical.accepted = abstract.accepted ∧
      physical.delivered = abstract.delivered := by
  induction requests generalizing queue concrete with
  | nil => simpa [observedEvents, runConcrete, Chan.runTrace] using rep
  | cons request rest ih =>
      simp only [observedEvents, runConcrete, Chan.runTrace]
      let one := implementation.step concrete request
      have oneRefines := implementation.step_refines request rep
      have later := ih (c.step queue one.event).state one.state oneRefines.1
      exact ⟨later.1,
        by
          change one.accepted.toList ++
              (implementation.runConcrete one.state rest).accepted = _
          have first : one.accepted.toList = c.acceptedValues queue one.event := by
            unfold Chan.acceptedValues
            rw [oneRefines.2.1]
            cases accepted : one.accepted <;> simp [ConcreteResult.event, accepted]
          rw [first, later.2.1],
        by
          change one.delivered.toList ++
              (implementation.runConcrete one.state rest).delivered = _
          have first : one.delivered.toList = c.deliveredValues queue one.event := by
            unfold Chan.deliveredValues
            rw [oneRefines.2.2]
          rw [first, later.2.2]⟩

/-- Reset-specialized form used by stock and user-defined implementations. -/
theorem equivalent {c : Chan w} (implementation : Refinement c)
    (requests : List implementation.Request) :
    let abstract := c.runTrace []
      (implementation.observedEvents implementation.reset requests)
    let physical := implementation.runConcrete implementation.reset requests
    implementation.Rep abstract.state physical.state ∧
      physical.accepted = abstract.accepted ∧
      physical.delivered = abstract.delivered :=
  implementation.run_refines [] implementation.reset requests
    implementation.reset_refines

end Refinement
end Chan
end Loom.Hw
