-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ChanRefinement

/-!
# Loss-explicit channel recovery refinement

`Chan.Refinement` proves that an implementation's successful transfers are
ordinary abstract queue steps.  Independent reset needs one additional
observable: the point at which a recovery protocol has quiesced both
endpoints and begins a fresh, empty channel epoch.

This file makes that point explicit.  A recovery step either performs one
ordinary `Chan.Event` or flushes the complete old queue.  The flushed values
are returned as `discarded`; reset is therefore not disguised as lossless
delivery.  A concrete protocol may take arbitrarily many conservative
stuttering steps before reporting `recovered = true`, but that report is its
linearization point and must re-establish the empty representation.

The interface is technology-neutral.  It mentions no reset-pin convention,
synchronizer, Gray pointer, FPGA primitive, ASIC macro, or synthesis tool.
-/

namespace Loom.Hw
namespace Chan

variable {w : Nat}

/-- The abstract event observed at the channel/recovery boundary. -/
inductive RecoveryEvent (width : Nat) where
  | transfer (event : Event width)
  | flush
  deriving DecidableEq, Repr

/-- One loss-explicit abstract step.  `discarded` is nonempty only when the
old epoch is flushed; a flush never simultaneously accepts or delivers. -/
structure RecoveryResult (width : Nat) where
  state : State width
  accepted : Option (BitVec width)
  delivered : Option (BitVec width)
  discarded : List (BitVec width)
  recovered : Bool
  deriving DecidableEq, Repr

def recoveryStep (c : Chan w) (queue : State w) :
    RecoveryEvent w → RecoveryResult w
  | .transfer event =>
      let result := c.step queue event
      { state := result.state
        accepted := if result.accepted then event.push else none
        delivered := result.delivered
        discarded := []
        recovered := false }
  | .flush =>
      { state := []
        accepted := none
        delivered := none
        discarded := queue
        recovered := true }

@[simp] theorem recoveryStep_flush (c : Chan w) (queue : State w) :
    c.recoveryStep queue .flush =
      { state := []
        accepted := none
        delivered := none
        discarded := queue
        recovered := true } := rfl

/-- Result reported by a concrete independently recoverable implementation.
`recovered` is a completed-protocol observation, not the raw assertion of an
island reset request. -/
structure ConcreteRecoveryResult (ConcreteState : Type) (width : Nat) where
  state : ConcreteState
  accepted : Option (BitVec width)
  delivered : Option (BitVec width)
  recovered : Bool

def ConcreteRecoveryResult.event
    {ConcreteState : Type} (result : ConcreteRecoveryResult ConcreteState w) :
    RecoveryEvent w :=
  if result.recovered then .flush else
    .transfer { push := result.accepted, pop := result.delivered.isSome }

/-- A concrete recovery-capable channel and its forward simulation.  The
step theorem forces a reported recovery completion to establish the empty
queue representation and to account for the complete discarded old epoch.
Implementation-internal request/ack traffic may stutter before that point. -/
structure RecoveryRefinement (c : Chan w) where
  ConcreteState : Type
  Request : Type
  reset : ConcreteState
  step : ConcreteState → Request → ConcreteRecoveryResult ConcreteState w
  Rep : State w → ConcreteState → Prop
  reset_refines : Rep [] reset
  step_refines : ∀ {queue concrete} (request : Request), Rep queue concrete →
    let physical := step concrete request
    let abstract := c.recoveryStep queue physical.event
    Rep abstract.state physical.state ∧
      abstract.accepted = physical.accepted ∧
      abstract.delivered = physical.delivered

namespace RecoveryRefinement

private theorem acceptedOption_eq {alpha : Type} (candidate : Option alpha)
    (accepted : Bool) (equal : accepted = candidate.isSome) :
    (if accepted then candidate else none) = candidate := by
  cases candidate <;> simp_all

/-- Trace result that retains epoch boundaries.  In particular, callers do
not have to infer a flush from missing payloads. -/
structure TraceResult (ConcreteState : Type) (width : Nat) where
  state : ConcreteState
  accepted : List (BitVec width)
  delivered : List (BitVec width)

def runConcrete {c : Chan w} (implementation : RecoveryRefinement c) :
    implementation.ConcreteState → List implementation.Request →
      TraceResult implementation.ConcreteState w
  | state, [] => ⟨state, [], []⟩
  | state, request :: rest =>
      let one := implementation.step state request
      let later := implementation.runConcrete one.state rest
      { state := later.state
        accepted := one.accepted.toList ++ later.accepted
        delivered := one.delivered.toList ++ later.delivered }

/-- Abstract trace execution retaining the exact queue discarded at every
recovery linearization point. -/
structure AbstractTraceResult (width : Nat) where
  state : State width
  accepted : List (BitVec width)
  delivered : List (BitVec width)
  discarded : List (List (BitVec width))

def runAbstract (c : Chan w) : State w → List (RecoveryEvent w) →
    AbstractTraceResult w
  | queue, [] => ⟨queue, [], [], []⟩
  | queue, event :: rest =>
      let one := c.recoveryStep queue event
      let later := runAbstract c one.state rest
      { state := later.state
        accepted := one.accepted.toList ++ later.accepted
        delivered := one.delivered.toList ++ later.delivered
        discarded := (if one.recovered then [one.discarded] else []) ++
          later.discarded }

def observedEvents {c : Chan w} (implementation : RecoveryRefinement c) :
    implementation.ConcreteState → List implementation.Request →
      List (RecoveryEvent w)
  | _, [] => []
  | state, request :: rest =>
      let one := implementation.step state request
      one.event :: implementation.observedEvents one.state rest

/-- Every finite concrete recovery trace is exactly the corresponding
loss-explicit abstract trace: successful transfers agree, every completed
recovery exposes one discarded old epoch, and the final states remain
related. -/
theorem run_refines {c : Chan w} (implementation : RecoveryRefinement c)
    (queue : State w) (concrete : implementation.ConcreteState)
    (requests : List implementation.Request) (rep : implementation.Rep queue concrete) :
    let events := implementation.observedEvents concrete requests
    let abstract := runAbstract c queue events
    let physical := implementation.runConcrete concrete requests
    implementation.Rep abstract.state physical.state ∧
      physical.accepted = abstract.accepted ∧
      physical.delivered = abstract.delivered := by
  induction requests generalizing queue concrete with
  | nil => simpa [observedEvents, runConcrete, runAbstract] using rep
  | cons request rest ih =>
      simp only [observedEvents, runConcrete, runAbstract]
      let one := implementation.step concrete request
      let event := one.event
      let abstractOne := c.recoveryStep queue event
      have oneRefines := implementation.step_refines request rep
      have later := ih abstractOne.state one.state oneRefines.1
      refine ⟨later.1, ?_, ?_⟩
      · change one.accepted.toList ++
          (implementation.runConcrete one.state rest).accepted = _
        rw [later.2.1, oneRefines.2.1]
      · change one.delivered.toList ++
          (implementation.runConcrete one.state rest).delivered = _
        rw [later.2.2, oneRefines.2.2]

/-- Reset-specialized finite-trace form.  The returned abstract result retains
the exact old queue at every recovery completion. -/
theorem equivalent {c : Chan w} (implementation : RecoveryRefinement c)
    (requests : List implementation.Request) :
    let events := implementation.observedEvents implementation.reset requests
    let abstract := runAbstract c [] events
    let physical := implementation.runConcrete implementation.reset requests
    implementation.Rep abstract.state physical.state ∧
      physical.accepted = abstract.accepted ∧
      physical.delivered = abstract.delivered :=
  implementation.run_refines [] implementation.reset requests
    implementation.reset_refines

/-- Existing transfer-only implementations embed without changing their
state relation or step theorem. They simply never report a live recovery. -/
def ofRefinement {c : Chan w} (implementation : Refinement c) :
    RecoveryRefinement c where
  ConcreteState := implementation.ConcreteState
  Request := implementation.Request
  reset := implementation.reset
  step := fun state request =>
    let result := implementation.step state request
    { state := result.state
      accepted := result.accepted
      delivered := result.delivered
      recovered := false }
  Rep := implementation.Rep
  reset_refines := implementation.reset_refines
  step_refines := by
    intro queue concrete request rep
    have refined := implementation.step_refines request rep
    rcases refined with ⟨stateRefines, acceptedRefines, deliveredRefines⟩
    refine ⟨stateRefines, ?_, deliveredRefines⟩
    exact acceptedOption_eq _ _ acceptedRefines

/-- A specification-level non-vacuity witness: either take an ordinary
implementation request or complete a recovery atomically.  This is not an
emitted CDC circuit; it proves the recovery interface itself is satisfiable
and states the exact target for a later distributed protocol refinement. -/
def atomicFlush {c : Chan w} (implementation : Refinement c) :
    RecoveryRefinement c where
  ConcreteState := implementation.ConcreteState
  Request := Option implementation.Request
  reset := implementation.reset
  step := fun state request =>
    match request with
    | some ordinary =>
        let result := implementation.step state ordinary
        { state := result.state
          accepted := result.accepted
          delivered := result.delivered
          recovered := false }
    | none =>
        { state := implementation.reset
          accepted := none
          delivered := none
          recovered := true }
  Rep := implementation.Rep
  reset_refines := implementation.reset_refines
  step_refines := by
    intro queue concrete request rep
    cases request with
    | some ordinary =>
        have refined := implementation.step_refines ordinary rep
        rcases refined with ⟨stateRefines, acceptedRefines, deliveredRefines⟩
        refine ⟨stateRefines, ?_, deliveredRefines⟩
        exact acceptedOption_eq _ _ acceptedRefines
    | none =>
        simp [ConcreteRecoveryResult.event, recoveryStep,
          implementation.reset_refines]

end RecoveryRefinement
end Chan
end Loom.Hw
