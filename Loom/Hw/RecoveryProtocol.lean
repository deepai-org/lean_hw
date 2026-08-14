-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ChanRecovery

/-!
# Technology-neutral channel recovery handshake

This is the executable protocol between the loss-explicit recovery contract
and a future pair of compiler-produced endpoint controllers.  A local reset
manager requests recovery while the corresponding channel clock is alive.
The two endpoints then:

1. latch and propagate the request;
2. stop accepting traffic at each endpoint as it joins recovery;
3. acknowledge that the peer is quiesced;
4. mark each local half flushed only after seeing that acknowledgement; and
5. linearize one abstract `.flush` after both local halves are flushed.

The four-phase request/acknowledgement levels cannot miss a stopped or slow
peer merely because of a clock ratio. Requests arriving while one recovery is
busy coalesce into that recovery. A new request after the handshake returns
idle creates a new epoch.

This protocol is intentionally a digital, schedule-executable model. Abrupt
power loss, reset-request pulse width, clock availability during the graceful
handshake, metastability, and physical reset distribution remain outside it.
-/

namespace Loom.Hw
namespace Chan.RecoveryProtocol

variable {w : Nat}

/-- One endpoint's distributed protocol state. The `peer*` pairs are the two
destination-clock synchronizer stages for the peer's request and
acknowledgement levels. -/
@[ext] structure Endpoint where
  recoverInputSeen : Bool := false
  request : Bool := false
  peerRequest0 : Bool := false
  peerRequest1 : Bool := false
  acknowledge : Bool := false
  peerAcknowledge0 : Bool := false
  peerAcknowledge1 : Bool := false
  flushed : Bool := false
  deriving DecidableEq, Repr

/-- The queue is present here so the handshake theorem can state its exact
loss-explicit abstraction. `recovering` is a specification ghost recording
whether a request has yet to produce its single completion event; the endpoint
bits are the distributed hardware state. -/
@[ext] structure State (width : Nat) where
  queue : Chan.State width := []
  source : Endpoint := {}
  sink : Endpoint := {}
  recovering : Bool := false
  deriving DecidableEq, Repr

/-- One executable clock event. `sourceRecover` and `sinkRecover` are graceful
requests sampled on their respective ticks, not asynchronous reset pins. -/
structure Request (width : Nat) where
  sourceTick : Bool := false
  sinkTick : Bool := false
  sourceRecover : Bool := false
  sinkRecover : Bool := false
  transfer : Chan.Event width := {}
  deriving DecidableEq, Repr

def reset (width : Nat) : State width := {}

def Endpoint.blocked (endpoint : Endpoint) (requestNow : Bool) : Bool :=
  requestNow || endpoint.request || endpoint.peerRequest1 || endpoint.flushed

def Endpoint.newRequest (endpoint : Endpoint) (requestNow : Bool) : Bool :=
  requestNow && !endpoint.recoverInputSeen

/-- A local reset edge is required when the peer acknowledgement first makes
the endpoint flushed, and reset remains asserted for the whole flushed phase.
Holding reset is essential under skew: a half that reset early must not resume
sampling the peer's pre-reset pointer before the peer has also reset. -/
def Endpoint.localFlush (endpoint : Endpoint) : Bool :=
  endpoint.request && endpoint.peerAcknowledge1

def Endpoint.resetHeld (endpoint : Endpoint) : Bool :=
  endpoint.flushed || endpoint.localFlush

/-- One local-clock transition. All right-hand sides read the pre-edge state,
matching ordinary `Design.cycle` semantics. -/
def Endpoint.step (endpoint : Endpoint) (tick requestNow peerRequest peerAck : Bool) :
    Endpoint :=
  if !tick then endpoint else
    let sawPeerRequest := endpoint.peerRequest1
    let localFlush := endpoint.localFlush
    let idle := !requestNow && !endpoint.request && !endpoint.peerRequest1 &&
      !endpoint.peerAcknowledge1
    { recoverInputSeen := requestNow
      request :=
        if endpoint.flushed then false
        else if endpoint.newRequest requestNow || sawPeerRequest then true
        else endpoint.request
      peerRequest0 := peerRequest
      peerRequest1 := endpoint.peerRequest0
      acknowledge := sawPeerRequest
      peerAcknowledge0 := peerAck
      peerAcknowledge1 := endpoint.peerAcknowledge0
      flushed := if idle then false else endpoint.flushed || localFlush }

@[simp] theorem Endpoint.resetHeld_of_flushed (endpoint : Endpoint)
    (flushed : endpoint.flushed = true) : endpoint.resetHeld = true := by
  simp [Endpoint.resetHeld, flushed]

/-- Whenever an edge establishes or preserves `flushed`, that same edge saw
reset asserted from the pre-edge endpoint state. -/
theorem Endpoint.resetHeld_of_step_flushed (endpoint : Endpoint)
    (tick requestNow peerRequest peerAck : Bool)
    (flushed : (endpoint.step tick requestNow peerRequest peerAck).flushed = true) :
    endpoint.resetHeld = true := by
  cases tick with
  | false => exact endpoint.resetHeld_of_flushed flushed
  | true =>
      simp only [Endpoint.step, Bool.not_true, Bool.false_eq_true, if_false] at flushed
      split at flushed
      · simp at flushed
      · simpa [Endpoint.resetHeld, Endpoint.localFlush] using flushed

def maskedTransfer (state : State w) (request : Request w) : Chan.Event w :=
  { push := if state.source.blocked request.sourceRecover then none
      else request.transfer.push
    pop := if state.sink.blocked request.sinkRecover then false
      else request.transfer.pop }

def nextSource (state : State w) (request : Request w) : Endpoint :=
  state.source.step request.sourceTick request.sourceRecover
    state.sink.request state.sink.acknowledge

def nextSink (state : State w) (request : Request w) : Endpoint :=
  state.sink.step request.sinkTick request.sinkRecover
    state.source.request state.source.acknowledge

/-- Completion is deliberately later than request assertion: both local
halves must have observed peer acknowledgement and reached their flushed
state. That is the one event represented by `System.RecoveryEvent`. -/
def completes (state : State w) (request : Request w) : Bool :=
  state.recovering && (nextSource state request).flushed &&
    (nextSink state request).flushed

def startsRecovery (state : State w) (request : Request w) : Bool :=
  (request.sourceTick && state.source.newRequest request.sourceRecover) ||
    (request.sinkTick && state.sink.newRequest request.sinkRecover)

def acceptedValue (result : Chan.Result w) (event : Chan.Event w) :
    Option (BitVec w) :=
  if result.accepted then event.push else none

def step (c : Chan w) (state : State w) (request : Request w) :
    Chan.ConcreteRecoveryResult (State w) w :=
  let source := nextSource state request
  let sink := nextSink state request
  let event := maskedTransfer state request
  let ordinary := c.step state.queue event
  let complete := completes state request
  { state :=
      { queue := if complete then [] else ordinary.state
        source
        sink
        recovering := if complete then false else
          state.recovering || startsRecovery state request }
    accepted := if complete then none else acceptedValue ordinary event
    delivered := if complete then none else ordinary.delivered
    recovered := complete }

def Rep (queue : Chan.State w) (state : State w) : Prop :=
  queue = state.queue

@[simp] theorem rep_reset : Rep ([] : Chan.State w) (reset w) := rfl

private theorem acceptedValue_isSome (c : Chan w) (queue : Chan.State w)
    (event : Chan.Event w) :
    (acceptedValue (c.step queue event) event).isSome =
      (c.step queue event).accepted := by
  unfold acceptedValue
  cases accepted : (c.step queue event).accepted
  · simp
  · cases pushed : event.push with
    | none => simp [Chan.step, pushed] at accepted
    | some value => simp

/-- The distributed handshake is a recovery refinement for every channel
width, depth, and co-tick policy. The theorem makes no clock-ratio or
technology assumption: arbitrary held-domain events simply stutter the local
endpoint protocol state. -/
def refinement (c : Chan w) : Chan.RecoveryRefinement c where
  ConcreteState := State w
  Request := Request w
  reset := reset w
  step := step c
  Rep := Rep
  reset_refines := rep_reset
  step_refines := by
    intro queue state request represented
    subst queue
    unfold step
    dsimp only
    cases completeEq : completes state request with
    | true =>
        simp [Chan.ConcreteRecoveryResult.event, Chan.recoveryStep, Rep]
    | false =>
        let event := maskedTransfer state request
        have observedEq :
            ({ push := acceptedValue (c.step state.queue event) event
               pop := (c.step state.queue event).delivered.isSome } : Chan.Event w) =
              c.successfulEvent state.queue event := rfl
        have normalized := c.step_successfulEvent state.queue event
        simp only [Bool.false_eq_true, if_false]
        dsimp only [Chan.ConcreteRecoveryResult.event, Chan.recoveryStep]
        rw [observedEq]
        simp only [Bool.false_eq_true, if_false]
        rw [normalized]
        refine ⟨rfl, ?_, rfl⟩
        unfold acceptedValue
        cases accepted : (c.step state.queue event).accepted with
        | false => simp
        | true =>
            simp only [Chan.successfulEvent, accepted, if_true]
            rfl

/-! ## System-coordinated linearization

The endpoint handshake above completes independently for each channel.  An
island with several incident channels must not expose those local completion
times as several `System.RecoveryEvent`s: the System contract has one atomic
island-reset event after every incident endpoint is quiescent.  The
coordinated view therefore retains the old logical queue as a ghost while a
physical FIFO may already be held in reset, and commits the loss-explicit
flush only when the System coordinator supplies `commit = true`.

This is not another circuit and `commit` is not a channel port.  It is the
linearization choice made by the structural System proof from the generated
coordinator's complete signal. -/
namespace Coordinated

/-- One endpoint event plus the System-level recovery commit. -/
structure Request (width : Nat) where
  endpoint : RecoveryProtocol.Request width := {}
  commit : Bool := false
  deriving DecidableEq, Repr

/-- A commit is admitted only after this channel's two physical halves have
completed their endpoint protocol and an epoch is actually pending. -/
def commitReady (state : State w) (request : Request w) : Bool :=
  state.recovering &&
    (nextSource state request.endpoint).flushed &&
    (nextSink state request.endpoint).flushed

def commits (state : State w) (request : Request w) : Bool :=
  request.commit && commitReady state request

/-- Recovery semantics with a globally selected linearization point.  Before
`commit`, endpoint blocking makes locally reset channels stutter while the
old abstract epoch remains available for exact discard accounting. -/
def step (c : Chan w) (state : State w) (request : Request w) :
    Chan.ConcreteRecoveryResult (State w) w :=
  let source := nextSource state request.endpoint
  let sink := nextSink state request.endpoint
  let event := maskedTransfer state request.endpoint
  let ordinary := c.step state.queue event
  let complete := commits state request
  { state :=
      { queue := if complete then [] else ordinary.state
        source
        sink
        recovering := if complete then false else
          state.recovering || startsRecovery state request.endpoint }
    accepted := if complete then none else acceptedValue ordinary event
    delivered := if complete then none else ordinary.delivered
    recovered := complete }

/-- Coordinated endpoint/recovery transition driven by an already observed
ordinary channel event. This is the composition form used with a conservative
physical FIFO: its actual accepted/delivered event, not the application's
attempted transfer, advances the retained logical epoch. -/
def stepObserved (c : Chan w) (state : State w) (request : Request w)
    (observed : Chan.Event w) : Chan.ConcreteRecoveryResult (State w) w :=
  let source := nextSource state request.endpoint
  let sink := nextSink state request.endpoint
  let ordinary := c.step state.queue observed
  let complete := commits state request
  { state :=
      { queue := if complete then [] else ordinary.state
        source
        sink
        recovering := if complete then false else
          state.recovering || startsRecovery state request.endpoint }
    accepted := if complete then none else acceptedValue ordinary observed
    delivered := if complete then none else ordinary.delivered
    recovered := complete }

/-- `stepObserved` is itself one exact loss-explicit abstract step after
normalizing the supplied event to the transfers the queue performed. -/
theorem stepObserved_refines (c : Chan w) (state : State w)
    (request : Request w) (observed : Chan.Event w) :
    let physical := stepObserved c state request observed
    let abstract := c.recoveryStep state.queue physical.event
    Rep abstract.state physical.state ∧
      abstract.accepted = physical.accepted ∧
      abstract.delivered = physical.delivered := by
  dsimp only
  unfold stepObserved
  cases completeEq : commits state request with
  | true =>
      simp [Chan.ConcreteRecoveryResult.event, Chan.recoveryStep, Rep]
  | false =>
      have observedEq :
          ({ push := acceptedValue (c.step state.queue observed) observed
             pop := (c.step state.queue observed).delivered.isSome } : Chan.Event w) =
            c.successfulEvent state.queue observed := rfl
      have normalized := c.step_successfulEvent state.queue observed
      simp only [Bool.false_eq_true, if_false]
      dsimp only [Chan.ConcreteRecoveryResult.event, Chan.recoveryStep]
      rw [observedEq]
      simp only [Bool.false_eq_true, if_false]
      rw [normalized]
      refine ⟨rfl, ?_, rfl⟩
      unfold acceptedValue
      cases accepted : (c.step state.queue observed).accepted with
      | false => simp
      | true =>
          simp only [Chan.successfulEvent, accepted, if_true]

theorem stepObserved_event_eq_flush_iff (c : Chan w) (state : State w)
    (request : Request w) (observed : Chan.Event w) :
    (stepObserved c state request observed).event = .flush ↔
      commits state request = true := by
  unfold stepObserved Chan.ConcreteRecoveryResult.event
  cases commits state request <;> simp

/-- Request surface used when composing the protocol with a conservative
physical FIFO. `observed` is its actual successful transfer event. -/
structure ObservedRequest (width : Nat) where
  control : Request width := {}
  observed : Chan.Event width := {}
  deriving DecidableEq, Repr

/-- Loss-explicit refinement whose queue advances from the physical FIFO's
observed event. This is the semantic interface selected by the stock recovery
binding; the ideal-attempt `refinement` below remains useful as a standalone
protocol model. -/
def observedRefinement (c : Chan w) : Chan.RecoveryRefinement c where
  ConcreteState := State w
  Request := ObservedRequest w
  reset := reset w
  step := fun state request => stepObserved c state request.control request.observed
  Rep := Rep
  reset_refines := rep_reset
  step_refines := by
    intro queue state request represented
    subst queue
    exact stepObserved_refines c state request.control request.observed

/-- The coordinated protocol remains a loss-explicit channel refinement for
all widths, depths, schedules, and commit choices.  Premature commits simply
stutter until the local protocol is ready. -/
def refinement (c : Chan w) : Chan.RecoveryRefinement c where
  ConcreteState := State w
  Request := Request w
  reset := reset w
  step := step c
  Rep := Rep
  reset_refines := rep_reset
  step_refines := by
    intro queue state request represented
    subst queue
    unfold step
    dsimp only
    cases completeEq : commits state request with
    | true =>
        simp [Chan.ConcreteRecoveryResult.event, Chan.recoveryStep, Rep]
    | false =>
        let event := maskedTransfer state request.endpoint
        have observedEq :
            ({ push := acceptedValue (c.step state.queue event) event
               pop := (c.step state.queue event).delivered.isSome } : Chan.Event w) =
              c.successfulEvent state.queue event := rfl
        have normalized := c.step_successfulEvent state.queue event
        simp only [Bool.false_eq_true, if_false]
        dsimp only [Chan.ConcreteRecoveryResult.event, Chan.recoveryStep]
        rw [observedEq]
        simp only [Bool.false_eq_true, if_false]
        rw [normalized]
        refine ⟨rfl, ?_, rfl⟩
        unfold acceptedValue
        cases accepted : (c.step state.queue event).accepted with
        | false => simp
        | true =>
            simp only [Chan.successfulEvent, accepted, if_true]
            rfl

theorem step_event_eq_flush_iff (c : Chan w) (state : State w)
    (request : Request w) :
    (step c state request).event = .flush ↔ commits state request = true := by
  unfold step Chan.ConcreteRecoveryResult.event
  cases commits state request <;> simp

theorem commit_of_event_flush (c : Chan w) (state : State w)
    (request : Request w) (flushed : (step c state request).event = .flush) :
    request.commit = true ∧ commitReady state request = true := by
  have complete := (step_event_eq_flush_iff c state request).mp flushed
  simpa [commits, Bool.and_eq_true] using complete

/-- A globally committed flush occurs on an edge that holds both physical
FIFO halves in reset. This is stronger than observing their post-edge done
levels: it pins the reset inputs seen by the controls and storage on the
linearization edge itself. -/
theorem commits_bothResetHeld (state : State w) (request : Request w)
    (complete : commits state request = true) :
    state.source.resetHeld = true ∧ state.sink.resetHeld = true := by
  have commitFacts : request.commit = true ∧ commitReady state request = true := by
    simpa [commits, Bool.and_eq_true] using complete
  have ready := commitFacts.2
  simp only [commitReady, Bool.and_eq_true] at ready
  have sourceFlushed :
      (nextSource state request.endpoint).flushed = true := by
    exact ready.1.2
  have sinkFlushed :
      (nextSink state request.endpoint).flushed = true := by
    exact ready.2
  exact
    ⟨Endpoint.resetHeld_of_step_flushed state.source
        request.endpoint.sourceTick request.endpoint.sourceRecover
        state.sink.request state.sink.acknowledge sourceFlushed,
      Endpoint.resetHeld_of_step_flushed state.sink
        request.endpoint.sinkTick request.endpoint.sinkRecover
        state.source.request state.source.acknowledge sinkFlushed⟩

theorem step_event_eq_transfer_of_not_commit (c : Chan w) (state : State w)
    (request : Request w) (incomplete : commits state request = false) :
    (step c state request).event =
      .transfer (c.successfulEvent state.queue
        (maskedTransfer state request.endpoint)) := by
  unfold step Chan.ConcreteRecoveryResult.event
  simp only [incomplete, Bool.false_eq_true, if_false]
  congr 1

end Coordinated

/-- The protocol's recovery linearization point is not merely compatible
with the abstract contract: it is exactly the event classified as `.flush`.
This pins the event consumed by the System-level recovery join. -/
theorem step_event_eq_flush_iff (c : Chan w) (state : State w)
    (request : Request w) :
    (step c state request).event = .flush ↔ completes state request = true := by
  unfold step Chan.ConcreteRecoveryResult.event
  cases completes state request <;> simp

/-- Before the recovery linearization point, the wrapper exposes precisely
the successful ordinary FIFO transfer. Conservative stalls therefore remain
ordinary abstract stuttering, rather than becoming an implicit recovery
event. -/
theorem step_event_eq_transfer_of_not_complete (c : Chan w) (state : State w)
    (request : Request w) (incomplete : completes state request = false) :
    (step c state request).event =
      .transfer (c.successfulEvent state.queue (maskedTransfer state request)) := by
  unfold step Chan.ConcreteRecoveryResult.event
  simp only [incomplete, Bool.false_eq_true, if_false]
  congr 1

/-- A request is complete only after both distributed halves have reached
their local flushed state. -/
theorem completes_bothFlushed (state : State w) (request : Request w)
    (complete : completes state request = true) :
    (nextSource state request).flushed = true ∧
      (nextSink state request).flushed = true := by
  cases sourceEq : (nextSource state request).flushed <;>
    cases sinkEq : (nextSink state request).flushed <;>
    simp [completes, sourceEq, sinkEq] at complete ⊢

/-- A completing protocol event resets both FIFO halves on their respective
completion edges. Their subsequently asserted `flushed` levels keep both
halves reset until the four-phase handshake releases them. -/
theorem completes_bothResetHeld (state : State w) (request : Request w)
    (complete : completes state request = true) :
    state.source.resetHeld = true ∧ state.sink.resetHeld = true := by
  have flushed := completes_bothFlushed state request complete
  exact
    ⟨Endpoint.resetHeld_of_step_flushed state.source request.sourceTick
        request.sourceRecover state.sink.request state.sink.acknowledge flushed.1,
      Endpoint.resetHeld_of_step_flushed state.sink request.sinkTick
        request.sinkRecover state.source.request state.source.acknowledge flushed.2⟩

/-- Recovery completion never shares an abstract event with a transfer. -/
theorem step_complete_quiet (c : Chan w) (state : State w) (request : Request w)
    (complete : completes state request = true) :
    (step c state request).accepted = none ∧
      (step c state request).delivered = none ∧
      (step c state request).state.queue = [] := by
  simp [step, complete]

/-- Held clocks preserve all state owned by that endpoint. -/
theorem source_held (state : State w) (request : Request w)
    (held : request.sourceTick = false) :
    nextSource state request = state.source := by
  simp [nextSource, Endpoint.step, held]

theorem sink_held (state : State w) (request : Request w)
    (held : request.sinkTick = false) :
    nextSink state request = state.sink := by
  simp [nextSink, Endpoint.step, held]

end Chan.RecoveryProtocol
end Loom.Hw
