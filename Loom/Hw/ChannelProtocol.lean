-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.System
import Loom.Hw.TraceContract

/-!
# Compositional channel protocol proofs

This file is the stable semantic proof layer between application endpoints and
`System`.  It deliberately does not mention a CDC circuit.  A payload has one
logical owner at a time:

* a destination presentation buffer (oldest);
* unreserved abstract FIFO storage;
* a source staging slot (newest).

The conservative registered sink deserves special care.  Once the application
consumes the visible head, the still-asserted physical pop is an acknowledgement
debt; it is not another owned copy of that payload.  `unreservedQueue` therefore
drops that head while the acknowledgement is pending.  This makes the ledger
non-overlapping even though the physical queue does not drop the head until the
next destination event.
-/

namespace Loom.Hw

namespace Chan

variable {w : Nat}

/-- Logical ownership regions in consumer-to-producer order.  Separate fields
make ownership transfer explicit and prevent a proof from silently counting a
payload in both a presentation buffer and the FIFO. -/
structure Ownership (width : Nat) where
  presented : List (BitVec width) := []
  queued : List (BitVec width) := []
  staged : List (BitVec width) := []
  deriving DecidableEq, Repr

/-- The ordered in-flight payload sequence. -/
def Ownership.inventory (ownership : Ownership w) : List (BitVec w) :=
  ownership.presented ++ ownership.queued ++ ownership.staged

/-- A conservation step at the application boundary.  Accepted values enter
at the producer end and consumed values leave at the consumer end. -/
def OwnershipStep (before : Ownership w) (accepted consumed : List (BitVec w))
    (after : Ownership w) : Prop :=
  before.inventory ++ accepted = consumed ++ after.inventory

@[simp] theorem OwnershipStep.nil (ownership : Ownership w) :
    OwnershipStep ownership [] [] ownership := by
  simp [OwnershipStep, Ownership.inventory]

/-- Conservation composes without exposing intermediate buffering. -/
theorem OwnershipStep.comp {before middle after : Ownership w}
    {accepted₁ consumed₁ accepted₂ consumed₂ : List (BitVec w)}
    (first : OwnershipStep before accepted₁ consumed₁ middle)
    (second : OwnershipStep middle accepted₂ consumed₂ after) :
    OwnershipStep before (accepted₁ ++ accepted₂) (consumed₁ ++ consumed₂) after := by
  unfold OwnershipStep at first second ⊢
  calc
    before.inventory ++ (accepted₁ ++ accepted₂) =
        (before.inventory ++ accepted₁) ++ accepted₂ := by simp
    _ = (consumed₁ ++ middle.inventory) ++ accepted₂ := by rw [first]
    _ = consumed₁ ++ (middle.inventory ++ accepted₂) := by simp
    _ = consumed₁ ++ (consumed₂ ++ after.inventory) := by rw [second]
    _ = (consumed₁ ++ consumed₂) ++ after.inventory := by simp

/-- The FIFO portion still owned by the channel/application boundary.  With a
registered pop outstanding, the head was already consumed by the application
and is retained physically only until the acknowledgement event. -/
def unreservedQueue (queue : State w) (popPending : Bool) : State w :=
  if popPending then queue.drop 1 else queue

/-- Values consumed by an application on this destination edge. -/
def applicationConsumed (queue : State w) (consume : Bool) : List (BitVec w) :=
  if consume then queue.take 1 else []

/-- The stock registered source and conservative sink viewed as a single,
non-overlapping ownership inventory. -/
def registeredOwnership (queue : State w)
    (sourceValid : Bool) (sourcePayload : BitVec w)
    (sinkPopPending : Bool) : Ownership w where
  queued := unreservedQueue queue sinkPopPending
  staged := sourcePending sourceValid sourcePayload

/-- The conservative sink transfers ownership exactly once.  A newly accepted
FIFO push is appended at the producer side; an application consume removes the
oldest unreserved value even though its physical pop completes one event later.

`consumeLegal` is the generated `canDeq` rule.  `pendingLegal` says an old pop
was issued only for a real head. -/
theorem registeredSink_conservation (c : Chan w) (queue : State w)
    (push : Option (BitVec w)) (popPending consume : Bool)
    (pendingLegal : popPending = true → queue.isEmpty = false)
    (consumeLegal : consume = true →
      popPending = false ∧ queue.isEmpty = false) :
    unreservedQueue queue popPending ++
        c.acceptedValues queue { push, pop := popPending } =
      applicationConsumed queue consume ++
        unreservedQueue (c.step queue { push, pop := popPending }).state consume := by
  rcases c with ⟨name, depth, policy⟩
  cases queue with
  | nil =>
      cases push <;> cases popPending <;> cases consume <;> cases policy <;>
        simp [unreservedQueue, applicationConsumed, acceptedValues, step]
          at pendingLegal consumeLegal ⊢
  | cons head tail =>
      cases push <;> cases popPending <;> cases consume <;> cases policy <;>
        simp [unreservedQueue, applicationConsumed, acceptedValues, step]
          at pendingLegal consumeLegal ⊢
      all_goals split <;> simp_all

/-- Schedule-aware conservative sink ledger.  An unticked destination neither
consumes nor acknowledges its outstanding reservation; source-only pushes may
still extend the queue tail without changing ownership of the reserved head. -/
theorem scheduledSink_conservation (c : Chan w) (queue : State w)
    (push : Option (BitVec w)) (popPending sinkFires consume : Bool)
    (pendingLegal : popPending = true → queue.isEmpty = false)
    (consumeLegal : consume = true →
      sinkFires = true ∧ popPending = false ∧ queue.isEmpty = false)
    (consumeNoneUnticked : sinkFires = false → consume = false) :
    unreservedQueue queue popPending ++
        c.acceptedValues queue { push, pop := sinkFires && popPending } =
      applicationConsumed queue consume ++
        unreservedQueue
          (c.step queue { push, pop := sinkFires && popPending }).state
          (if sinkFires then consume else popPending) := by
  cases sinkFires
  · have noConsume := consumeNoneUnticked rfl
    subst consume
    rcases c with ⟨name, depth, policy⟩
    cases queue with
    | nil =>
        cases push <;> cases popPending <;> cases policy <;>
          simp [unreservedQueue, applicationConsumed, acceptedValues, step]
            at pendingLegal ⊢
    | cons head tail =>
        cases push <;> cases popPending <;> cases policy <;>
          simp [unreservedQueue, applicationConsumed, acceptedValues, step]
            at pendingLegal ⊢
        all_goals split <;> simp_all
  · apply registeredSink_conservation c queue push popPending consume
      pendingLegal
    intro consumed
    exact ⟨(consumeLegal consumed).2.1, (consumeLegal consumed).2.2⟩

/-- Inputs needed to relate a generated registered endpoint edge to the
technology-neutral ownership model.  This is also the interface a custom
endpoint implementation must refine. -/
structure RegisteredTransfer (width : Nat) where
  sourceFires : Bool
  sinkFires : Bool
  sourceValid : Bool
  sourcePayload : BitVec width
  sinkPopPending : Bool
  channelEvent : Event width
  sourceReplacement : Option (BitVec width) := none
  sinkConsume : Bool := false
  deriving DecidableEq, Repr

def RegisteredTransfer.nextSource (transfer : RegisteredTransfer w)
    (result : Result w) : SourceStep w :=
  if transfer.sourceFires then
    sourceStep transfer.sourceValid transfer.sourcePayload result.accepted
      transfer.sourceReplacement
  else ⟨transfer.sourceValid, transfer.sourcePayload⟩

def RegisteredTransfer.nextSinkPop (transfer : RegisteredTransfer w) : Bool :=
  if transfer.sinkFires then transfer.sinkConsume else transfer.sinkPopPending

/-- The exact next logical ownership after one registered endpoint/channel
event. -/
def RegisteredTransfer.nextOwnership (transfer : RegisteredTransfer w)
    (c : Chan w) (queue : State w) : Ownership w :=
  let result := c.step queue transfer.channelEvent
  registeredOwnership result.state
    (transfer.nextSource result).valid (transfer.nextSource result).payload
    transfer.nextSinkPop

/-- A checked edge contract.  It connects the source request to the staged
payload and records the protocol premises generated by `withSource`/`withSink`.
The queue is explicit because one transfer record can be replayed from any
reachable channel state. -/
structure RegisteredTransfer.Valid (c : Chan w) (queue : State w)
    (transfer : RegisteredTransfer w) : Prop where
  pushMatches : transfer.channelEvent.push =
    (if transfer.sourceFires && transfer.sourceValid then
      some transfer.sourcePayload else none)
  acceptedLegal : (c.step queue transfer.channelEvent).accepted = true →
    transfer.sourceFires = true ∧ transfer.sourceValid = true
  replacementLegal : transfer.sourceReplacement.isSome = true →
    transfer.sourceFires = true ∧
      (transfer.sourceValid = false ∨
        (c.step queue transfer.channelEvent).accepted = true)
  replacementNoneUnticked : transfer.sourceFires = false →
    transfer.sourceReplacement = none
  pendingLegal : transfer.sinkPopPending = true → queue.isEmpty = false
  popMatches : transfer.channelEvent.pop =
    (transfer.sinkFires && transfer.sinkPopPending)
  consumeLegal : transfer.sinkConsume = true →
    transfer.sinkFires = true ∧ transfer.sinkPopPending = false ∧
      queue.isEmpty = false
  consumeNoneUnticked : transfer.sinkFires = false →
    transfer.sinkConsume = false

/-- End-to-end one-event ledger for the checked stock registered endpoints.
This is the schedule-local theorem used by reachable-state and trace lifting;
it is independent of clock ratios and of the selected CDC realization. -/
theorem registeredTransfer_conservation (c : Chan w) (queue : State w)
    (transfer : RegisteredTransfer w) (valid : transfer.Valid c queue) :
    OwnershipStep
      (registeredOwnership queue transfer.sourceValid transfer.sourcePayload
        transfer.sinkPopPending)
      transfer.sourceReplacement.toList
      (applicationConsumed queue transfer.sinkConsume)
      (let result := c.step queue transfer.channelEvent
       let source := transfer.nextSource result
       registeredOwnership result.state source.valid source.payload
         transfer.nextSinkPop) := by
  have sourceLedger :
      sourcePending transfer.sourceValid transfer.sourcePayload ++
          transfer.sourceReplacement.toList =
        (if (c.step queue transfer.channelEvent).accepted then
          sourcePending transfer.sourceValid transfer.sourcePayload else []) ++
        sourcePending (transfer.nextSource
          (c.step queue transfer.channelEvent)).valid
          (transfer.nextSource (c.step queue transfer.channelEvent)).payload := by
    cases fires : transfer.sourceFires
    · have replacementNone := valid.replacementNoneUnticked fires
      have pushNone : transfer.channelEvent.push = none := by
        rw [valid.pushMatches]
        simp [fires]
      have acceptedFalse :
          (c.step queue transfer.channelEvent).accepted = false := by
        cases eventDef : transfer.channelEvent with
        | mk push pop =>
            have pushEq := pushNone
            rw [eventDef] at pushEq
            change push = none at pushEq
            subst push
            exact c.step_no_push_accepted queue pop
      simp [RegisteredTransfer.nextSource, fires, replacementNone,
        acceptedFalse]
    · have ledger := sourceStep_conservation transfer.sourceValid
        transfer.sourcePayload (c.step queue transfer.channelEvent).accepted
        transfer.sourceReplacement
        (fun accepted => (valid.acceptedLegal accepted).2)
        (fun replacement => (valid.replacementLegal replacement).2)
      simpa [RegisteredTransfer.nextSource, fires] using ledger
  have sinkLedger := scheduledSink_conservation c queue
    transfer.channelEvent.push transfer.sinkPopPending transfer.sinkFires
    transfer.sinkConsume valid.pendingLegal valid.consumeLegal
    valid.consumeNoneUnticked
  have acceptedEq :
      (if (c.step queue transfer.channelEvent).accepted then
          sourcePending transfer.sourceValid transfer.sourcePayload else []) =
        c.acceptedValues queue transfer.channelEvent := by
    cases accepted : (c.step queue transfer.channelEvent).accepted
    · simp [acceptedValues, accepted]
    · have source := valid.acceptedLegal accepted
      unfold acceptedValues
      rw [accepted, valid.pushMatches]
      simp [sourcePending, source.1, source.2]
  have eventEq : transfer.channelEvent =
      { push := transfer.channelEvent.push,
        pop := transfer.sinkFires && transfer.sinkPopPending } := by
    cases eventDef : transfer.channelEvent with
    | mk push pop =>
        congr
        have popEq := valid.popMatches
        rw [eventDef] at popEq
        exact popEq
  have sinkLedger' :
      unreservedQueue queue transfer.sinkPopPending ++
          c.acceptedValues queue transfer.channelEvent =
        applicationConsumed queue transfer.sinkConsume ++
          unreservedQueue (c.step queue transfer.channelEvent).state
            transfer.nextSinkPop := by
    rw [eventEq]
    simpa [RegisteredTransfer.nextSinkPop] using sinkLedger
  unfold OwnershipStep Ownership.inventory registeredOwnership
  simp only [List.nil_append]
  calc
    (unreservedQueue queue transfer.sinkPopPending ++
        sourcePending transfer.sourceValid transfer.sourcePayload) ++
        transfer.sourceReplacement.toList =
      unreservedQueue queue transfer.sinkPopPending ++
        (sourcePending transfer.sourceValid transfer.sourcePayload ++
          transfer.sourceReplacement.toList) := by simp
    _ = unreservedQueue queue transfer.sinkPopPending ++
        ((if (c.step queue transfer.channelEvent).accepted then
            sourcePending transfer.sourceValid transfer.sourcePayload else []) ++
          sourcePending (transfer.nextSource
            (c.step queue transfer.channelEvent)).valid
            (transfer.nextSource (c.step queue transfer.channelEvent)).payload) := by
          rw [sourceLedger]
    _ = unreservedQueue queue transfer.sinkPopPending ++
        (c.acceptedValues queue transfer.channelEvent ++
          sourcePending (transfer.nextSource
            (c.step queue transfer.channelEvent)).valid
            (transfer.nextSource (c.step queue transfer.channelEvent)).payload) := by
          rw [acceptedEq]
    _ = (unreservedQueue queue transfer.sinkPopPending ++
          c.acceptedValues queue transfer.channelEvent) ++
        sourcePending (transfer.nextSource
          (c.step queue transfer.channelEvent)).valid
          (transfer.nextSource (c.step queue transfer.channelEvent)).payload := by simp
    _ = (applicationConsumed queue transfer.sinkConsume ++
          unreservedQueue (c.step queue transfer.channelEvent).state
            transfer.nextSinkPop) ++
        sourcePending (transfer.nextSource
          (c.step queue transfer.channelEvent)).valid
          (transfer.nextSource (c.step queue transfer.channelEvent)).payload := by
          rw [sinkLedger']
    _ = applicationConsumed queue transfer.sinkConsume ++
        (unreservedQueue (c.step queue transfer.channelEvent).state
            transfer.nextSinkPop ++
          sourcePending (transfer.nextSource
            (c.step queue transfer.channelEvent)).valid
            (transfer.nextSource (c.step queue transfer.channelEvent)).payload) := by simp

/-! ## Exact generated-endpoint cycle refinement -/

/-- Interpret a one-bit hardware coordinate as a protocol decision. -/
def bitAsserted (value : BitVec 1) : Bool := value = 1#1

theorem bitAsserted_eq_nonzero (value : BitVec 1) :
    bitAsserted value = (value != 0#1) := by
  have cases : value = 0#1 ∨ value = 1#1 := by bv_omega
  rcases cases with rfl | rfl <;> decide

/-- Semantic projection of the generated source staging registers. -/
def sourceView (c : Chan w) (state : St) : SourceStep w :=
  ⟨bitAsserted (state.regs c.sourceValidName 1),
    state.regs c.sourcePayloadName w⟩

/-- Semantic projection of the generated conservative sink request. -/
def sinkPopPending (c : Chan w) (state : St) : Bool :=
  bitAsserted (state.regs c.sinkPopName 1)

/-- Proof that one arbitrary application body respects the generated source
endpoint protocol.  It is indexed by the unadapted body, while the theorem
below is explicitly about the exact `withSource` result.  Pretty-authored
hardware can generate this certificate; expert `Design` authors may prove it
against their custom rules. -/
structure SourceEndpointCertificate (c : Chan w) (body : Design) where
  assume : InputAssumption
  replacement : InEnv → St → Option (BitVec w)
  refines : ∀ input state, assume state input →
    let driven := state.setInputs (c.withSource body).inputs input
    let accepted := bitAsserted (driven.regs c.sourceAcceptedName 1)
    sourceView c ((c.withSource body).cycleOpen input state) =
      sourceStep (sourceView c state).valid (sourceView c state).payload
        accepted (replacement input state)
  acceptedLegal : ∀ input state, assume state input →
    let driven := state.setInputs (c.withSource body).inputs input
    bitAsserted (driven.regs c.sourceAcceptedName 1) = true →
      (sourceView c state).valid = true
  replacementLegal : ∀ input state, assume state input →
    (replacement input state).isSome = true →
      let driven := state.setInputs (c.withSource body).inputs input
      (sourceView c state).valid = false ∨
        bitAsserted (driven.regs c.sourceAcceptedName 1) = true

/-- Generic checked `withSource` refinement.  The statement reaches the
actual `Design.cycleOpen` selected by the generated endpoint constructor. -/
theorem withSource_refines (c : Chan w) (body : Design)
    (certificate : SourceEndpointCertificate c body) (input : InEnv) (state : St)
    (accepted : certificate.assume state input) :
    let driven := state.setInputs (c.withSource body).inputs input
    let accepted := bitAsserted (driven.regs c.sourceAcceptedName 1)
    sourceView c ((c.withSource body).cycleOpen input state) =
      sourceStep (sourceView c state).valid (sourceView c state).payload
        accepted (certificate.replacement input state) :=
  certificate.refines input state accepted

/-- Proof that an arbitrary application body respects the generated
conservative sink endpoint.  `consume` records the single application-level
transfer intent; the fields prevent an unguarded consume or a re-consume while
an older acknowledgement is pending. -/
structure SinkEndpointCertificate (c : Chan w) (body : Design) where
  assume : InputAssumption
  consume : InEnv → St → Bool
  refines : ∀ input state, assume state input →
    sinkPopPending c ((c.withSink body).cycleOpen input state) = consume input state
  payloadPreserved : ∀ input state, assume state input →
    ((c.withSink body).cycleOpen input state).regs c.sinkPayloadName w =
      (state.setInputs (c.withSink body).inputs input).regs c.sinkPayloadName w
  consumeLegal : ∀ input state, assume state input →
    consume input state = true →
    sinkPopPending c state = false ∧
      let driven := state.setInputs (c.withSink body).inputs input
      bitAsserted (driven.regs c.sinkValidName 1) = true

/-- Generic checked `withSink` refinement of the exact generated Design. -/
theorem withSink_refines (c : Chan w) (body : Design)
    (certificate : SinkEndpointCertificate c body) (input : InEnv) (state : St)
    (accepted : certificate.assume state input) :
    sinkPopPending c ((c.withSink body).cycleOpen input state) =
      certificate.consume input state :=
  certificate.refines input state accepted

/-- A compositional endpoint pair.  Larger blocks can seal this beside their
trace theorem instead of exposing either island's generated maintenance rule. -/
structure RegisteredEndpointPair (c : Chan w) (sourceBody sinkBody : Design) where
  source : SourceEndpointCertificate c sourceBody
  sink : SinkEndpointCertificate c sinkBody

/-! ## Trace-level ownership -/

structure LedgerEvent (width : Nat) where
  accepted : List (BitVec width)
  consumed : List (BitVec width)
  after : Ownership width

def runLedger : Ownership w → List (LedgerEvent w) →
    List (BitVec w) × List (BitVec w) × Ownership w
  | initial, [] => ([], [], initial)
  | _, event :: rest =>
      let (laterAccepted, laterConsumed, final) := runLedger event.after rest
      (event.accepted ++ laterAccepted, event.consumed ++ laterConsumed, final)

/-- A trace whose adjacent events agree on the exact intermediate ownership.
This inductive presentation keeps the compositional premise local and avoids
index arithmetic in application proofs. -/
inductive ValidLedger : Ownership w → List (LedgerEvent w) → Prop
  | nil (initial : Ownership w) : ValidLedger initial []
  | cons {initial : Ownership w} {event : LedgerEvent w}
      {rest : List (LedgerEvent w)}
      (step : OwnershipStep initial event.accepted event.consumed event.after)
      (later : ValidLedger event.after rest) :
      ValidLedger initial (event :: rest)

/-- Per-edge ownership proofs compose into a whole-interface trace theorem.
This is the reusable protocol theorem for larger blocks and sealed systems. -/
theorem runLedger_conservation (initial : Ownership w)
    (events : List (LedgerEvent w))
    (valid : ValidLedger initial events) :
    let result := runLedger initial events
    initial.inventory ++ result.1 = result.2.1 ++ result.2.2.inventory := by
  induction valid with
  | nil => simp [runLedger]
  | cons first restValid ih =>
      rename_i initial event rest
      simp only [runLedger]
      dsimp only at ih ⊢
      unfold OwnershipStep at first
      calc
        initial.inventory ++ (event.accepted ++ (runLedger event.after rest).1) =
            (initial.inventory ++ event.accepted) ++
              (runLedger event.after rest).1 := by simp
        _ = (event.consumed ++ event.after.inventory) ++
              (runLedger event.after rest).1 := by rw [first]
        _ = event.consumed ++
              (event.after.inventory ++ (runLedger event.after rest).1) := by simp
        _ = event.consumed ++
              ((runLedger event.after rest).2.1 ++
                (runLedger event.after rest).2.2.inventory) := by rw [ih]
        _ = (event.consumed ++ (runLedger event.after rest).2.1) ++
              (runLedger event.after rest).2.2.inventory := by simp

end Chan

/-! ## Stable System proof handles -/

namespace System

/-- A checked reference to one exact System connection.  Application proofs
carry this value instead of generated names or `List.find?` equalities.  The
connection remains an index, so width, channel policy, and endpoint names
cannot drift between the declaration and a theorem invocation. -/
structure ConnectionHandle (sys : System) (connection : SystemConnection) : Prop where
  private mk ::
  found : sys.connections.find? (fun candidate =>
    candidate.chan.name == connection.chan.name) = some connection

/-- Expert/lowering constructor.  Pretty system declarations generate these
once; ordinary proofs consume the resulting handle through methods below. -/
def ConnectionHandle.ofFound (sys : System) (connection : SystemConnection)
    (found : sys.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection) :
    ConnectionHandle sys connection := ⟨found⟩

namespace ConnectionHandle

/-- Queue-capacity safety, quantified over every schedule admitted by the
System, without exposing connection lookup internals. -/
theorem capacity {sys : System} {connection : SystemConnection}
    (handle : ConnectionHandle sys connection) :
    sys.Invariant (atChannel connection fun queue =>
      queue.length ≤ connection.chan.depth) :=
  sys.channelCapacityInvariant connection handle.found

/-- Whole-run FIFO conservation through the stable connection handle. -/
theorem traceConservation {sys : System} {connection : SystemConnection}
    (handle : ConnectionHandle sys connection) (inputs : ExternalInputs)
    (initial : sys.State) (events : List NamedClockEvent) :
    let trace := sys.channelEventsFrom inputs connection initial events
    sys.channelState initial connection ++
        (connection.chan.runTrace (sys.channelState initial connection) trace).accepted =
      (connection.chan.runTrace (sys.channelState initial connection) trace).delivered ++
        sys.channelState (sys.runEventsFrom inputs initial events) connection :=
  sys.channelTraceConservation inputs connection handle.found initial events

end ConnectionHandle

/-- Additional invariant required of a conservative registered sink.  The
physical queue may still contain the acknowledged head, but it is reserved
and therefore excluded from `Chan.unreservedQueue`. -/
def RegisteredEndpointCoherent (sys : System) (connection : SystemConnection)
    (state : sys.State) : Prop :=
  let sink := state.island connection.sink
  let pending := sink.regs connection.chan.sinkPopName 1 = 1#1
  pending →
    (sys.channelState state connection).head? =
      some (sink.regs connection.chan.sinkPayloadName connection.width)

/-- A reusable induction certificate for endpoint protocol state.  Stock
endpoint constructors and custom endpoint libraries prove this once; larger
systems consume it without reopening generated rules or schedule semantics. -/
structure RegisteredEndpointCertificate (sys : System)
    (connection : SystemConnection) : Prop where
  reset : RegisteredEndpointCoherent sys connection sys.reset
  preserved : ∀ event external state,
    RegisteredEndpointCoherent sys connection state →
      RegisteredEndpointCoherent sys connection (sys.advance event external state)

/-! ### Compositional endpoint binding

The local endpoint certificates above intentionally expose their input
assumptions.  This System-level package is where assembly proves that the
generated channel wiring satisfies those assumptions.  Consequently an
island or sealed block can be verified once and then placed in any larger
System whose binding certificate is available. -/

/-- Exact connection of two locally certified endpoint-adapted Designs to a
checked named System. -/
structure RegisteredEndpointBinding (sys : System)
    (connection : SystemConnection) (sourceBody sinkBody : Design) where
  sourceIsland : SystemIsland
  sinkIsland : SystemIsland
  sourceFound : sys.findIsland? connection.source = some sourceIsland
  sinkFound : sys.findIsland? connection.sink = some sinkIsland
  connectionFound : sys.connections.find? (fun candidate =>
    candidate.chan.name == connection.chan.name) = some connection
  sourceDesign : sourceIsland.design = connection.chan.withSource sourceBody
  sinkDesign : sinkIsland.design = connection.chan.withSink sinkBody
  endpoints : Chan.RegisteredEndpointPair connection.chan sourceBody sinkBody
  sourceAssumption : ∀ event external state,
    endpoints.source.assume (state.island connection.source)
      (sys.islandInput event state external connection.source)
  sinkAssumption : ∀ event external state,
    endpoints.sink.assume (state.island connection.sink)
      (sys.islandInput event state external connection.sink)
  sinkPresentation : ∀ event external state,
    let input := sys.islandInput event state external connection.sink
    let driven := (state.island connection.sink).setInputs
      (connection.chan.withSink sinkBody).inputs input
    Chan.bitAsserted (driven.regs connection.chan.sinkValidName 1) =
        !(sys.channelState state connection).isEmpty ∧
      driven.regs connection.chan.sinkPayloadName connection.width =
        (sys.channelState state connection).head?.getD 0
  sourceAcknowledgement : ∀ event external state,
    let input := sys.islandInput event state external connection.source
    let driven := (state.island connection.source).setInputs
      (connection.chan.withSource sourceBody).inputs input
    Chan.bitAsserted (driven.regs connection.chan.sourceAcceptedName 1) =
      (sys.connectionResult event state connection).accepted
  resetCoherent : RegisteredEndpointCoherent sys connection sys.reset

namespace RegisteredEndpointBinding

/-- The schedule-local transfer record derived from the exact endpoint
Designs and named System event. Unticked endpoints contribute no application
transaction and retain their staged/request state. -/
def transfer {sys : System} {connection : SystemConnection}
    {sourceBody sinkBody : Design}
    (binding : RegisteredEndpointBinding sys connection sourceBody sinkBody)
    (event : NamedClockEvent) (external : String → InEnv) (state : sys.State) :
    Chan.RegisteredTransfer connection.width where
  sourceFires := event.fires binding.sourceIsland.clock
  sinkFires := event.fires binding.sinkIsland.clock
  sourceValid := (Chan.sourceView connection.chan
    (state.island connection.source)).valid
  sourcePayload := (Chan.sourceView connection.chan
    (state.island connection.source)).payload
  sinkPopPending := Chan.sinkPopPending connection.chan
    (state.island connection.sink)
  channelEvent := sys.connectionEvent event state connection
  sourceReplacement :=
    if event.fires binding.sourceIsland.clock then
      binding.endpoints.source.replacement
        (sys.islandInput event state external connection.source)
        (state.island connection.source)
    else none
  sinkConsume :=
    if event.fires binding.sinkIsland.clock then
      binding.endpoints.sink.consume
        (sys.islandInput event state external connection.sink)
        (state.island connection.sink)
    else false

/-- The derived record satisfies the abstract ledger protocol whenever the
reachable sink reservation is coherent.  This is the bridge that prevents
larger-System proofs from re-proving valid/ready details per channel. -/
theorem transfer_valid {sys : System} {connection : SystemConnection}
    {sourceBody sinkBody : Design}
    (binding : RegisteredEndpointBinding sys connection sourceBody sinkBody)
    (event : NamedClockEvent) (external : String → InEnv) (state : sys.State)
    (coherent : RegisteredEndpointCoherent sys connection state) :
    (binding.transfer event external state).Valid connection.chan
      (sys.channelState state connection) := by
  constructor
  · simp [transfer, System.connectionEvent, binding.sourceFound, Expr.eval,
      Chan.sourceView, Chan.sourceValid, Chan.sourcePayload,
      Chan.bitAsserted_eq_nonzero]
  · intro accepted
    have pushSome :
        (binding.transfer event external state).channelEvent.push.isSome = true := by
      cases pushEq : (binding.transfer event external state).channelEvent.push with
      | none =>
          simp [Chan.step, pushEq] at accepted
      | some payload => simp
    have pushMatchesEq :
        (binding.transfer event external state).channelEvent.push =
          (if (binding.transfer event external state).sourceFires &&
            (binding.transfer event external state).sourceValid then
            some (binding.transfer event external state).sourcePayload else none) := by
      simp [transfer, System.connectionEvent, binding.sourceFound, Expr.eval,
        Chan.sourceView, Chan.sourceValid, Chan.sourcePayload,
        Chan.bitAsserted_eq_nonzero]
    rw [pushMatchesEq] at pushSome
    cases sourceFires : (binding.transfer event external state).sourceFires <;>
      cases sourceValid : (binding.transfer event external state).sourceValid <;>
      simp [sourceFires, sourceValid] at pushSome ⊢
  · intro replacement
    change (if event.fires binding.sourceIsland.clock = true then
        binding.endpoints.source.replacement
          (sys.islandInput event state external connection.source)
          (state.island connection.source) else none).isSome = true at replacement
    change (event.fires binding.sourceIsland.clock = true ∧ _)
    split at replacement
    · rename_i fires
      have assumption := binding.sourceAssumption event external state
      have legal := binding.endpoints.source.replacementLegal _ _ assumption replacement
      refine ⟨fires, ?_⟩
      rcases legal with empty | acknowledged
      · exact Or.inl empty
      · right
        have acknowledgement := binding.sourceAcknowledgement event external state
        rw [acknowledgement] at acknowledged
        exact acknowledged
    · simp at replacement
  · intro unticked
    change event.fires binding.sourceIsland.clock = false at unticked
    change (if event.fires binding.sourceIsland.clock = true then _ else none) = none
    simp [unticked]
  · intro pending
    unfold transfer Chan.sinkPopPending Chan.bitAsserted at pending
    have pendingEq : (state.island connection.sink).regs
        connection.chan.sinkPopName 1 = 1#1 := by simpa using pending
    have head := coherent pendingEq
    cases queueEq : sys.channelState state connection with
    | nil => simp [queueEq] at head
    | cons first rest => simp
  · simp [transfer, System.connectionEvent, binding.sinkFound, Expr.eval,
      Chan.sinkPopPending, Chan.bitAsserted_eq_nonzero]
  · intro consumed
    change (if event.fires binding.sinkIsland.clock = true then
        binding.endpoints.sink.consume
          (sys.islandInput event state external connection.sink)
          (state.island connection.sink) else false) = true at consumed
    change event.fires binding.sinkIsland.clock = true ∧ _
    split at consumed
    · rename_i fires
      have assumption := binding.sinkAssumption event external state
      have legal := binding.endpoints.sink.consumeLegal _ _ assumption consumed
      refine ⟨fires, legal.1, ?_⟩
      have presentation := binding.sinkPresentation event external state
      have notEmpty : (!(sys.channelState state connection).isEmpty) = true :=
        presentation.1.symm.trans legal.2
      simpa using notEmpty
    · simp at consumed
  · intro unticked
    change event.fires binding.sinkIsland.clock = false at unticked
    change (if event.fires binding.sinkIsland.clock = true then _ else false) = false
    simp [unticked]

/-- One-call conservation theorem for an assembled endpoint pair.  Application
proofs supply only the reachable presentation-coherence fact; wiring, clock
gating, valid/ready legality, and the non-overlapping ownership convention are
discharged by the binding. -/
theorem transfer_conservation {sys : System} {connection : SystemConnection}
    {sourceBody sinkBody : Design}
    (binding : RegisteredEndpointBinding sys connection sourceBody sinkBody)
    (event : NamedClockEvent) (external : String → InEnv) (state : sys.State)
    (coherent : RegisteredEndpointCoherent sys connection state) :
    let transfer := binding.transfer event external state
    Chan.OwnershipStep
      (Chan.registeredOwnership (sys.channelState state connection)
        transfer.sourceValid transfer.sourcePayload transfer.sinkPopPending)
      transfer.sourceReplacement.toList
      (Chan.applicationConsumed (sys.channelState state connection)
        transfer.sinkConsume)
      (transfer.nextOwnership connection.chan
        (sys.channelState state connection)) := by
  dsimp only
  exact Chan.registeredTransfer_conservation connection.chan
    (sys.channelState state connection) (binding.transfer event external state)
    (binding.transfer_valid event external state coherent)

/-- A source-island edge in the composed System refines the registered source
step selected by the local certificate. -/
theorem sourceCycle {sys : System} {connection : SystemConnection}
    {sourceBody sinkBody : Design}
    (binding : RegisteredEndpointBinding sys connection sourceBody sinkBody)
    (event : NamedClockEvent) (external : String → InEnv) (state : sys.State) :
    let input := sys.islandInput event state external connection.source
    let before := state.island connection.source
    let driven := before.setInputs
      (connection.chan.withSource sourceBody).inputs input
    let accepted := Chan.bitAsserted
      (driven.regs connection.chan.sourceAcceptedName 1)
    Chan.sourceView connection.chan
        ((connection.chan.withSource sourceBody).cycleOpen input before) =
      Chan.sourceStep
        (Chan.sourceView connection.chan before).valid
        (Chan.sourceView connection.chan before).payload accepted
        (binding.endpoints.source.replacement input before) := by
  exact connection.chan.withSource_refines sourceBody binding.endpoints.source
    _ _ (binding.sourceAssumption event external state)

/-- The corresponding conservative sink edge refinement. -/
theorem sinkCycle {sys : System} {connection : SystemConnection}
    {sourceBody sinkBody : Design}
    (binding : RegisteredEndpointBinding sys connection sourceBody sinkBody)
    (event : NamedClockEvent) (external : String → InEnv) (state : sys.State) :
    let input := sys.islandInput event state external connection.sink
    let before := state.island connection.sink
    Chan.sinkPopPending connection.chan
        ((connection.chan.withSink sinkBody).cycleOpen input before) =
      binding.endpoints.sink.consume input before := by
  exact connection.chan.withSink_refines sinkBody binding.endpoints.sink
    _ _ (binding.sinkAssumption event external state)

/-- The checked local endpoint refinements and exact System wiring induce the
reachable conservative-sink coherence certificate automatically. -/
def toEndpointCertificate {sys : System} {connection : SystemConnection}
    {sourceBody sinkBody : Design}
    (binding : RegisteredEndpointBinding sys connection sourceBody sinkBody) :
    RegisteredEndpointCertificate sys connection where
  reset := binding.resetCoherent
  preserved := by
    intro event external state coherent
    unfold RegisteredEndpointCoherent at coherent ⊢
    dsimp only
    intro nextPending
    have sinkName : binding.sinkIsland.name = connection.sink :=
      System.findIsland?_name binding.sinkFound
    by_cases ticked : event.fires binding.sinkIsland.clock = true
    · have sinkAdvance := sys.advance_island_ticked event external state
          binding.sinkIsland (by simpa [sinkName] using binding.sinkFound) ticked
      have sinkNext :
          (sys.advance event external state).island connection.sink =
            (connection.chan.withSink sinkBody).cycleOpen
              (sys.islandInput event state external connection.sink)
              (state.island connection.sink) := by
        simpa [sinkName, binding.sinkDesign] using sinkAdvance
      have assumption := binding.sinkAssumption event external state
      have cycleRefines := binding.sinkCycle event external state
      have pendingTrue :
          Chan.sinkPopPending connection.chan
            ((connection.chan.withSink sinkBody).cycleOpen
              (sys.islandInput event state external connection.sink)
              (state.island connection.sink)) = true := by
        unfold Chan.sinkPopPending Chan.bitAsserted
        rw [← sinkNext]
        simp [nextPending]
      have consumeTrue : binding.endpoints.sink.consume
          (sys.islandInput event state external connection.sink)
          (state.island connection.sink) = true := by
        rw [← cycleRefines]
        exact pendingTrue
      have legal := binding.endpoints.sink.consumeLegal _ _ assumption consumeTrue
      have oldPending :
          (state.island connection.sink).regs
            connection.chan.sinkPopName 1 = 0#1 := by
        unfold Chan.sinkPopPending Chan.bitAsserted at legal
        have bitCases :
            (state.island connection.sink).regs
                connection.chan.sinkPopName 1 = 0#1 ∨
              (state.island connection.sink).regs
                connection.chan.sinkPopName 1 = 1#1 := by
          bv_omega
        rcases bitCases with zero | one
        · exact zero
        · simp [one] at legal
      have presentation := binding.sinkPresentation event external state
      have notEmpty : (!(sys.channelState state connection).isEmpty) = true :=
        presentation.1.symm.trans legal.2
      have queueNonempty : (sys.channelState state connection).isEmpty = false := by
        simpa using notEmpty
      have eventPop : (sys.connectionEvent event state connection).pop = false := by
        unfold System.connectionEvent
        simp [binding.sinkFound, ticked, Expr.eval, oldPending]
      have eventEq : sys.connectionEvent event state connection =
          { push := (sys.connectionEvent event state connection).push,
            pop := false } := by
        cases eventDef : sys.connectionEvent event state connection with
        | mk push pop =>
            congr
            have popEq := eventPop
            rw [eventDef] at popEq
            exact popEq
      let sinkPayload :=
        ((state.island connection.sink).setInputs
          (connection.chan.withSink sinkBody).inputs
          (sys.islandInput event state external connection.sink)).regs
            connection.chan.sinkPayloadName connection.width
      have oldHead :
          (sys.channelState state connection).head? =
            some sinkPayload := by
        cases queueDef : sys.channelState state connection with
        | nil => simp [queueDef] at queueNonempty
        | cons head tail =>
            have payloadEq := presentation.2
            rw [queueDef] at payloadEq
            simpa [sinkPayload] using payloadEq.symm
      have nextHead := connection.chan.step_head_of_no_pop
        (sys.channelState state connection)
        (sys.connectionEvent event state connection).push
        sinkPayload oldHead
      have payloadPreserved := binding.endpoints.sink.payloadPreserved _ _ assumption
      rw [sys.channelState_advance event external state connection
        binding.connectionFound]
      unfold System.connectionResult
      rw [eventEq]
      change (connection.chan.step (sys.channelState state connection)
        { push := (sys.connectionEvent event state connection).push,
          pop := false }).state.head? = _
      rw [sinkNext, payloadPreserved]
      exact nextHead
    · have unticked : event.fires binding.sinkIsland.clock = false := by
        simpa using ticked
      have sinkAdvance := sys.advance_island_unticked event external state
        binding.sinkIsland (by simpa [sinkName] using binding.sinkFound) unticked
      have sinkSame :
          (sys.advance event external state).island connection.sink =
            state.island connection.sink := by
        simpa [sinkName] using sinkAdvance
      have eventPop : (sys.connectionEvent event state connection).pop = false := by
        unfold System.connectionEvent
        simp [binding.sinkFound, unticked]
      have eventEq : sys.connectionEvent event state connection =
          { push := (sys.connectionEvent event state connection).push,
            pop := false } := by
        cases eventDef : sys.connectionEvent event state connection with
        | mk push pop =>
            congr
            have popEq := eventPop
            rw [eventDef] at popEq
            exact popEq
      have oldPendingEq :
          (state.island connection.sink).regs
            connection.chan.sinkPopName 1 = 1#1 := by
        rw [← sinkSame]
        exact nextPending
      have oldHead := coherent oldPendingEq
      have nextHead := connection.chan.step_head_of_no_pop
        (sys.channelState state connection)
        (sys.connectionEvent event state connection).push
        ((state.island connection.sink).regs
          connection.chan.sinkPayloadName connection.width) oldHead
      rw [sys.channelState_advance event external state connection
        binding.connectionFound]
      unfold System.connectionResult
      rw [eventEq]
      change (connection.chan.step (sys.channelState state connection)
        { push := (sys.connectionEvent event state connection).push,
          pop := false }).state.head? = _
      rw [sinkSame]
      exact nextHead

end RegisteredEndpointBinding

/-- Endpoint presentation facts exposed to interface proofs.  These are about
the actual values supplied to an island at an event, not merely the abstract
queue in isolation. -/
structure PresentationCoherent (sys : System) (connection : SystemConnection)
    (state : sys.State) : Prop where
  bounded : (sys.channelState state connection).length ≤ connection.chan.depth
  sinkValid : ∀ event,
    (sys.resolveConnection event state connection).sinkValid =
      !(sys.channelState state connection).isEmpty
  sinkPayload : ∀ event,
    (sys.resolveConnection event state connection).sinkPayload =
      (sys.channelState state connection).head?.getD 0
  channelStep : ∀ event,
    (sys.resolveConnection event state connection).result =
      connection.chan.step (sys.channelState state connection)
        (sys.resolveConnection event state connection).request

/-- Capacity and generated endpoint presentation are supplied together for
every reachable state.  The schedule induction is internal to Loom. -/
theorem ConnectionHandle.safety {sys : System} {connection : SystemConnection}
    (handle : ConnectionHandle sys connection) :
    sys.Invariant (PresentationCoherent sys connection) := by
  intro schedule inputs admitted state reachable
  have bounded := handle.capacity schedule inputs admitted state reachable
  exact ⟨bounded, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Reachable-state induction automatically supplies registered endpoint
coherence under every admitted schedule. -/
theorem RegisteredEndpointCertificate.invariant {sys : System}
    {connection : SystemConnection}
    (certificate : RegisteredEndpointCertificate sys connection) :
    sys.Invariant (RegisteredEndpointCoherent sys connection) := by
  intro schedule inputs _ state reachable
  induction reachable with
  | init initial =>
      rw [← initial]
      exact certificate.reset
  | step _ stepEq ih =>
      rename_i before after _
      rw [stepEq]
      exact certificate.preserved (schedule before.time) (inputs before.time) before ih

/-- The complete reusable safety surface for a registered connection. -/
structure RegisteredChannelSafety (sys : System)
    (connection : SystemConnection) (state : sys.State) : Prop where
  presentation : PresentationCoherent sys connection state
  endpoint : RegisteredEndpointCoherent sys connection state

theorem ConnectionHandle.registeredSafety {sys : System}
    {connection : SystemConnection}
    (handle : ConnectionHandle sys connection)
    (endpoint : RegisteredEndpointCertificate sys connection) :
    sys.Invariant (RegisteredChannelSafety sys connection) := by
  intro schedule inputs admitted state reachable
  exact ⟨handle.safety schedule inputs admitted state reachable,
    endpoint.invariant schedule inputs admitted state reachable⟩

/-- One-call safety theorem for a connection whose local endpoints and System
wiring have been compositionally certified. -/
theorem ConnectionHandle.boundRegisteredSafety {sys : System}
    {connection : SystemConnection} {sourceBody sinkBody : Design}
    (handle : ConnectionHandle sys connection)
    (binding : RegisteredEndpointBinding sys connection sourceBody sinkBody) :
    sys.Invariant (RegisteredChannelSafety sys connection) :=
  handle.registeredSafety binding.toEndpointCertificate

/-! ## Whole-System interface protocol bundles -/

/-- A stable theorem bundle for one externally meaningful System interface.
The observations may project application transactions, packed messages, or a
more abstract protocol trace.  Internal islands, generated coordinates, and
channel placement do not appear in the contract. -/
structure InterfaceProof (sys : System) (input output : Type) where
  safety : sys.State → Prop
  safetyInvariant : sys.Invariant safety
  contract : TraceContract input output
  observeInput : ExternalInputs → sys.State → List NamedClockEvent → List input
  observeOutput : ExternalInputs → sys.State → List NamedClockEvent → List output
  holds : ∀ inputs initial events,
    contract (observeInput inputs initial events)
      (observeOutput inputs initial events)

namespace InterfaceProof

/-- Compose two protocol interfaces in the same assembled System.  The sole
glue obligation states that both bundles observe the same intermediate
transaction sequence; the result hides that sequence behind relational
`TraceContract.comp`. -/
def comp {sys : System} {input middle output : Type}
    (first : InterfaceProof sys input middle)
    (second : InterfaceProof sys middle output)
    (interfaceEq : ∀ inputs initial events,
      first.observeOutput inputs initial events =
        second.observeInput inputs initial events) :
    InterfaceProof sys input output where
  safety := fun state => first.safety state ∧ second.safety state
  safetyInvariant := sys.invariantAnd first.safetyInvariant second.safetyInvariant
  contract := TraceContract.comp first.contract second.contract
  observeInput := first.observeInput
  observeOutput := second.observeOutput
  holds := by
    intro inputs initial events
    refine ⟨first.observeOutput inputs initial events,
      first.holds inputs initial events, ?_⟩
    rw [interfaceEq]
    exact second.holds inputs initial events

/-- Strengthen a reusable interface with an independently proved System
safety invariant without changing its trace observations or contract. -/
def andSafety {sys : System} {input output : Type}
    (interface : InterfaceProof sys input output)
    (property : sys.State → Prop) (invariant : sys.Invariant property) :
    InterfaceProof sys input output where
  safety := fun state => interface.safety state ∧ property state
  safetyInvariant := sys.invariantAnd interface.safetyInvariant invariant
  contract := interface.contract
  observeInput := interface.observeInput
  observeOutput := interface.observeOutput
  holds := interface.holds

end InterfaceProof

end System

/-! ## Bounded compositional progress contracts -/

namespace TraceContract

/-- A bounded service interface.  The unit is deliberately explicit: it may
be destination ticks, arbitration grants, or protocol rounds, but two stages
compose only when they use the same service index. -/
structure BoundedService where
  unit : String
  accepted : CountTrace
  delivered : CountTrace
  bound : Nat
  deliveredMonotone : ∀ first second, first ≤ second →
    delivered first ≤ delivered second
  guarantee : deliveredWithin bound accepted delivered

namespace BoundedService

/-- Serial composition adds bounds and hides the intermediate trace. -/
def comp (first second : BoundedService)
    (_sameUnit : first.unit = second.unit)
    (interfaceEq : first.delivered = second.accepted) : BoundedService where
  unit := first.unit
  accepted := first.accepted
  delivered := second.delivered
  bound := first.bound + second.bound
  deliveredMonotone := second.deliveredMonotone
  guarantee := by
    have secondGuarantee :
        deliveredWithin second.bound first.delivered second.delivered := by
      rw [interfaceEq]
      exact second.guarantee
    exact deliveredWithin_comp first.guarantee secondGuarantee

/-- A proved service contract can advertise a weaker bound without changing
the component or its traces. -/
def weaken (service : BoundedService) (bound : Nat)
    (weaker : service.bound ≤ bound) : BoundedService where
  unit := service.unit
  accepted := service.accepted
  delivered := service.delivered
  bound := bound
  deliveredMonotone := service.deliveredMonotone
  guarantee := deliveredWithin_mono service.deliveredMonotone
    service.guarantee weaker

/-- Parallel independent services share a service unit and complete within
the maximum of their bounds.  Counts are added because the two interfaces are
disjoint; arbitration belongs in an explicit component contract instead. -/
def parallel (left right : BoundedService)
    (sameUnit : left.unit = right.unit) : BoundedService where
  unit := left.unit
  accepted := fun time => left.accepted time + right.accepted time
  delivered := fun time => left.delivered time + right.delivered time
  bound := max left.bound right.bound
  deliveredMonotone := by
    have _unitsAgree := sameUnit
    intro first second le
    exact Nat.add_le_add (left.deliveredMonotone first second le)
      (right.deliveredMonotone first second le)
  guarantee := by
    intro time
    apply Nat.add_le_add
    · exact deliveredWithin_mono left.deliveredMonotone left.guarantee
        (Nat.le_max_left _ _) time
    · exact deliveredWithin_mono right.deliveredMonotone right.guarantee
        (Nat.le_max_right _ _) time

end BoundedService

end TraceContract

end Loom.Hw
