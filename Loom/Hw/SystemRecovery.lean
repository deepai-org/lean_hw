-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.System
import Loom.Hw.ChanRecovery

/-!
# Explicit independent-reset recovery semantics

The ordinary `NamedClockEvent` remains the small reset-free schedule object.
This module adds an executable event carrying a named set of islands whose
reset is asserted for that event. A `coordinated` System rejects every such
live reset. An `independentFlush` System gives it one precise meaning:

* reset dominates a simultaneous tick of the named island;
* every incident channel is empty after the event;
* queued and same-event traffic on an incident channel is discarded; and
* nonincident islands and channels take the ordinary `System.advance` step.

This is intentionally a loss-explicit recovery contract. It does not claim
that pre-reset traffic is preserved, replayed, or acknowledged. Physical
realizations must carry a recovery refinement before exposing independent
reset ports; the stock recovery realization is assembled separately by the
multiclock application layer.
-/

namespace Loom.Hw
namespace System

/-- One schedule event plus independently asserted island resets. The lists
are executable/replayable data, not proof-only predicates. -/
structure RecoveryEvent where
  tick : NamedClockEvent
  resetIslands : List String := []
  deriving DecidableEq, Repr

def RecoveryEvent.resets (event : RecoveryEvent) (island : String) : Bool :=
  event.resetIslands.contains island

def RecoveryEvent.affects (event : RecoveryEvent)
    (connection : SystemConnection) : Bool :=
  event.resets connection.source || event.resets connection.sink

/-- A live-reset event is legal only under the explicit flush policy, names
existing islands exactly once. Coordinated Systems accept reset-free events
and reject every live reset. -/
def recoveryEventOk (system : System) (event : RecoveryEvent) : Bool :=
  event.resetIslands.eraseDups.length == event.resetIslands.length &&
    event.resetIslands.all (fun name => (system.findIsland? name).isSome) &&
    match system.resetPolicy with
    | .coordinated => event.resetIslands.isEmpty
    | .independentFlush => true

private def emptyPackedQueue (connection : SystemConnection) : PackedQueue :=
  ⟨connection.width, []⟩

/-- Assert the named island resets and flush their incident abstract queues,
without advancing time. This intermediate state is also what unaffected
islands observe when they tick in the same recovery event. -/
def applyRecovery (system : System) (event : RecoveryEvent)
    (state : system.State) : system.State where
  island := fun name =>
    if event.resets name then
      match system.findIsland? name with
      | some island => island.design.reset
      | none => state.island name
    else state.island name
  channel := fun name =>
    match system.connections.find? (fun connection =>
        connection.chan.name == name) with
    | some connection =>
        if event.affects connection then emptyPackedQueue connection
        else state.channel name
    | none => state.channel name
  time := state.time

/-- Reset-dominant combined transition. An unaffected island/channel takes
the ordinary tick step from the already-flushed intermediate state. A reset
island and every incident channel are then held in reset/empty state for the
whole event. -/
def advanceRecovery (system : System) (event : RecoveryEvent)
    (external : String → InEnv) (state : system.State) : system.State :=
  let recovered := system.applyRecovery event state
  let advanced := system.advance event.tick external recovered
  { island := fun name =>
      if event.resets name then recovered.island name else advanced.island name
    channel := fun name =>
      match system.connections.find? (fun connection =>
          connection.chan.name == name) with
      | some connection =>
          if event.affects connection then emptyPackedQueue connection
          else advanced.channel name
      | none => advanced.channel name
    time := advanced.time }

/-- The per-connection observation of a System recovery event.  An affected
connection sees the loss-explicit channel flush; an unaffected connection
takes its ordinary transfer step from the recovered intermediate state. -/
def recoveryChannelEvent (system : System) (event : RecoveryEvent)
    (state : system.State)
    (connection : SystemConnection) : Chan.RecoveryEvent connection.width :=
  if event.affects connection then .flush else
    .transfer (system.connectionEvent event.tick
      (system.applyRecovery event state) connection)

def runRecoveryEventsFrom (system : System) (inputs : ExternalInputs) :
    system.State → List RecoveryEvent → system.State
  | state, [] => state
  | state, event :: rest =>
      system.runRecoveryEventsFrom inputs
        (system.advanceRecovery event (inputs state.time) state) rest

abbrev RecoverySchedulePrefix := Array RecoveryEvent

def runRecoveryPrefix (system : System) (events : RecoverySchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) : system.State :=
  system.runRecoveryEventsFrom inputs system.reset events.toList

/-- Fail closed on both the existing clock relation and the selected reset
contract. The rejected event remains printable/replayable. -/
def runRecoveryPrefixChecked (system : System) (events : RecoverySchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) : Except String system.State := do
  if !events.all (system.recoveryEventOk ·) then
    throw "recovery schedule violates SystemResetPolicy or names an invalid island"
  let ticks := events.map (·.tick)
  if !system.clockRel.accepts ticks then
    throw "recovery schedule tick projection rejected by ClockRel"
  pure (system.runRecoveryPrefix events inputs)

@[simp] theorem applyRecovery_time (system : System) (event : RecoveryEvent)
    (state : system.State) :
    (system.applyRecovery event state).time = state.time := rfl

@[simp] theorem advanceRecovery_time (system : System) (event : RecoveryEvent)
    (external : String → InEnv) (state : system.State) :
    (system.advanceRecovery event external state).time = state.time + 1 := rfl

theorem applyRecovery_island_reset (system : System) (event : RecoveryEvent)
    (state : system.State) (island : SystemIsland)
    (found : system.findIsland? island.name = some island)
    (reset : event.resets island.name = true) :
    (system.applyRecovery event state).island island.name = island.design.reset := by
  simp [applyRecovery, reset, found]

theorem advanceRecovery_island_reset (system : System) (event : RecoveryEvent)
    (external : String → InEnv) (state : system.State) (island : SystemIsland)
    (found : system.findIsland? island.name = some island)
    (reset : event.resets island.name = true) :
    (system.advanceRecovery event external state).island island.name =
      island.design.reset := by
  simp [advanceRecovery, reset, system.applyRecovery_island_reset event state island found reset]

theorem applyRecovery_channel_flush (system : System) (event : RecoveryEvent)
    (state : system.State) (connection : SystemConnection)
    (found : system.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection)
    (affected : event.affects connection = true) :
    system.channelState (system.applyRecovery event state) connection = [] := by
  unfold channelState connectionQueue applyRecovery
  change (match system.connections.find? (fun (candidate : SystemConnection) =>
      candidate.chan.name == connection.chan.name) with
    | some candidate =>
        if event.affects candidate then emptyPackedQueue candidate
        else state.channel connection.chan.name
    | none => state.channel connection.chan.name).asWidth connection.width = []
  rw [found]
  simp only
  rw [if_pos affected]
  simp [PackedQueue.asWidth, emptyPackedQueue]

theorem advanceRecovery_channel_flush (system : System) (event : RecoveryEvent)
    (external : String → InEnv) (state : system.State)
    (connection : SystemConnection)
    (found : system.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection)
    (affected : event.affects connection = true) :
    system.channelState (system.advanceRecovery event external state) connection = [] := by
  unfold channelState connectionQueue advanceRecovery
  change (match system.connections.find? (fun (candidate : SystemConnection) =>
      candidate.chan.name == connection.chan.name) with
    | some candidate =>
        if event.affects candidate then emptyPackedQueue candidate
        else (system.advance event.tick external
          (system.applyRecovery event state)).channel connection.chan.name
    | none => (system.advance event.tick external
        (system.applyRecovery event state)).channel connection.chan.name).asWidth
          connection.width = []
  rw [found]
  simp only
  rw [if_pos affected]
  simp [PackedQueue.asWidth, emptyPackedQueue]

theorem applyRecovery_channel_unaffected (system : System) (event : RecoveryEvent)
    (state : system.State) (connection : SystemConnection)
    (found : system.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection)
    (unaffected : event.affects connection = false) :
    system.channelState (system.applyRecovery event state) connection =
      system.channelState state connection := by
  unfold channelState connectionQueue applyRecovery
  change (match system.connections.find? (fun (candidate : SystemConnection) =>
      candidate.chan.name == connection.chan.name) with
    | some candidate =>
        if event.affects candidate then emptyPackedQueue candidate
        else state.channel connection.chan.name
    | none => state.channel connection.chan.name).asWidth connection.width =
      (state.channel connection.chan.name).asWidth connection.width
  rw [found]
  simp [unaffected]

theorem advanceRecovery_channel_unaffected (system : System)
    (event : RecoveryEvent) (external : String → InEnv) (state : system.State)
    (connection : SystemConnection)
    (found : system.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection)
    (unaffected : event.affects connection = false) :
    system.channelState (system.advanceRecovery event external state) connection =
      system.channelState
        (system.advance event.tick external (system.applyRecovery event state))
        connection := by
  unfold channelState connectionQueue advanceRecovery
  change (match system.connections.find? (fun (candidate : SystemConnection) =>
      candidate.chan.name == connection.chan.name) with
    | some candidate =>
        if event.affects candidate then emptyPackedQueue candidate
        else (system.advance event.tick external
          (system.applyRecovery event state)).channel connection.chan.name
    | none => (system.advance event.tick external
        (system.applyRecovery event state)).channel connection.chan.name).asWidth
          connection.width = _
  rw [found]
  simp [unaffected]

/-- The System transition uses exactly the generic loss-explicit channel
recovery semantics.  This is the semantic handoff target for a distributed
quiesce/acknowledgement implementation: its completion event must refine this
step, rather than merely resetting some emitted registers. -/
theorem channelState_advanceRecovery_eq_recoveryStep (system : System)
    (event : RecoveryEvent) (external : String → InEnv) (state : system.State)
    (connection : SystemConnection)
    (found : system.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection) :
    system.channelState (system.advanceRecovery event external state) connection =
      (connection.chan.recoveryStep (system.channelState state connection)
        (system.recoveryChannelEvent event state connection)).state := by
  cases affected : event.affects connection with
  | true =>
      rw [system.advanceRecovery_channel_flush event external state connection
        found affected]
      simp [recoveryChannelEvent, affected, Chan.recoveryStep]
  | false =>
      rw [system.advanceRecovery_channel_unaffected event external state connection
        found affected]
      rw [channelState_advance system event.tick external
        (system.applyRecovery event state) connection found]
      simp only [connectionResult]
      have queueEq :
          connectionQueue (system.applyRecovery event state) connection =
            connectionQueue state connection := by
        simpa [channelState] using
          system.applyRecovery_channel_unaffected event state connection found affected
      rw [queueEq]
      simp [recoveryChannelEvent, affected, Chan.recoveryStep]
      rfl

/-- Schedule-free induction package for reset-aware safety properties. Its
preservation hypothesis sees the validity proof, so coordinated-only and
independent-reset theorems cannot be conflated. -/
structure RecoveryInvariant (system : System)
    (property : system.State → Prop) where
  reset : property system.reset
  preserved : ∀ event external state, system.recoveryEventOk event = true →
    property state → property (system.advanceRecovery event external state)

theorem RecoveryInvariant.run {system : System} {property : system.State → Prop}
    (certificate : RecoveryInvariant system property) (inputs : ExternalInputs)
    (state : system.State) (events : List RecoveryEvent)
    (initial : property state)
    (valid : ∀ event ∈ events, system.recoveryEventOk event = true) :
    property (system.runRecoveryEventsFrom inputs state events) := by
  induction events generalizing state with
  | nil => exact initial
  | cons event rest ih =>
      apply ih (system.advanceRecovery event (inputs state.time) state)
      · exact certificate.preserved event (inputs state.time) state
          (valid event (by simp)) initial
      · intro later member
        exact valid later (by simp [member])

/-- Queue capacity survives every legal independent-reset trace. Resetting an
endpoint establishes the bound by flushing; a nonincident event reduces to
the ordinary proved `Chan.noOverflow` transition. -/
def channelCapacityRecoveryInvariant (system : System)
    (connection : SystemConnection)
    (found : system.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection) :
    RecoveryInvariant system
      (atChannel connection fun queue => queue.length ≤ connection.chan.depth) where
  reset := by
    simp only [atChannel]
    rw [channelState_reset system connection found]
    simp
  preserved := by
    intro event external state _ bounded
    simp only [atChannel] at bounded ⊢
    cases affected : event.affects connection with
    | true =>
        rw [system.advanceRecovery_channel_flush event external state connection
          found affected]
        simp
    | false =>
        rw [system.advanceRecovery_channel_unaffected event external state
          connection found affected]
        rw [channelState_advance system event.tick external
          (system.applyRecovery event state) connection found]
        apply connection.chan.noOverflow
        change (system.channelState (system.applyRecovery event state)
          connection).length ≤ connection.chan.depth
        rw [system.applyRecovery_channel_unaffected event state connection
          found affected]
        exact bounded

end System
end Loom.Hw
