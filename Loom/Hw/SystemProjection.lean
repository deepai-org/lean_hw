-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Multiclock

/-!
# Compositional multiclock execution projection

A fragment-wide theorem is reusable only when parent execution genuinely
simulates fragment execution.  This module makes that boundary explicit.  A
projection covers state, clock/reset events, and the input valuation observed
at every step; its one-step simulation law is then lifted to arbitrary finite
reset-aware executions by kernel-checked induction.

The structural Boolean is diagnostic evidence, not the semantic proof.  The
`ExecutionProjection` fields are the refinement certificate.  In particular,
clock and reset compatibility are used to prove that a valid parent trace
projects to a valid child trace; unlike island-local invariant lifting, they
are not decorative premises.
-/

namespace Loom.Hw
universe u
namespace System

@[ext] theorem State.ext {system : System} {left right : system.State}
    (island : left.island = right.island)
    (channel : left.channel = right.channel)
    (time : left.time = right.time) : left = right := by
  cases left
  cases right
  simp_all

/-- One replay step with the exact external input valuation used for that
step.  Keeping the valuation beside the reset/clock event permits a projected
fragment input to depend on the pre-step parent state (as a closed exported
endpoint necessarily does). -/
structure ObservedRecoveryEvent where
  event : RecoveryEvent
  external : String → InEnv

/-- Execute an observation-rich reset-aware trace from an explicit state. -/
def runObservedFrom (system : System) :
    system.State → List ObservedRecoveryEvent → system.State
  | state, [] => state
  | state, step :: rest =>
      system.runObservedFrom
        (system.advanceRecovery step.event step.external state) rest

def runObserved (system : System) (steps : List ObservedRecoveryEvent) :
    system.State :=
  system.runObservedFrom system.reset steps

def observedEvents (steps : List ObservedRecoveryEvent) : List RecoveryEvent :=
  steps.map (·.event)

/-- The typed channel requests observed along the same reset-aware execution.
This is the ledger projection used by fragment-wide FIFO-order and no-loss
theorems; it is derived from pre-step System states, not reconstructed from
the final queue. -/
def observedChannelEventsFrom (system : System)
    (connection : SystemConnection) :
    system.State → List ObservedRecoveryEvent →
      List (Chan.Event connection.width)
  | _, [] => []
  | state, observed :: rest =>
      system.connectionEvent observed.event.tick state connection ::
        system.observedChannelEventsFrom connection
          (system.advanceRecovery observed.event observed.external state) rest

theorem applyRecovery_noReset (system : System) (event : RecoveryEvent)
    (state : system.State) (none : event.resetIslands = []) :
    system.applyRecovery event state = state := by
  cases event with
  | mk tick resetIslands =>
      simp only at none
      subst resetIslands
      cases state
      simp only [applyRecovery, RecoveryEvent.affects,
        RecoveryEvent.resets, List.contains_nil, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte]
      congr 1
      funext name
      split <;> rfl

theorem advanceRecovery_noReset (system : System) (event : RecoveryEvent)
    (external : String → InEnv) (state : system.State)
    (none : event.resetIslands = []) :
    system.advanceRecovery event external state =
      system.advance event.tick external state := by
  cases event with
  | mk tick resetIslands =>
      simp only at none
      subst resetIslands
      unfold advanceRecovery
      rw [system.applyRecovery_noReset ⟨tick, []⟩ state rfl]
      simp only [RecoveryEvent.affects, RecoveryEvent.resets,
        List.contains_nil, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      congr 1
      funext name
      split <;> rfl

theorem recoveryEventOk_coordinated_noReset (system : System)
    (event : RecoveryEvent) (policy : system.resetPolicy = .coordinated)
    (valid : system.recoveryEventOk event = true) :
    event.resetIslands = [] := by
  unfold recoveryEventOk at valid
  rw [policy] at valid
  simp only [Bool.and_eq_true, List.isEmpty_iff] at valid
  exact valid.2

/-- A coordinated reset-aware execution projects exactly to the ordinary
abstract queue trace for every declared channel. -/
theorem channelState_runObservedFrom (system : System)
    (connection : SystemConnection)
    (found : system.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection)
    (initial : system.State) (steps : List ObservedRecoveryEvent)
    (noReset : ∀ observed ∈ steps, observed.event.resetIslands = []) :
    system.channelState (system.runObservedFrom initial steps) connection =
      (connection.chan.runTrace (system.channelState initial connection)
        (system.observedChannelEventsFrom connection initial steps)).state := by
  induction steps generalizing initial with
  | nil => rfl
  | cons observed rest ih =>
      have headNone := noReset observed (by simp)
      have restNone : ∀ later ∈ rest, later.event.resetIslands = [] :=
        fun later member => noReset later (by simp [member])
      simp only [runObservedFrom, observedChannelEventsFrom, Chan.runTrace]
      rw [system.advanceRecovery_noReset observed.event observed.external
        initial headNone]
      rw [ih (system.advance observed.event.tick observed.external initial)
        restNone]
      rw [System.channelState_advance system observed.event.tick
        observed.external initial connection found]
      rfl

/-- Fragment-wide order/no-loss ledger for a declared channel. Accepted
payloads equal delivered payloads followed by the exact final queue, so the
single equation rules out loss, duplication, corruption, and reordering. -/
theorem observedChannelConservation (system : System)
    (connection : SystemConnection)
    (found : system.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection)
    (initial : system.State) (steps : List ObservedRecoveryEvent)
    (noReset : ∀ observed ∈ steps, observed.event.resetIslands = []) :
    let events := system.observedChannelEventsFrom connection initial steps
    system.channelState initial connection ++
        (connection.chan.runTrace
          (system.channelState initial connection) events).accepted =
      (connection.chan.runTrace
          (system.channelState initial connection) events).delivered ++
        system.channelState (system.runObservedFrom initial steps) connection := by
  dsimp only
  rw [system.channelState_runObservedFrom connection found initial steps noReset]
  exact connection.chan.runTrace_conservation
    (system.channelState initial connection)
    (system.observedChannelEventsFrom connection initial steps)

/-- A finite trace is valid when every live-reset event respects the declared
reset policy and the complete tick prefix respects the declared clock
relation. -/
structure ValidObservedTrace (system : System)
    (steps : List ObservedRecoveryEvent) : Prop where
  resets : ∀ step ∈ steps, system.recoveryEventOk step.event = true
  clocks : system.clockRel.accepts
    ((steps.map fun step => step.event.tick).toArray) = true

private def endpointMatchesConnectionB (endpoint : SystemOpenEndpoint)
    (connection : SystemConnection) (asSource : Bool) : Bool :=
  endpoint.chan.name == connection.chan.name &&
    endpoint.width == connection.width &&
    endpoint.chan.depth == connection.chan.depth &&
    endpoint.chan.policy == connection.chan.policy &&
    (if asSource then endpoint.island == connection.source
      else endpoint.island == connection.sink)

private def sameOpenEndpointB (left right : SystemOpenEndpoint) : Bool :=
  left.chan.name == right.chan.name && left.width == right.width &&
    left.chan.depth == right.chan.depth &&
    left.chan.policy == right.chan.policy && left.island == right.island

/-- Executable inventory check for a fragment embedded in a parent. It checks
that islands and internal channels retain their identities and every exported
endpoint is either retained as an explicit top-level environment contract or
closed by an exactly matching parent connection. The semantic simulation
certificate below remains authoritative. -/
def fragmentBoundaryCheckB (child parent : System) : Bool :=
  (child.islands.all fun island =>
      parent.islands.any fun candidate =>
        candidate.name == island.name && candidate.clock == island.clock &&
          candidate.design.name == island.design.name) &&
  (child.connections.all fun connection =>
      parent.connections.any (·.key == connection.key)) &&
  (child.openSources.all fun endpoint =>
      parent.openSources.any (sameOpenEndpointB endpoint) ||
        parent.connections.any fun connection =>
          endpointMatchesConnectionB endpoint connection true) &&
  (child.openSinks.all fun endpoint =>
      parent.openSinks.any (sameOpenEndpointB endpoint) ||
        parent.connections.any fun connection =>
          endpointMatchesConnectionB endpoint connection false)

private def emptyProjectedIsland : St where
  regs := fun _ _ => 0
  mems := fun _ _ _ => 0

/-- Canonical state restriction used by fragment embeddings. Coordinates not
declared by the child are replaced by fixed empty values, so changes in a
parent-only island or boundary channel cannot leak into child-state equality. -/
def restrictState (child : System) {parent : System}
    (state : parent.State) : child.State where
  island := fun name =>
    if (child.findIsland? name).isSome then state.island name
    else emptyProjectedIsland
  channel := fun name =>
    if (child.connections.find? fun connection =>
        connection.chan.name == name).isSome then state.channel name
    else ⟨0, []⟩
  time := state.time

@[simp] theorem restrictState_time (child : System) {parent : System}
    (state : parent.State) :
    (restrictState child state).time = state.time := rfl

theorem restrictState_island (child : System) {parent : System}
    (state : parent.State) (island : SystemIsland)
    (found : child.findIsland? island.name = some island) :
    (restrictState child state).island island.name = state.island island.name := by
  simp [restrictState, found]

theorem restrictState_channel (child : System) {parent : System}
    (state : parent.State) (connection : SystemConnection)
    (found : child.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection) :
    child.channelState (restrictState child state) connection =
      parent.channelState state connection := by
  have member : connection ∈ child.connections :=
    List.mem_of_find?_eq_some found
  have present : ∃ candidate,
      candidate ∈ child.connections ∧
        candidate.chan.name = connection.chan.name :=
    ⟨connection, member, rfl⟩
  unfold channelState connectionQueue
  simp [restrictState, present]

/-- The observable state projection relation. Only coordinates declared by
the child participate: total-map values at unrelated names are deliberately
irrelevant. -/
structure StateProjects (parent child : System)
    (parentState : parent.State) (childState : child.State) : Prop where
  time : childState.time = parentState.time
  island : ∀ name, (child.findIsland? name).isSome = true →
    childState.island name = parentState.island name
  channel : ∀ name,
    (child.connections.find? fun connection =>
      connection.chan.name == name).isSome = true →
    childState.channel name = parentState.channel name

/-- A forward simulation from a parent System to an embedded child System.
`projectExternal` supplies the inputs that the child observes after its open
endpoints have been connected by the parent. -/
structure ExecutionProjection (parent child : System) where
  boundary : fragmentBoundaryCheckB child parent = true
  projectEvent : RecoveryEvent → RecoveryEvent
  projectExternal : parent.State → ObservedRecoveryEvent → String → InEnv
  clockEvent : ∀ event clock,
    (projectEvent event).tick.fires clock = event.tick.fires clock
  resetEvent : ∀ event island,
    (projectEvent event).resets island = event.resets island
  resetCompatible : ∀ event,
    parent.recoveryEventOk event = true →
      child.recoveryEventOk (projectEvent event) = true
  clockCompatible : ∀ (events : List RecoveryEvent),
    parent.clockRel.accepts ((events.map (·.tick)).toArray) = true →
      child.clockRel.accepts
        (((events.map projectEvent).map (·.tick)).toArray) = true
  initial : StateProjects parent child parent.reset child.reset
  step : ∀ parentState childState observed,
    StateProjects parent child parentState childState →
    parent.recoveryEventOk observed.event = true →
    StateProjects parent child
      (parent.advanceRecovery observed.event observed.external parentState)
      (child.advanceRecovery (projectEvent observed.event)
        (projectExternal parentState observed) childState)

namespace ExecutionProjection

def projectObserved {parent child : System}
    (projection : ExecutionProjection parent child) (state : parent.State)
    (observed : ObservedRecoveryEvent) : ObservedRecoveryEvent :=
  { event := projection.projectEvent observed.event
    external := projection.projectExternal state observed }

/-- State-dependent trace projection. The next child input valuation is
derived from the matching pre-step parent state, not guessed from names after
the execution has finished. -/
def projectTraceFrom {parent child : System}
    (projection : ExecutionProjection parent child) :
    parent.State → List ObservedRecoveryEvent → List ObservedRecoveryEvent
  | _, [] => []
  | state, observed :: rest =>
      projection.projectObserved state observed ::
        projection.projectTraceFrom
          (parent.advanceRecovery observed.event observed.external state) rest

@[simp] theorem projectTraceFrom_events {parent child : System}
    (projection : ExecutionProjection parent child) (state : parent.State)
    (steps : List ObservedRecoveryEvent) :
    (projection.projectTraceFrom state steps).map (·.event) =
      (steps.map (·.event)).map projection.projectEvent := by
  induction steps generalizing state with
  | nil => rfl
  | cons observed rest ih =>
      simp [projectTraceFrom, projectObserved, ih]

/-- The central execution-projection theorem. Every finite parent execution
commutes with projection, including reset-aware steps and state-dependent
fragment input valuation. -/
theorem runObservedFrom_project {parent child : System}
    (projection : ExecutionProjection parent child)
    (parentInitial : parent.State) (childInitial : child.State)
    (steps : List ObservedRecoveryEvent)
    (initial : StateProjects parent child parentInitial childInitial)
    (valid : ∀ step ∈ steps,
      parent.recoveryEventOk step.event = true) :
    StateProjects parent child
      (parent.runObservedFrom parentInitial steps)
      (child.runObservedFrom childInitial
        (projection.projectTraceFrom parentInitial steps)) := by
  induction steps generalizing parentInitial childInitial with
  | nil => exact initial
  | cons observed rest ih =>
    simp only [System.runObservedFrom, projectTraceFrom, projectObserved]
    apply ih
    · exact projection.step parentInitial childInitial observed initial
        (valid observed (by simp))
    · exact fun step member => valid step (by simp [member])

theorem projectedTrace_valid {parent child : System}
    (projection : ExecutionProjection parent child) (initial : parent.State)
    {steps : List ObservedRecoveryEvent}
    (valid : ValidObservedTrace parent steps) :
    ValidObservedTrace child (projection.projectTraceFrom initial steps) := by
  constructor
  · have preservesResets : ∀ (state : parent.State)
        (trace : List ObservedRecoveryEvent),
        (∀ step ∈ trace, parent.recoveryEventOk step.event = true) →
        ∀ step ∈ projection.projectTraceFrom state trace,
          child.recoveryEventOk step.event = true := by
      intro state trace
      induction trace generalizing state with
      | nil => simp [projectTraceFrom]
      | cons observed rest ih =>
          intro sourceValid projected member
          simp only [projectTraceFrom, List.mem_cons] at member
          rcases member with rfl | later
          · exact projection.resetCompatible observed.event
              (sourceValid observed (by simp))
          · exact ih
              (parent.advanceRecovery observed.event observed.external state)
              (fun step stepMember => sourceValid step (by simp [stepMember]))
              projected later
    exact preservesResets initial steps valid.resets
  · have tickProjection :
        (projection.projectTraceFrom initial steps).map
            (fun step => step.event.tick) =
          (((steps.map (·.event)).map projection.projectEvent).map
            (·.tick)) := by
      calc
        _ = ((projection.projectTraceFrom initial steps).map (·.event)).map
              (·.tick) := by
                generalize projection.projectTraceFrom initial steps = projected
                induction projected with
                | nil => rfl
                | cons head tail ih => simp only [List.map_cons, ih]
        _ = _ := by
          simp [List.map_map, projection.projectTraceFrom_events]
    rw [tickProjection]
    exact projection.clockCompatible (steps.map (·.event)) (by
      simpa [List.map_map] using valid.clocks)

end ExecutionProjection

/-- A fragment-wide finite-trace theorem. The property may inspect the entire
projected input/reset/clock trace and its final fragment state, so it covers
cross-island safety and bounded progress rather than only local state. -/
def FiniteTraceTheorem (system : System)
    (property : List ObservedRecoveryEvent → system.State → Prop) : Prop :=
  ∀ steps, ValidObservedTrace system steps →
    property steps (system.runObserved steps)

namespace ExecutionProjection

/-- Transport a genuinely fragment-wide theorem through the proved execution
projection. Clock/reset compatibility is consumed by `projectedTrace_valid`;
the simulation law is consumed by `runObservedFrom_project`. -/
theorem liftFiniteTraceTheorem {parent child : System}
    (projection : ExecutionProjection parent child)
    {property : List ObservedRecoveryEvent → child.State → Prop}
    (theoremInChild : FiniteTraceTheorem child property) :
    FiniteTraceTheorem parent (fun steps final =>
      ∃ childFinal,
        StateProjects parent child final childFinal ∧
          property (projection.projectTraceFrom parent.reset steps) childFinal) := by
  intro steps valid
  have childValid := projection.projectedTrace_valid parent.reset valid
  have proved := theoremInChild _ childValid
  let childFinal := child.runObservedFrom child.reset
    (projection.projectTraceFrom parent.reset steps)
  refine ⟨childFinal, ?_, ?_⟩
  · exact projection.runObservedFrom_project parent.reset child.reset steps
      projection.initial valid.resets
  · exact proved

end ExecutionProjection

end System

namespace System.SystemFragment

/-- Parent-to-fragment specialization of the generic System forward
simulation certificate. -/
abbrev ExecutionProjection
    {Interface : System → Type u}
    {TheoremBundle : (system : System) → Interface system → Type u}
    (parent : System)
    (fragment : _root_.Loom.Hw.System.SystemFragment Interface TheoremBundle) :=
  System.ExecutionProjection parent fragment.system

/-- Reuse a schedule-sensitive theorem from a sealed fragment without
flattening its proof. The result talks about the identical child property on
the checked projected parent trace and state. -/
theorem liftFragmentTheorem
    {Interface : System → Type u}
    {TheoremBundle : (system : System) → Interface system → Type u}
    {parent : System}
    {fragment : _root_.Loom.Hw.System.SystemFragment Interface TheoremBundle}
    (projection : ExecutionProjection parent fragment)
    {property : List System.ObservedRecoveryEvent →
      fragment.system.State → Prop}
    (theoremInFragment : System.FiniteTraceTheorem fragment.system property) :
    System.FiniteTraceTheorem parent (fun steps final =>
      ∃ childFinal,
        System.StateProjects parent fragment.system final childFinal ∧
          property (projection.projectTraceFrom parent.reset steps) childFinal) :=
  projection.liftFiniteTraceTheorem theoremInFragment

end System.SystemFragment

end Loom.Hw
