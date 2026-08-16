-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.SystemProjection

/-!
# Genuine compositional multiclock proof gate

The reusable fragment accepts requests in one clock domain, forwards them
through an internal asynchronous channel, and returns responses from a second
domain. Two different parents close the typed request/response boundary. The
proof gate reuses one fragment execution theorem through checked semantic
projections rather than flattening the fragment proof.
-/

namespace Tests.SystemProjection

open Loom.Hw

def clientClock : ClockHandle := ⟨"client_clk"⟩
def workerClock : ClockHandle := ⟨"worker_clk"⟩
def engineClock : ClockHandle := ⟨"engine_clk"⟩
def collectorClock : ClockHandle := ⟨"collector_clk"⟩
def monitorClock : ClockHandle := ⟨"monitor_clk"⟩

def request : Chan 8 := ⟨"request", 2, .exchange⟩
def internal : Chan 8 := ⟨"internal", 2, .exchange⟩
def response : Chan 8 := ⟨"response", 2, .exchange⟩

def workerCore : Design where
  name := "projection_worker"
  regs := []
  mems := []
  outputs := []
  rules := [⟨"forward", .ite
    (.and request.hasData internal.canSend)
    (.seq (internal.send (.add request.data (.lit 1))) request.consume)
    .skip⟩]

def engineCore : Design where
  name := "projection_engine"
  regs := []
  mems := []
  outputs := []
  rules := [⟨"respond", .ite
    (.and internal.hasData response.canSend)
    (.seq (response.send (.add internal.data (.lit 1))) internal.consume)
    .skip⟩]

def clientCore : Design where
  name := "projection_client"
  regs := [⟨"next_request", 8, 1⟩]
  mems := []
  outputs := []
  rules := [⟨"issue", .ite request.canSend
    (.seq (request.send (.reg 8 "next_request"))
      (.write 8 "next_request" (.add (.reg 8 "next_request") (.lit 1))))
    .skip⟩]

def collectorCore : Design where
  name := "projection_collector"
  regs := [⟨"received", 8, 0⟩, ⟨"last_response", 8, 0⟩]
  mems := []
  outputs := ["received", "last_response"]
  rules := [⟨"collect", .ite response.hasData
    (.seq (.write 8 "received" (.add (.reg 8 "received") (.lit 1)))
      (.seq (.write 8 "last_response" response.data) response.consume))
    .skip⟩]

def monitorCore : Design where
  name := "projection_monitor"
  regs := [⟨"ticks", 8, 0⟩]
  mems := []
  outputs := ["ticks"]
  rules := [⟨"tick", .write 8 "ticks" (.add (.reg 8 "ticks") (.lit 1))⟩]

def workerIsland : IslandHandle := .named "worker" workerCore workerClock
def engineIsland : IslandHandle := .named "engine" engineCore engineClock
def clientIsland : IslandHandle := .named "client" clientCore workerClock
def collectorIsland : IslandHandle := .named "collector" collectorCore engineClock
def monitorIsland : IslandHandle := .named "monitor" monitorCore monitorClock

def internalRoute := internal.between workerIsland engineIsland
def requestSink := request.exportSink workerIsland
def responseSource := response.exportSource engineIsland
def requestSource := request.exportSource clientIsland
def responseSink := response.exportSink collectorIsland
def requestRoute := request.between clientIsland workerIsland
def responseRoute := response.between engineIsland collectorIsland

def fragmentBuilder : SystemBuilder :=
  System.empty
    |>.addErasedIsland workerIsland
    |>.addErasedIsland engineIsland
    |>.addChannel internalRoute
    |>.exportSink requestSink
    |>.exportSource responseSource
    |>.withClockRel .asynchronous

def fragmentSystem : System := fragmentBuilder.certify (by decide)

structure FragmentInterface (system : System) where
  request : DeclaredSink system request
  response : DeclaredSource system response

def fragmentInterface : FragmentInterface fragmentSystem where
  request := ⟨requestSink, by decide⟩
  response := ⟨responseSource, by decide⟩

def fragmentBlock : System.SealedBlock FragmentInterface (fun _ _ => Unit) where
  system := fragmentSystem
  islands := fragmentSystem.certifyIslands (by decide)
  interface := fragmentInterface
  theorems := ()

def fragment : System.SystemFragment FragmentInterface (fun _ _ => Unit) where
  block := fragmentBlock
  plan := .portable
  realizationReady := by decide

def emptyHost (name : String) : Design where
  name
  regs := []
  mems := []
  outputs := []
  rules := []

def hostA : IslandHandle := .named "host_a" (emptyHost "host_a") clientClock
def hostB : IslandHandle := .named "host_b" (emptyHost "host_b") monitorClock

def asynchronousParentBuilder : SystemBuilder :=
  System.empty
    |>.includeFragment fragment
    |>.addErasedIsland clientIsland
    |>.addErasedIsland collectorIsland
    |>.exportSource requestSource
    |>.exportSink responseSink
    |>.connectExports requestSource requestSink
    |>.connectExports responseSource responseSink
    |>.withClockRel .asynchronous

def asynchronousParent : System :=
  asynchronousParentBuilder.certify (by decide)

def monitoredParentBuilder : SystemBuilder :=
  asynchronousParentBuilder
    |>.addErasedIsland monitorIsland
    |>.withClockRel .interleaved

def monitoredParent : System :=
  monitoredParentBuilder.certify (by decide)

theorem asynchronous_find_worker :
    asynchronousParent.findIsland? workerIsland.name =
      fragmentSystem.findIsland? workerIsland.name := by
  rfl

theorem asynchronous_find_engine :
    asynchronousParent.findIsland? engineIsland.name =
      fragmentSystem.findIsland? engineIsland.name := by
  rfl

theorem fragment_island_names :
    fragmentSystem.islands.map (fun island => island.name) =
      [workerIsland.name, engineIsland.name] := by
  decide

theorem fragment_island_name {name : String}
    (present : (fragmentSystem.findIsland? name).isSome = true) :
    name = workerIsland.name ∨ name = engineIsland.name := by
  cases found : fragmentSystem.findIsland? name with
  | none => simp [found] at present
  | some island =>
      have islandName := System.findIsland?_name found
      have member : island ∈ fragmentSystem.islands := by
        apply List.mem_of_find?_eq_some
        change fragmentSystem.islands.find?
          (fun candidate => candidate.name == name) = some island at found
        exact found
      have mapped : island.name ∈
          fragmentSystem.islands.map (fun candidate => candidate.name) :=
        List.mem_map_of_mem member
      rw [fragment_island_names] at mapped
      simp only [List.mem_cons] at mapped
      simpa [islandName] using mapped

theorem fragment_channel_name {name : String}
    (present : (fragmentSystem.connections.find? fun connection =>
      connection.chan.name == name).isSome = true) : name = internal.name := by
  rw [show fragmentSystem.connections = [internalRoute.toSystemConnection]
    by rfl] at present
  simp [internalRoute, ChannelRoute.toSystemConnection, Chan.between,
    internal] at present
  exact present.symm

theorem asynchronous_find_of_fragment {name : String} {island : SystemIsland}
    (found : fragmentSystem.findIsland? name = some island) :
    asynchronousParent.findIsland? name = some island := by
  have present : (fragmentSystem.findIsland? name).isSome = true := by
    rw [found]
    rfl
  rcases fragment_island_name present with worker | engine
  · subst name
    rw [asynchronous_find_worker]
    exact found
  · subst name
    rw [asynchronous_find_engine]
    exact found

@[simp] theorem fragment_find_internal :
    fragmentSystem.connections.find? (fun connection =>
      connection.chan.name == internal.name) =
        some internalRoute.toSystemConnection := rfl

@[simp] theorem asynchronous_find_internal :
    asynchronousParent.connections.find? (fun connection =>
      connection.chan.name == internal.name) =
        some internalRoute.toSystemConnection := rfl

theorem asynchronous_connectionInput_eq
    (parentState : asynchronousParent.State)
    (childState : fragmentSystem.State)
    (represents : System.StateProjects asynchronousParent fragmentSystem
      parentState childState)
    (event : NamedClockEvent) (name inputName : String) (width : Nat) :
    fragmentSystem.connectionInput? event childState
        internalRoute.toSystemConnection name inputName width =
      asynchronousParent.connectionInput? event parentState
        internalRoute.toSystemConnection name inputName width := by
  have workerState := represents.island workerIsland.name (by decide)
  have engineState := represents.island engineIsland.name (by decide)
  have queueState := represents.channel internal.name (by decide)
  have workerState' : childState.island "worker" =
      parentState.island "worker" := workerState
  have engineState' : childState.island "engine" =
      parentState.island "engine" := engineState
  have queueState' : childState.channel "internal" =
      parentState.channel "internal" := queueState
  unfold System.connectionInput? System.connectionQueue System.connectionEvent
  simp only [internalRoute, ChannelRoute.toSystemConnection, Chan.between,
    workerIsland, engineIsland, IslandHandle.named]
  have workerFind : asynchronousParent.findIsland? "worker" =
      fragmentSystem.findIsland? "worker" := asynchronous_find_worker
  have engineFind : asynchronousParent.findIsland? "engine" =
      fragmentSystem.findIsland? "engine" := asynchronous_find_engine
  rw [workerFind, engineFind]
  simp [internal,
    Chan.sourceReadyName, Chan.sourceAcceptedName, Chan.sinkValidName,
    Chan.sinkPayloadName, Chan.sinkPopName, Chan.sourceValid,
    Chan.sourcePayload, Chan.stem, workerState', engineState', queueState']

theorem asynchronous_islandInput_eq
    (parentState : asynchronousParent.State)
    (childState : fragmentSystem.State)
    (represents : System.StateProjects asynchronousParent fragmentSystem
      parentState childState)
    (event : NamedClockEvent) (external : String → InEnv) (name : String) :
    fragmentSystem.islandInput event childState
        (asynchronousParent.islandInput event parentState external) name =
      asynchronousParent.islandInput event parentState external name := by
  funext inputName width
  simp only [System.islandInput, System.inputFor]
  rw [show fragmentSystem.connections = [internalRoute.toSystemConnection]
    by rfl]
  rw [show asynchronousParent.connections =
    [internalRoute.toSystemConnection, requestRoute.toSystemConnection,
      responseRoute.toSystemConnection] by rfl]
  simp only [List.findSome?_cons, List.findSome?_nil]
  rw [asynchronous_connectionInput_eq parentState childState represents]
  cases asynchronousParent.connectionInput? event parentState
      internalRoute.toSystemConnection name inputName width <;> rfl

theorem asynchronous_connectionResult_eq
    (parentState : asynchronousParent.State)
    (childState : fragmentSystem.State)
    (represents : System.StateProjects asynchronousParent fragmentSystem
      parentState childState) (event : NamedClockEvent) :
    fragmentSystem.connectionResult event childState
        internalRoute.toSystemConnection =
      asynchronousParent.connectionResult event parentState
        internalRoute.toSystemConnection := by
  have workerState : childState.island "worker" =
      parentState.island "worker" :=
    represents.island workerIsland.name (by decide)
  have engineState : childState.island "engine" =
      parentState.island "engine" :=
    represents.island engineIsland.name (by decide)
  have queueState : childState.channel "internal" =
      parentState.channel "internal" :=
    represents.channel internal.name (by decide)
  unfold System.connectionResult System.connectionQueue System.connectionEvent
  simp only [internalRoute, ChannelRoute.toSystemConnection, Chan.between,
    workerIsland, engineIsland, IslandHandle.named]
  have workerFind : asynchronousParent.findIsland? "worker" =
      fragmentSystem.findIsland? "worker" := asynchronous_find_worker
  have engineFind : asynchronousParent.findIsland? "engine" =
      fragmentSystem.findIsland? "engine" := asynchronous_find_engine
  rw [workerFind, engineFind]
  rw [workerState, engineState]
  simp only [internal]
  rw [queueState]

#guard System.fragmentBoundaryCheckB fragmentSystem asynchronousParent
#guard System.fragmentBoundaryCheckB fragmentSystem monitoredParent
#guard asynchronousParent.openSources.isEmpty &&
  asynchronousParent.openSinks.isEmpty
#guard monitoredParent.openSources.isEmpty && monitoredParent.openSinks.isEmpty

/-- The parents close both typed fragment endpoints with ordinary same-clock
components. These handles are the explicit endpoint contracts consumed by
protocol proofs; no raw valid/ready/payload wires appear at the boundary. -/
structure ClosedParentInterface (system : System) where
  request : System.ConnectionHandle system requestRoute.toSystemConnection
  response : System.ConnectionHandle system responseRoute.toSystemConnection

def asynchronousInterface : ClosedParentInterface asynchronousParent where
  request := requestRoute.proofHandle asynchronousParent (by rfl)
  response := responseRoute.proofHandle asynchronousParent (by rfl)

def monitoredInterface : ClosedParentInterface monitoredParent where
  request := requestRoute.proofHandle monitoredParent (by rfl)
  response := responseRoute.proofHandle monitoredParent (by rfl)

def closedClientIsland : SystemIsland :=
  ⟨clientIsland.name, clientIsland.clock.name, request.withSource clientCore⟩

def closedCollectorIsland : SystemIsland :=
  ⟨collectorIsland.name, collectorIsland.clock.name,
    response.withSink collectorCore⟩

def asynchronousEmbedding :
    System.StandardEmbedding asynchronousParent fragmentSystem where
  islandSuffix := [closedClientIsland, closedCollectorIsland]
  connectionSuffix :=
    [requestRoute.toSystemConnection, responseRoute.toSystemConnection]
  islands := rfl
  connections := rfl
  childEndpoints := by decide
  boundary := by decide
  resetPolicy := rfl
  coordinated := rfl
  clockCompatible := by intros; rfl

def asynchronousProjection :
    System.ExecutionProjection asynchronousParent fragmentSystem :=
  fragment.standardProjection asynchronousEmbedding

theorem monitored_find_worker :
    monitoredParent.findIsland? workerIsland.name =
      fragmentSystem.findIsland? workerIsland.name := by
  rfl

theorem monitored_find_engine :
    monitoredParent.findIsland? engineIsland.name =
      fragmentSystem.findIsland? engineIsland.name := by
  rfl

theorem monitored_find_of_fragment {name : String} {island : SystemIsland}
    (found : fragmentSystem.findIsland? name = some island) :
    monitoredParent.findIsland? name = some island := by
  have present : (fragmentSystem.findIsland? name).isSome = true := by
    rw [found]
    rfl
  rcases fragment_island_name present with worker | engine
  · subst name
    rw [monitored_find_worker]
    exact found
  · subst name
    rw [monitored_find_engine]
    exact found

@[simp] theorem monitored_find_internal :
    monitoredParent.connections.find? (fun connection =>
      connection.chan.name == internal.name) =
        some internalRoute.toSystemConnection := rfl

theorem monitored_connectionInput_eq
    (parentState : monitoredParent.State)
    (childState : fragmentSystem.State)
    (represents : System.StateProjects monitoredParent fragmentSystem
      parentState childState)
    (event : NamedClockEvent) (name inputName : String) (width : Nat) :
    fragmentSystem.connectionInput? event childState
        internalRoute.toSystemConnection name inputName width =
      monitoredParent.connectionInput? event parentState
        internalRoute.toSystemConnection name inputName width := by
  have workerState := represents.island workerIsland.name (by decide)
  have engineState := represents.island engineIsland.name (by decide)
  have queueState := represents.channel internal.name (by decide)
  have workerState' : childState.island "worker" =
      parentState.island "worker" := workerState
  have engineState' : childState.island "engine" =
      parentState.island "engine" := engineState
  have queueState' : childState.channel "internal" =
      parentState.channel "internal" := queueState
  unfold System.connectionInput? System.connectionQueue System.connectionEvent
  simp only [internalRoute, ChannelRoute.toSystemConnection, Chan.between,
    workerIsland, engineIsland, IslandHandle.named]
  have workerFind : monitoredParent.findIsland? "worker" =
      fragmentSystem.findIsland? "worker" := monitored_find_worker
  have engineFind : monitoredParent.findIsland? "engine" =
      fragmentSystem.findIsland? "engine" := monitored_find_engine
  rw [workerFind, engineFind]
  simp [internal, Chan.sourceReadyName, Chan.sourceAcceptedName,
    Chan.sinkValidName, Chan.sinkPayloadName, Chan.sinkPopName,
    Chan.sourceValid, Chan.sourcePayload, Chan.stem, workerState',
    engineState', queueState']

theorem monitored_islandInput_eq
    (parentState : monitoredParent.State)
    (childState : fragmentSystem.State)
    (represents : System.StateProjects monitoredParent fragmentSystem
      parentState childState)
    (event : NamedClockEvent) (external : String → InEnv) (name : String) :
    fragmentSystem.islandInput event childState
        (monitoredParent.islandInput event parentState external) name =
      monitoredParent.islandInput event parentState external name := by
  funext inputName width
  simp only [System.islandInput, System.inputFor]
  rw [show fragmentSystem.connections = [internalRoute.toSystemConnection]
    by rfl]
  rw [show monitoredParent.connections =
    [internalRoute.toSystemConnection, requestRoute.toSystemConnection,
      responseRoute.toSystemConnection] by rfl]
  simp only [List.findSome?_cons, List.findSome?_nil]
  rw [monitored_connectionInput_eq parentState childState represents]
  cases monitoredParent.connectionInput? event parentState
      internalRoute.toSystemConnection name inputName width <;> rfl

theorem monitored_connectionResult_eq
    (parentState : monitoredParent.State)
    (childState : fragmentSystem.State)
    (represents : System.StateProjects monitoredParent fragmentSystem
      parentState childState) (event : NamedClockEvent) :
    fragmentSystem.connectionResult event childState
        internalRoute.toSystemConnection =
      monitoredParent.connectionResult event parentState
        internalRoute.toSystemConnection := by
  have workerState : childState.island "worker" =
      parentState.island "worker" :=
    represents.island workerIsland.name (by decide)
  have engineState : childState.island "engine" =
      parentState.island "engine" :=
    represents.island engineIsland.name (by decide)
  have queueState : childState.channel "internal" =
      parentState.channel "internal" :=
    represents.channel internal.name (by decide)
  unfold System.connectionResult System.connectionQueue System.connectionEvent
  simp only [internalRoute, ChannelRoute.toSystemConnection, Chan.between,
    workerIsland, engineIsland, IslandHandle.named]
  have workerFind : monitoredParent.findIsland? "worker" =
      fragmentSystem.findIsland? "worker" := monitored_find_worker
  have engineFind : monitoredParent.findIsland? "engine" =
      fragmentSystem.findIsland? "engine" := monitored_find_engine
  rw [workerFind, engineFind]
  rw [workerState, engineState]
  simp only [internal]
  rw [queueState]

def monitoredEmbedding :
    System.StandardEmbedding monitoredParent fragmentSystem where
  islandSuffix :=
    [closedClientIsland, closedCollectorIsland,
      monitorIsland.toSystemIsland]
  connectionSuffix :=
    [requestRoute.toSystemConnection, responseRoute.toSystemConnection]
  islands := rfl
  connections := rfl
  childEndpoints := by decide
  boundary := by decide
  resetPolicy := rfl
  coordinated := rfl
  clockCompatible := by intros; rfl

def monitoredProjection :
    System.ExecutionProjection monitoredParent fragmentSystem :=
  fragment.standardProjection monitoredEmbedding

/-! ## One theorem bundle reused in both parents -/

/-- The fragment's internal CDC queue has one trace ledger: no payload is
lost, duplicated, corrupted, or reordered. The property mentions the whole
fragment execution rather than one island's local state. -/
def internalOrderingNoLoss
    (steps : List System.ObservedRecoveryEvent)
    (final : fragmentSystem.State) : Prop :=
  let connection := internalRoute.toSystemConnection
  let events := fragmentSystem.observedChannelEventsFrom connection
    fragmentSystem.reset steps
  fragmentSystem.channelState fragmentSystem.reset connection ++
      (connection.chan.runTrace
        (fragmentSystem.channelState fragmentSystem.reset connection)
        events).accepted =
    (connection.chan.runTrace
        (fragmentSystem.channelState fragmentSystem.reset connection)
        events).delivered ++ fragmentSystem.channelState final connection

theorem fragmentOrderingNoLoss :
    System.FiniteTraceTheorem fragmentSystem internalOrderingNoLoss := by
  intro steps valid
  apply fragmentSystem.observedChannelConservation
    internalRoute.toSystemConnection fragment_find_internal
  intro observed member
  exact System.recoveryEventOk_coordinated_noReset fragmentSystem
    observed.event rfl (valid.resets observed member)

def asynchronousOrderingNoLoss :=
  fragment.liftFragmentTheorem asynchronousProjection fragmentOrderingNoLoss

def monitoredOrderingNoLoss :=
  fragment.liftFragmentTheorem monitoredProjection fragmentOrderingNoLoss

/-! ## Bounded request/response witness

This deliberately states the environment assumptions rather than smuggling
fairness into the System semantics: one request is presented, the worker and
engine each receive two ticks, and the response endpoint remains ready. -/

def serviceExternal (requestOn responseReady : Bool) (payload : BitVec 8) :
    String → InEnv := fun island input width =>
  if island = workerIsland.name && input = request.sinkValidName then
    if h : width = 1 then h ▸ (if requestOn then 1#1 else 0#1) else 0
  else if island = workerIsland.name && input = request.sinkPayloadName then
    if h : width = 8 then h ▸ payload else 0
  else if island = engineIsland.name && input = response.sourceReadyName then
    if h : width = 1 then h ▸ (if responseReady then 1#1 else 0#1) else 0
  else 0

def serviceStep (clock : ClockHandle) (requestOn : Bool := false) :
    System.ObservedRecoveryEvent :=
  ⟨⟨clock.tick, []⟩, serviceExternal requestOn true 40⟩

/-- Explicit progress and backpressure assumptions for the bounded theorem. -/
def serviceTrace : List System.ObservedRecoveryEvent :=
  [serviceStep workerClock true, serviceStep workerClock,
   serviceStep engineClock, serviceStep engineClock]

def responseIs42 {system : System} (state : system.State) : Prop :=
  (state.island engineIsland.name).regs response.sourceValidName 1 = 1#1 ∧
    (state.island engineIsland.name).regs response.sourcePayloadName 8 = 42#8

/-- The environment-side progress contract. Equality to `serviceTrace`
packages the required request presentation, destination readiness, and four
named clock events without elevating any of them into global fairness axioms. -/
structure BoundedServiceContract
    (steps : List System.ObservedRecoveryEvent) : Prop where
  exactTrace : steps = serviceTrace

def boundedResponseProperty
    (steps : List System.ObservedRecoveryEvent)
    (final : fragmentSystem.State) : Prop :=
  BoundedServiceContract steps → responseIs42 final

theorem fragmentBoundedResponse :
    System.FiniteTraceTheorem fragmentSystem boundedResponseProperty := by
  intro steps _ contract
  rw [contract.exactTrace]
  change
    ((fragmentSystem.runObserved serviceTrace).island "engine").regs
        response.sourceValidName 1 = 1#1 ∧
      ((fragmentSystem.runObserved serviceTrace).island "engine").regs
        response.sourcePayloadName 8 = 42#8
  decide

def asynchronousBoundedResponse :=
  fragment.liftFragmentTheorem asynchronousProjection fragmentBoundedResponse

def monitoredBoundedResponse :=
  fragment.liftFragmentTheorem monitoredProjection fragmentBoundedResponse

theorem asynchronousResponseUnderContract
    (steps : List System.ObservedRecoveryEvent)
    (valid : System.ValidObservedTrace asynchronousParent steps)
    (contract : BoundedServiceContract
      (asynchronousProjection.projectTraceFrom asynchronousParent.reset steps)) :
    responseIs42 (asynchronousParent.runObserved steps) := by
  have lifted := asynchronousBoundedResponse steps valid
  rcases lifted with ⟨childFinal, projects, responds⟩
  have childResponse := responds contract
  have engineEq := projects.island engineIsland.name (by decide)
  simpa [responseIs42, engineEq] using childResponse

theorem monitoredResponseUnderContract
    (steps : List System.ObservedRecoveryEvent)
    (valid : System.ValidObservedTrace monitoredParent steps)
    (contract : BoundedServiceContract
      (monitoredProjection.projectTraceFrom monitoredParent.reset steps)) :
    responseIs42 (monitoredParent.runObserved steps) := by
  have lifted := monitoredBoundedResponse steps valid
  rcases lifted with ⟨childFinal, projects, responds⟩
  have childResponse := responds contract
  have engineEq := projects.island engineIsland.name (by decide)
  simpa [responseIs42, engineEq] using childResponse

def asynchronousPlan : RealizationPlan :=
  RealizationPlan.synchronous.includeFragment fragment

def monitoredPlan : RealizationPlan :=
  RealizationPlan.synchronous.includeFragment fragment

#guard asynchronousPlan.select internalRoute.key == fragment.plan.select internalRoute.key
#guard monitoredPlan.select internalRoute.key == fragment.plan.select internalRoute.key

/-! ## Fail-closed incompatible boundaries -/

def alignedFragmentBuilder : SystemBuilder :=
  fragmentBuilder.withClockRel (.aligned workerClock.name engineClock.name)

def alignedFragmentSystem : System :=
  alignedFragmentBuilder.certify (by decide)

def alignedFragmentInterface : FragmentInterface alignedFragmentSystem where
  request := ⟨requestSink, by decide⟩
  response := ⟨responseSource, by decide⟩

def alignedFragmentBlock :
    System.SealedBlock FragmentInterface (fun _ _ => Unit) where
  system := alignedFragmentSystem
  islands := alignedFragmentSystem.certifyIslands (by decide)
  interface := alignedFragmentInterface
  theorems := ()

def alignedFragment :
    System.SystemFragment FragmentInterface (fun _ _ => Unit) where
  block := alignedFragmentBlock
  plan := .portable
  realizationReady := by decide

def clockMismatchParentBuilder : SystemBuilder :=
  System.empty.includeFragment alignedFragment |>.withClockRel .asynchronous

def clockMismatchParent : System :=
  clockMismatchParentBuilder.certify (by decide)

/-- The failed obligation names the exact semantic mismatch: an unconstrained
asynchronous parent does not refine a fragment that requires aligned edges. -/
example : ¬ System.SystemFragment.ClockCompatible
    clockMismatchParent alignedFragment := by
  intro compatible
  exact ClockRel.asynchronous_not_refines_aligned (by decide)
    compatible.refines

def resetMismatchBuilder : SystemBuilder :=
  System.empty.includeFragment fragment |>.withIndependentReset

def resetMismatchMessage : String :=
  match resetMismatchBuilder.assemble with
  | .ok _ => "unexpected success"
  | .error message => message

example : resetMismatchMessage =
    "included System reset policy differs from parent; rebuild or explicitly adapt the child contract" := by
  decide

def wrongRequest : Chan 8 := ⟨"request", 4, .exchange⟩

def endpointMismatchBuilder : SystemBuilder :=
  System.empty.includeFragment fragment
    |>.connectOpen wrongRequest "external" workerIsland.name

def endpointMismatchMessage : String :=
  match endpointMismatchBuilder.assemble with
  | .ok _ => "unexpected success"
  | .error message => message

example : endpointMismatchMessage =
    "connected channel still has an exported endpoint; closure requires exact channel name, width, depth, policy, and owner" := by
  decide

end Tests.SystemProjection
