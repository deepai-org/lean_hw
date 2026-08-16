-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Tests.SystemProjection

/-!
# Predicate-based bounded multiclock progress

The earlier witness required literal equality with one four-event trace.  This
gate observes only the fragment-relevant facts: worker/engine ticks, request
presentation, destination readiness, and reset absence. Events that tick
neither fragment domain may be inserted anywhere.
-/

namespace Tests.SystemProjection

open Loom.Hw

@[ext] structure ServiceObservation where
  tick : NamedClockEvent
  workerTick : Bool
  engineTick : Bool
  requestValid : BitVec 1
  requestPayload : BitVec 8
  responseReady : BitVec 1
  workerInputs : InEnv
  engineInputs : InEnv

def observeService (step : System.ObservedRecoveryEvent) : ServiceObservation where
  tick := step.event.tick
  workerTick := step.event.tick.fires workerClock.name
  engineTick := step.event.tick.fires engineClock.name
  requestValid := step.external workerIsland.name request.sinkValidName 1
  requestPayload := step.external workerIsland.name request.sinkPayloadName 8
  responseReady := step.external engineIsland.name response.sourceReadyName 1
  workerInputs := step.external workerIsland.name
  engineInputs := step.external engineIsland.name

def serviceRelevant (step : System.ObservedRecoveryEvent) : Bool :=
  step.event.tick.fires workerClock.name ||
    step.event.tick.fires engineClock.name

def expectedServiceObservations : List ServiceObservation :=
  serviceTrace.map observeService

/-- Environmental service premises, stated independently of irrelevant clock
events. The observation equation implies one accepted request opportunity,
two worker ticks, two ready engine ticks, and no extra fragment-domain ticks;
`noReset` rules out interruption of that bounded service window. This focused
theorem retains the full worker/engine input functions rather than claiming
input-footprint slicing. -/
structure PredicateServiceContract
    (steps : List System.ObservedRecoveryEvent) : Prop where
  noReset : ∀ step ∈ steps, step.event.resetIslands = []
  observations :
    (steps.filter serviceRelevant).map observeService =
      expectedServiceObservations

structure SameServiceState
    (left right : fragmentSystem.State) : Prop where
  islands : left.island = right.island
  channels : left.channel = right.channel

namespace SameServiceState

theorem refl (state : fragmentSystem.State) : SameServiceState state state :=
  ⟨rfl, rfl⟩

theorem trans {first second third : fragmentSystem.State}
    (left : SameServiceState first second)
    (right : SameServiceState second third) :
    SameServiceState first third :=
  ⟨left.islands.trans right.islands, left.channels.trans right.channels⟩

theorem response_iff {left right : fragmentSystem.State}
    (same : SameServiceState left right) :
    responseIs42 left ↔ responseIs42 right := by
  simp only [responseIs42]
  rw [same.islands]

end SameServiceState

def fragmentWorkerIsland : SystemIsland :=
  ⟨workerIsland.name, workerIsland.clock.name,
    request.withSink (internal.withSource workerCore)⟩

def fragmentEngineIsland : SystemIsland :=
  ⟨engineIsland.name, engineIsland.clock.name,
    response.withSource (internal.withSink engineCore)⟩

@[simp] theorem fragment_find_worker_exact :
    fragmentSystem.findIsland? workerIsland.name = some fragmentWorkerIsland := rfl

@[simp] theorem fragment_find_engine_exact :
    fragmentSystem.findIsland? engineIsland.name = some fragmentEngineIsland := rfl

def fragmentIdentityEmbedding :
    System.StandardEmbedding fragmentSystem fragmentSystem where
  islandSuffix := []
  connectionSuffix := []
  islands := by simp
  connections := by simp
  childEndpoints := by decide
  boundary := by decide
  resetPolicy := rfl
  coordinated := rfl
  clockCompatible := by intros; assumption

/-- The concrete fragment transition depends on an event only through the
five observations above. This theorem is deliberately fragment-specific: it
is the reusable service-interface contract, not a new global fairness rule. -/
theorem serviceObservation_step
    (leftStep rightStep : System.ObservedRecoveryEvent)
    (leftState rightState : fragmentSystem.State)
    (same : SameServiceState leftState rightState)
    (leftNoReset : leftStep.event.resetIslands = [])
    (rightNoReset : rightStep.event.resetIslands = [])
    (observation : observeService leftStep = observeService rightStep) :
    SameServiceState
      (fragmentSystem.advanceRecovery leftStep.event leftStep.external leftState)
      (fragmentSystem.advanceRecovery rightStep.event rightStep.external rightState) := by
  rw [fragmentSystem.advanceRecovery_noReset _ _ _ leftNoReset]
  rw [fragmentSystem.advanceRecovery_noReset _ _ _ rightNoReset]
  cases leftStep with
  | mk leftEvent leftExternal =>
    cases rightStep with
    | mk rightEvent rightExternal =>
      have workerTickEq := congrArg ServiceObservation.workerTick observation
      have engineTickEq := congrArg ServiceObservation.engineTick observation
      have requestValidEq := congrArg ServiceObservation.requestValid observation
      have requestPayloadEq := congrArg ServiceObservation.requestPayload observation
      have responseReadyEq := congrArg ServiceObservation.responseReady observation
      have workerInputsEq := congrArg ServiceObservation.workerInputs observation
      have engineInputsEq := congrArg ServiceObservation.engineInputs observation
      have tickEq := congrArg ServiceObservation.tick observation
      simp only [observeService] at workerTickEq engineTickEq requestValidEq requestPayloadEq responseReadyEq
      simp only [observeService] at workerInputsEq engineInputsEq
      simp only [observeService] at tickEq
      have data : System.StateDataProjects fragmentSystem fragmentSystem
          rightState leftState :=
        { island := fun name _ => congrFun same.islands name
          channel := fun name width _ => by rw [same.channels] }
      constructor
      · funext name
        simp only [System.advance]
        cases found : fragmentSystem.findIsland? name with
        | none => simp [same.islands]
        | some island =>
          have present : (fragmentSystem.findIsland? name).isSome = true := by
            simp [found]
          rcases fragment_island_name present with worker | engine
          · subst name
            rw [fragment_find_worker_exact] at found
            cases found
            simp only [fragmentWorkerIsland, workerIsland, IslandHandle.named]
            rw [workerTickEq, same.islands]
            by_cases ticked : rightEvent.tick.fires workerClock.name = true
            · simp only [ticked, ↓reduceIte]
              congr 1
              funext inputName width
              rw [tickEq]
              unfold System.islandInput System.inputFor
              rw [fragmentIdentityEmbedding.childConnectionInputs_eq
                rightState leftState data rightEvent.tick "worker"
                inputName width]
              rw [show leftExternal "worker" = rightExternal "worker" by
                simpa [workerIsland] using workerInputsEq]
            · simp [ticked]
          · subst name
            rw [fragment_find_engine_exact] at found
            cases found
            simp only [fragmentEngineIsland, engineIsland, IslandHandle.named]
            rw [engineTickEq, same.islands]
            by_cases ticked : rightEvent.tick.fires engineClock.name = true
            · simp only [ticked, ↓reduceIte]
              congr 1
              funext inputName width
              rw [tickEq]
              unfold System.islandInput System.inputFor
              rw [fragmentIdentityEmbedding.childConnectionInputs_eq
                rightState leftState data rightEvent.tick "engine"
                inputName width]
              rw [show leftExternal "engine" = rightExternal "engine" by
                simpa [engineIsland] using engineInputsEq]
            · simp [ticked]
      · funext name
        simp only [System.advance]
        cases found : fragmentSystem.connections.find? (fun connection =>
            connection.chan.name == name) with
        | none => simp [same.channels]
        | some connection =>
          have present : (fragmentSystem.connections.find? fun candidate =>
              candidate.chan.name == name).isSome = true := by
            rw [found]
            rfl
          have onlyInternal := fragment_channel_name present
          subst name
          rw [fragment_find_internal] at found
          cases found
          simp [System.connectionResult, System.connectionEvent,
            System.connectionQueue, internalRoute,
            ChannelRoute.toSystemConnection, Chan.between, workerIsland,
            engineIsland, same.islands, same.channels, tickEq]

def canonicalObservedService : List System.ObservedRecoveryEvent := serviceTrace

theorem canonical_observations :
    canonicalObservedService.map observeService = expectedServiceObservations := by
  rfl

theorem canonical_noReset :
    ∀ step ∈ canonicalObservedService, step.event.resetIslands = [] := by
  decide

/-- Removing or inserting pure non-fragment events does not change fragment
data state; it changes only the event counter. -/
theorem irrelevant_step
    (step : System.ObservedRecoveryEvent) (state : fragmentSystem.State)
    (noReset : step.event.resetIslands = [])
    (irrelevant : serviceRelevant step = false)
    (wellFormed : (state.channel internal.name).width = 8) :
    SameServiceState
      (fragmentSystem.advanceRecovery step.event step.external state) state := by
  have irrelevantPair :
      step.event.tick.fires workerClock.name = false ∧
        step.event.tick.fires engineClock.name = false := by
    exact Bool.or_eq_false_iff.mp (by simpa [serviceRelevant] using irrelevant)
  constructor
  · funext name
    rw [fragmentSystem.advanceRecovery_noReset step.event step.external state noReset]
    cases found : fragmentSystem.findIsland? name with
    | none => simp [System.advance, found]
    | some island =>
      have present : (fragmentSystem.findIsland? name).isSome = true := by
        simp [found]
      rcases fragment_island_name present with worker | engine <;> subst name
      · rw [fragment_find_worker_exact] at found
        cases found
        exact fragmentSystem.advance_island_unticked _ _ _
          fragmentWorkerIsland fragment_find_worker_exact irrelevantPair.1
      · rw [fragment_find_engine_exact] at found
        cases found
        exact fragmentSystem.advance_island_unticked _ _ _
          fragmentEngineIsland fragment_find_engine_exact irrelevantPair.2
  · funext name
    rw [fragmentSystem.advanceRecovery_noReset step.event step.external state noReset]
    cases found : fragmentSystem.connections.find? (fun connection =>
        connection.chan.name == name) with
    | none => simp [System.advance, found]
    | some connection =>
      have present : (fragmentSystem.connections.find? fun candidate =>
          candidate.chan.name == name).isSome = true := by
        rw [found]
        rfl
      have onlyInternal := fragment_channel_name present
      subst name
      rw [fragment_find_internal] at found
      cases found
      cases queueEq : state.channel internal.name with
      | mk oldWidth values =>
        simp only [queueEq] at wellFormed
        subst oldWidth
        simp only [System.advance, fragment_find_internal]
        unfold System.connectionResult System.connectionEvent
        simp only [internalRoute, ChannelRoute.toSystemConnection, Chan.between]
        rw [fragment_find_worker_exact, fragment_find_engine_exact]
        simp only [fragmentWorkerIsland, fragmentEngineIsland, workerIsland,
          engineIsland, IslandHandle.named]
        rw [irrelevantPair.1, irrelevantPair.2]
        have queueView : System.connectionQueue state
            { width := 8, chan := internal, source := "worker", sink := "engine" } =
            values := by
          have queueEq' : state.channel "internal" =
              ({ width := 8, values := values } : System.PackedQueue) := by
            simpa [internal] using queueEq
          unfold System.connectionQueue
          change (state.channel "internal").asWidth 8 = values
          rw [queueEq']
          simp [System.PackedQueue.asWidth]
        rw [queueView]
        simp [Chan.step]
        rfl

theorem advance_internal_width
    (step : System.ObservedRecoveryEvent) (state : fragmentSystem.State)
    (noReset : step.event.resetIslands = []) :
    ((fragmentSystem.advanceRecovery step.event step.external state).channel
      internal.name).width = 8 := by
  rw [fragmentSystem.advanceRecovery_noReset step.event step.external state noReset]
  simp only [System.advance]
  change (match fragmentSystem.connections.find? (fun (connection : SystemConnection) =>
      connection.chan.name == internal.name) with
    | some connection =>
        ({ width := connection.width,
           values := (fragmentSystem.connectionResult step.event.tick state
             connection).state } : System.PackedQueue)
    | none => state.channel internal.name).width = 8
  rw [fragment_find_internal]
  rfl

theorem erase_irrelevant_from
    (steps : List System.ObservedRecoveryEvent)
    (leftState rightState : fragmentSystem.State)
    (same : SameServiceState leftState rightState)
    (leftWidth : (leftState.channel internal.name).width = 8)
    (rightWidth : (rightState.channel internal.name).width = 8)
    (noReset : ∀ step ∈ steps, step.event.resetIslands = []) :
    SameServiceState
      (fragmentSystem.runObservedFrom leftState steps)
      (fragmentSystem.runObservedFrom rightState
        (steps.filter serviceRelevant)) := by
  induction steps generalizing leftState rightState with
  | nil => exact same
  | cons step rest ih =>
    have headNoReset := noReset step (by simp)
    have tailNoReset : ∀ later ∈ rest, later.event.resetIslands = [] :=
      fun later member => noReset later (by simp [member])
    by_cases relevant : serviceRelevant step = true
    · simp only [System.runObservedFrom, List.filter_cons, relevant, ↓reduceIte]
      have nextSame := serviceObservation_step step step leftState rightState
        same headNoReset headNoReset rfl
      exact ih
        (fragmentSystem.advanceRecovery step.event step.external leftState)
        (fragmentSystem.advanceRecovery step.event step.external rightState)
        nextSame
        (advance_internal_width step leftState headNoReset)
        (advance_internal_width step rightState headNoReset)
        tailNoReset
    · have irrelevant : serviceRelevant step = false := by
        exact Bool.eq_false_of_not_eq_true relevant
      simp only [System.runObservedFrom, List.filter_cons, irrelevant,
        Bool.false_eq_true, ↓reduceIte]
      have stutters := irrelevant_step step leftState headNoReset irrelevant leftWidth
      have nextSame := stutters.trans same
      exact ih
        (fragmentSystem.advanceRecovery step.event step.external leftState)
        rightState nextSame
        (advance_internal_width step leftState headNoReset) rightWidth tailNoReset

theorem run_observations_congr
    (leftSteps rightSteps : List System.ObservedRecoveryEvent)
    (leftState rightState : fragmentSystem.State)
    (same : SameServiceState leftState rightState)
    (observations : leftSteps.map observeService = rightSteps.map observeService)
    (leftNoReset : ∀ step ∈ leftSteps, step.event.resetIslands = [])
    (rightNoReset : ∀ step ∈ rightSteps, step.event.resetIslands = []) :
    SameServiceState
      (fragmentSystem.runObservedFrom leftState leftSteps)
      (fragmentSystem.runObservedFrom rightState rightSteps) := by
  induction leftSteps generalizing rightSteps leftState rightState with
  | nil =>
      cases rightSteps <;> simp_all [System.runObservedFrom]
  | cons leftStep leftRest ih =>
    cases rightSteps with
    | nil => simp at observations
    | cons rightStep rightRest =>
      simp only [List.map_cons, List.cons.injEq] at observations
      simp only [System.runObservedFrom]
      have nextSame := serviceObservation_step leftStep rightStep
        leftState rightState same
        (leftNoReset leftStep (by simp))
        (rightNoReset rightStep (by simp)) observations.1
      exact ih rightRest
        (fragmentSystem.advanceRecovery leftStep.event leftStep.external leftState)
        (fragmentSystem.advanceRecovery rightStep.event rightStep.external rightState)
        nextSame observations.2
        (fun step member => leftNoReset step (by simp [member]))
        (fun step member => rightNoReset step (by simp [member]))

theorem fragmentPredicateBoundedResponse
    (steps : List System.ObservedRecoveryEvent)
    (_valid : System.ValidObservedTrace fragmentSystem steps)
    (contract : PredicateServiceContract steps) :
    responseIs42 (fragmentSystem.runObserved steps) := by
  have resetWidth :
      ((fragmentSystem.reset.channel internal.name).width = 8) := by
    simp only [System.reset]
    rw [fragment_find_internal]
    rfl
  have erased := erase_irrelevant_from steps fragmentSystem.reset
    fragmentSystem.reset (SameServiceState.refl fragmentSystem.reset)
    resetWidth resetWidth contract.noReset
  have observed := run_observations_congr (steps.filter serviceRelevant)
    canonicalObservedService fragmentSystem.reset fragmentSystem.reset
    (SameServiceState.refl fragmentSystem.reset) contract.observations
    (fun step member => contract.noReset step (List.mem_filter.mp member).1)
    canonical_noReset
  have normalized := erased.trans observed
  have canonicalResponse :
      responseIs42 (fragmentSystem.runObserved canonicalObservedService) := by
    have valid : System.ValidObservedTrace fragmentSystem canonicalObservedService := by
      constructor <;> decide
    exact fragmentBoundedResponse canonicalObservedService valid
      ⟨rfl⟩
  exact (normalized.response_iff).mpr canonicalResponse

def predicateBoundedResponseProperty
    (steps : List System.ObservedRecoveryEvent)
    (final : fragmentSystem.State) : Prop :=
  PredicateServiceContract steps → responseIs42 final

theorem fragmentPredicateBoundedResponseTheorem :
    System.FiniteTraceTheorem fragmentSystem
      predicateBoundedResponseProperty := by
  intro steps valid contract
  exact fragmentPredicateBoundedResponse steps valid contract

def asynchronousPredicateBoundedResponse :=
  fragment.liftFragmentTheorem asynchronousProjection
    fragmentPredicateBoundedResponseTheorem

def monitoredPredicateBoundedResponse :=
  fragment.liftFragmentTheorem monitoredProjection
    fragmentPredicateBoundedResponseTheorem

theorem asynchronousResponseUnderPredicates
    (steps : List System.ObservedRecoveryEvent)
    (valid : System.ValidObservedTrace asynchronousParent steps)
    (contract : PredicateServiceContract
      (asynchronousProjection.projectTraceFrom asynchronousParent.reset steps)) :
    responseIs42 (asynchronousParent.runObserved steps) := by
  rcases asynchronousPredicateBoundedResponse steps valid with
    ⟨childFinal, projects, responds⟩
  have childResponse := responds contract
  have engineEq := projects.island engineIsland.name (by decide)
  simpa [responseIs42, engineEq] using childResponse

theorem monitoredResponseUnderPredicates
    (steps : List System.ObservedRecoveryEvent)
    (valid : System.ValidObservedTrace monitoredParent steps)
    (contract : PredicateServiceContract
      (monitoredProjection.projectTraceFrom monitoredParent.reset steps)) :
    responseIs42 (monitoredParent.runObserved steps) := by
  rcases monitoredPredicateBoundedResponse steps valid with
    ⟨childFinal, projects, responds⟩
  have childResponse := responds contract
  have engineEq := projects.island engineIsland.name (by decide)
  simpa [responseIs42, engineEq] using childResponse

end Tests.SystemProjection
