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

/-- The cycle-relevant portion of state projection. System time is omitted so
pure events on unrelated domains can be treated as stuttering steps without
discarding the ordinary time-aware `StateProjects` relation used by execution
theorems. -/
structure StateDataProjects (parent child : System)
    (parentState : parent.State) (childState : child.State) : Prop where
  island : ∀ name, (child.findIsland? name).isSome = true →
    childState.island name = parentState.island name
  channel : ∀ name width,
    (child.connections.find? fun connection =>
      connection.chan.name == name).isSome = true →
    (childState.channel name).asWidth width =
      (parentState.channel name).asWidth width

def StateProjects.data {parent child : System}
    {parentState : parent.State} {childState : child.State}
    (projects : StateProjects parent child parentState childState) :
    StateDataProjects parent child parentState childState :=
  ⟨projects.island, fun name width present => by
    rw [projects.channel name present]⟩

theorem restrictState_projects (child : System) {parent : System}
    (state : parent.State) :
    StateProjects parent child state (restrictState child state) := by
  refine { time := rfl, island := ?_, channel := ?_ }
  · intro name present
    simp only [restrictState]
    rw [if_pos present]
  · intro name present
    simp only [restrictState]
    rw [if_pos present]

namespace StateProjects

/-- Relational state projection is transitive when the inner projection
certifies that every child coordinate exists in its parent. -/
theorem trans {outer middle inner : System}
    {outerState : outer.State} {middleState : middle.State}
    {innerState : inner.State}
    (outerMiddle : StateProjects outer middle outerState middleState)
    (middleInner : StateProjects middle inner middleState innerState)
    (islandIncluded : ∀ name,
      (inner.findIsland? name).isSome = true →
        (middle.findIsland? name).isSome = true)
    (channelIncluded : ∀ name,
      (inner.connections.find? fun connection =>
        connection.chan.name == name).isSome = true →
      (middle.connections.find? fun connection =>
        connection.chan.name == name).isSome = true) :
    StateProjects outer inner outerState innerState := by
  refine { time := middleInner.time.trans outerMiddle.time,
           island := ?_, channel := ?_ }
  · intro name present
    exact (middleInner.island name present).trans
      (outerMiddle.island name (islandIncluded name present))
  · intro name present
    exact (middleInner.channel name present).trans
      (outerMiddle.channel name (channelIncluded name present))

/-- Recover the middle-to-inner relation from an outer-to-inner relation and
a canonical outer-to-middle projection. This is the key state fact needed by
state-dependent projection composition. -/
theorem through {outer middle inner : System}
    {outerState : outer.State} {middleState : middle.State}
    {innerState : inner.State}
    (outerInner : StateProjects outer inner outerState innerState)
    (outerMiddle : StateProjects outer middle outerState middleState)
    (islandIncluded : ∀ name,
      (inner.findIsland? name).isSome = true →
        (middle.findIsland? name).isSome = true)
    (channelIncluded : ∀ name,
      (inner.connections.find? fun connection =>
        connection.chan.name == name).isSome = true →
      (middle.connections.find? fun connection =>
        connection.chan.name == name).isSome = true) :
    StateProjects middle inner middleState innerState := by
  refine { time := outerInner.time.trans outerMiddle.time.symm,
           island := ?_, channel := ?_ }
  · intro name present
    exact (outerInner.island name present).trans
      (outerMiddle.island name (islandIncluded name present)).symm
  · intro name present
    exact (outerInner.channel name present).trans
      (outerMiddle.channel name (channelIncluded name present)).symm

end StateProjects

private theorem find?_append_eq_some {α : Type} (predicate : α → Bool)
    {xs ys : List α} {value : α}
    (found : xs.find? predicate = some value) :
    (xs ++ ys).find? predicate = some value := by
  induction xs with
  | nil => simp at found
  | cons head tail ih =>
      rw [List.find?_cons] at found
      change List.find? predicate (head :: (tail ++ ys)) = some value
      rw [List.find?_cons]
      cases matchHead : predicate head with
      | false =>
          simp only [matchHead] at found ⊢
          exact ih found
      | true =>
          simp only [matchHead] at found ⊢
          exact found

private theorem findSome?_append {α β : Type} (xs ys : List α)
    (select : α → Option β) :
    (xs ++ ys).findSome? select =
      match xs.findSome? select with
      | some value => some value
      | none => ys.findSome? select := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      cases selected : select head with
      | none => simp [selected, ih]
      | some value => simp [selected]

private theorem findSome?_congr {α β : Type} {xs : List α}
    {left right : α → Option β}
    (same : ∀ value ∈ xs, left value = right value) :
    xs.findSome? left = xs.findSome? right := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.findSome?_cons]
      rw [same head (by simp)]
      cases right head
      · exact ih (fun value member => same value (by simp [member]))
      · rfl

private theorem find?_eq_none_of_all_false {α : Type} {xs : List α}
    {predicate : α → Bool}
    (allFalse : ∀ value ∈ xs, predicate value = false) :
    xs.find? predicate = none := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.find?_cons, allFalse head (by simp)]
      exact ih (fun value member => allFalse value (by simp [member]))

private theorem findSome?_eq_none_of_all_none {α β : Type} {xs : List α}
    {select : α → Option β}
    (allNone : ∀ value ∈ xs, select value = none) :
    xs.findSome? select = none := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.findSome?_cons, allNone head (by simp)]
      exact ih (fun value member => allNone value (by simp [member]))

private theorem find?_append_of_none {α : Type} (predicate : α → Bool)
    {before after : List α} (beforeNone : before.find? predicate = none) :
    (before ++ after).find? predicate = after.find? predicate := by
  induction before with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.find?_cons] at beforeNone ⊢
      cases selected : predicate head with
      | false =>
          simp only [selected] at beforeNone
          simpa [selected] using ih beforeNone
      | true => simp [selected] at beforeNone

private theorem predicate_true_of_find?_eq_some {α : Type}
    {xs : List α} {predicate : α → Bool} {value : α}
    (found : xs.find? predicate = some value) : predicate value = true := by
  induction xs with
  | nil => simp at found
  | cons head tail ih =>
      simp only [List.find?_cons] at found
      cases selected : predicate head with
      | false => exact ih (by simpa [selected] using found)
      | true =>
          simp only [selected] at found
          cases found
          exact selected

/-- Structural provenance for the common fragment-parent construction path.
The child inventories remain an exact contiguous segment at any position;
preceding sibling inventory is checked not to collide with child identities or
to drive child inputs. Later connections may close the child's typed exports.
The Boolean endpoint condition is finite evidence that every child connection
names declared child islands.

This is intentionally narrower than arbitrary `ExecutionProjection`: it is
the automatically derivable case, while the latter remains the expert escape
hatch for adapters that transform state, events, or inputs. -/
structure StandardEmbedding (parent child : System) where
  islandPrefix : List SystemIsland
  islandSuffix : List SystemIsland
  connectionPrefix : List SystemConnection
  connectionSuffix : List SystemConnection
  islands : parent.islands = islandPrefix ++ child.islands ++ islandSuffix
  connections : parent.connections =
    connectionPrefix ++ child.connections ++ connectionSuffix
  islandPrefixDisjoint : islandPrefix.all (fun earlier =>
    child.islands.all fun nested => earlier.name != nested.name) = true
  connectionPrefixDisjoint : connectionPrefix.all (fun earlier =>
    child.connections.all fun nested =>
      earlier.chan.name != nested.chan.name) = true
  connectionPrefixOutside : connectionPrefix.all (fun earlier =>
    child.islands.all fun nested =>
      earlier.source != nested.name && earlier.sink != nested.name) = true
  childEndpoints : child.connections.all (fun connection =>
    (child.findIsland? connection.source).isSome &&
      (child.findIsland? connection.sink).isSome) = true
  boundary : fragmentBoundaryCheckB child parent = true
  resetPolicy : parent.resetPolicy = child.resetPolicy
  coordinated : child.resetPolicy = .coordinated
  clockCompatible : ∀ (events : List RecoveryEvent),
    parent.clockRel.accepts ((events.map (·.tick)).toArray) = true →
      child.clockRel.accepts ((events.map (·.tick)).toArray) = true

namespace StandardEmbedding

theorem islandPrefix_find_none {parent child : System}
    (embedding : StandardEmbedding parent child) {name : String}
    (present : (child.findIsland? name).isSome = true) :
    embedding.islandPrefix.find? (fun candidate =>
      candidate.name == name) = none := by
  cases found : child.findIsland? name with
  | none => simp [found] at present
  | some island =>
    apply find?_eq_none_of_all_false
    intro earlier member
    have islandMember : island ∈ child.islands :=
      List.mem_of_find?_eq_some found
    have allNested := List.all_eq_true.mp embedding.islandPrefixDisjoint
      earlier member
    have different := List.all_eq_true.mp allNested island islandMember
    have nameEq := System.findIsland?_name found
    exact Bool.eq_false_iff.mpr (by
      simpa [nameEq] using (bne_iff_ne.mp different))

theorem connectionPrefix_find_none {parent child : System}
    (embedding : StandardEmbedding parent child) {name : String}
    (present : (child.connections.find? fun candidate =>
      candidate.chan.name == name).isSome = true) :
    embedding.connectionPrefix.find? (fun candidate =>
      candidate.chan.name == name) = none := by
  cases found : child.connections.find? (fun candidate =>
      candidate.chan.name == name) with
  | none => simp [found] at present
  | some connection =>
    apply find?_eq_none_of_all_false
    intro earlier member
    have connectionMember : connection ∈ child.connections :=
      List.mem_of_find?_eq_some found
    have allNested := List.all_eq_true.mp embedding.connectionPrefixDisjoint
      earlier member
    have different := List.all_eq_true.mp allNested connection connectionMember
    have selected := predicate_true_of_find?_eq_some found
    have nameEq : connection.chan.name = name := beq_iff_eq.mp selected
    exact Bool.eq_false_iff.mpr (by
      simpa [nameEq] using (bne_iff_ne.mp different))

theorem findIsland_eq {parent child : System}
    (embedding : StandardEmbedding parent child) {name : String}
    {island : SystemIsland} (found : child.findIsland? name = some island) :
    parent.findIsland? name = some island := by
  change parent.islands.find? (fun candidate => candidate.name == name) = some island
  rw [embedding.islands]
  have present : (child.findIsland? name).isSome = true := by
    rw [found]
    rfl
  change child.islands.find? (fun candidate => candidate.name == name) = some island at found
  rw [List.append_assoc]
  rw [find?_append_of_none _ (embedding.islandPrefix_find_none present)]
  exact find?_append_eq_some _ found

theorem findConnection_eq {parent child : System}
    (embedding : StandardEmbedding parent child)
    {name : String} {connection : SystemConnection}
    (found : child.connections.find? (fun candidate =>
      candidate.chan.name == name) = some connection) :
    parent.connections.find? (fun candidate =>
      candidate.chan.name == name) = some connection := by
  rw [embedding.connections]
  rw [List.append_assoc]
  rw [find?_append_of_none _ (embedding.connectionPrefix_find_none (by simp [found]))]
  exact find?_append_eq_some _ found

private theorem endpointPresent {parent child : System}
    (embedding : StandardEmbedding parent child)
    (connection : SystemConnection) (member : connection ∈ child.connections) :
    (child.findIsland? connection.source).isSome = true ∧
      (child.findIsland? connection.sink).isSome = true := by
  have selected := List.all_eq_true.mp embedding.childEndpoints connection member
  simpa only [Bool.and_eq_true] using selected

theorem connectionInput_eq {parent child : System}
    (embedding : StandardEmbedding parent child)
    (parentState : parent.State) (childState : child.State)
    (represents : StateDataProjects parent child parentState childState)
    (event : NamedClockEvent) (connection : SystemConnection)
    (member : connection ∈ child.connections)
    (name inputName : String) (width : Nat) :
    child.connectionInput? event childState connection name inputName width =
      parent.connectionInput? event parentState connection name inputName width := by
  have endpoints := embedding.endpointPresent connection member
  cases sourceFound : child.findIsland? connection.source with
  | none => simp [sourceFound] at endpoints
  | some sourceIsland =>
    cases sinkFound : child.findIsland? connection.sink with
    | none => simp [sinkFound] at endpoints
    | some sinkIsland =>
      have parentSource := embedding.findIsland_eq sourceFound
      have parentSink := embedding.findIsland_eq sinkFound
      have sourceState := represents.island connection.source (by
        simp [sourceFound])
      have sinkState := represents.island connection.sink (by
        simp [sinkFound])
      have channelPresent :
          (child.connections.find? fun candidate =>
            candidate.chan.name == connection.chan.name).isSome = true := by
        exact List.find?_isSome.mpr ⟨connection, member, by simp⟩
      have queueState := represents.channel connection.chan.name
        connection.width channelPresent
      unfold System.connectionInput? System.connectionQueue System.connectionEvent
      rw [sourceFound, sinkFound, parentSource, parentSink]
      rw [sourceState, sinkState]
      exact queueState ▸ rfl

theorem childConnectionInputs_eq {parent child : System}
    (embedding : StandardEmbedding parent child)
    (parentState : parent.State) (childState : child.State)
    (represents : StateDataProjects parent child parentState childState)
    (event : NamedClockEvent) (name inputName : String) (width : Nat) :
    child.connections.findSome? (fun connection =>
      child.connectionInput? event childState connection name inputName width) =
    child.connections.findSome? (fun connection =>
      parent.connectionInput? event parentState connection name inputName width) := by
  apply findSome?_congr
  intro connection member
  exact embedding.connectionInput_eq parentState childState represents event
    connection member name inputName width

theorem connectionPrefixInputs_none {parent child : System}
    (embedding : StandardEmbedding parent child)
    (parentState : parent.State) (event : NamedClockEvent)
    (name inputName : String) (width : Nat)
    (present : (child.findIsland? name).isSome = true) :
    embedding.connectionPrefix.findSome? (fun connection =>
      parent.connectionInput? event parentState connection name inputName width) =
        none := by
  cases found : child.findIsland? name with
  | none => simp [found] at present
  | some island =>
    apply findSome?_eq_none_of_all_none
    intro earlier member
    have islandMember : island ∈ child.islands :=
      List.mem_of_find?_eq_some found
    have allNested := List.all_eq_true.mp embedding.connectionPrefixOutside
      earlier member
    have outside := List.all_eq_true.mp allNested island islandMember
    have outsideParts := Bool.and_eq_true_iff.mp outside
    have sourceDifferent : earlier.source ≠ island.name :=
      bne_iff_ne.mp outsideParts.1
    have sinkDifferent : earlier.sink ≠ island.name :=
      bne_iff_ne.mp outsideParts.2
    have nameEq := System.findIsland?_name found
    have sourceNe : name ≠ earlier.source := by
      simpa [nameEq] using sourceDifferent.symm
    have sinkNe : name ≠ earlier.sink := by
      simpa [nameEq] using sinkDifferent.symm
    simp [System.connectionInput?, sourceNe, sinkNe]

theorem islandInput_eq {parent child : System}
    (embedding : StandardEmbedding parent child)
    (parentState : parent.State) (childState : child.State)
    (represents : StateDataProjects parent child parentState childState)
    (event : NamedClockEvent) (external : String → InEnv) (name : String)
    (present : (child.findIsland? name).isSome = true) :
    child.islandInput event childState
        (parent.islandInput event parentState external) name =
      parent.islandInput event parentState external name := by
  funext inputName width
  unfold System.islandInput System.inputFor
  rw [embedding.connections]
  rw [List.append_assoc]
  rw [findSome?_append]
  rw [embedding.connectionPrefixInputs_none parentState event name inputName width
    present]
  rw [findSome?_append]
  rw [embedding.childConnectionInputs_eq parentState childState represents]
  cases selected : child.connections.findSome? (fun connection =>
      parent.connectionInput? event parentState connection name inputName width) with
  | none =>
    simp [selected,
      embedding.connectionPrefixInputs_none parentState event name inputName width
        present]
  | some value => simp [selected,
      embedding.connectionPrefixInputs_none parentState event name inputName width
        present]

theorem connectionResult_eq {parent child : System}
    (embedding : StandardEmbedding parent child)
    (parentState : parent.State) (childState : child.State)
    (represents : StateDataProjects parent child parentState childState)
    (event : NamedClockEvent) (connection : SystemConnection)
    (member : connection ∈ child.connections) :
    child.connectionResult event childState connection =
      parent.connectionResult event parentState connection := by
  have endpoints := embedding.endpointPresent connection member
  cases sourceFound : child.findIsland? connection.source with
  | none => simp [sourceFound] at endpoints
  | some sourceIsland =>
    cases sinkFound : child.findIsland? connection.sink with
    | none => simp [sinkFound] at endpoints
    | some sinkIsland =>
      have parentSource := embedding.findIsland_eq sourceFound
      have parentSink := embedding.findIsland_eq sinkFound
      have sourceState := represents.island connection.source (by
        simp [sourceFound])
      have sinkState := represents.island connection.sink (by
        simp [sinkFound])
      have channelPresent :
          (child.connections.find? fun candidate =>
            candidate.chan.name == connection.chan.name).isSome = true := by
        exact List.find?_isSome.mpr ⟨connection, member, by simp⟩
      have queueState := represents.channel connection.chan.name
        connection.width channelPresent
      unfold System.connectionResult System.connectionQueue System.connectionEvent
      rw [sourceFound, sinkFound, parentSource, parentSink]
      rw [sourceState, sinkState]
      exact queueState ▸ rfl

end StandardEmbedding

end System

namespace SystemBuilder

/-- Exact inventory position generated when a checked fragment is inserted
into a builder. The position remains valid when sibling inventory is appended;
it records values, not merely names or hashes. -/
structure FragmentPlacement (builder : SystemBuilder) (child : System) where
  islandPrefix : List SystemIsland
  islandSuffix : List SystemIsland
  connectionPrefix : List SystemConnection
  connectionSuffix : List SystemConnection
  islands : builder.islands = islandPrefix ++ child.islands ++ islandSuffix
  connections : builder.connections =
    connectionPrefix ++ child.connections ++ connectionSuffix

/-- The builder and exact placement produced by one fragment insertion. -/
structure FragmentInsertion (child : System) where
  builder : SystemBuilder
  placement : FragmentPlacement builder child

/-- Include a fragment and return exact, proof-carrying inventory provenance.
Unlike reconstructing a prefix after assembly, this works for every sibling
regardless of which fragment was inserted first. -/
def includeFragmentPlaced
    {Interface : System → Type u}
    {TheoremBundle : (system : System) → Interface system → Type u}
    (builder : SystemBuilder)
    (fragment : System.SystemFragment Interface TheoremBundle) :
    FragmentInsertion fragment.system where
  builder := builder.includeFragment fragment
  placement :=
    { islandPrefix := builder.islands
      islandSuffix := []
      connectionPrefix := builder.connections
      connectionSuffix := []
      islands := by
        simp [SystemBuilder.includeFragment, SystemBuilder.includeBlock,
          SystemBuilder.includeSystem, System.SystemFragment.system]
      connections := by
        simp [SystemBuilder.includeFragment, SystemBuilder.includeBlock,
          SystemBuilder.includeSystem, System.SystemFragment.system] }

/-- Appending a sibling moves that sibling into the suffix of an existing
placement; the original fragment's exact coordinates are unchanged. -/
def FragmentPlacement.afterIncludeFragment
    {builder : SystemBuilder} {child : System}
    (placement : FragmentPlacement builder child)
    {Interface : System → Type u}
    {TheoremBundle : (system : System) → Interface system → Type u}
    (sibling : System.SystemFragment Interface TheoremBundle) :
    FragmentPlacement (builder.includeFragment sibling) child where
  islandPrefix := placement.islandPrefix
  islandSuffix := placement.islandSuffix ++ sibling.system.islands
  connectionPrefix := placement.connectionPrefix
  connectionSuffix := placement.connectionSuffix ++ sibling.system.connections
  islands := by
    simp only [SystemBuilder.includeFragment, SystemBuilder.includeBlock,
      SystemBuilder.includeSystem, System.SystemFragment.system]
    rw [placement.islands]
    simp only [List.append_assoc]
  connections := by
    simp only [SystemBuilder.includeFragment, SystemBuilder.includeBlock,
      SystemBuilder.includeSystem, System.SystemFragment.system]
    rw [placement.connections]
    simp only [List.append_assoc]

/-- Seal builder-generated placement provenance into the semantic projection
certificate. The remaining arguments are finite collision/endpoint checks and
the already-explicit reset/clock compatibility contract. -/
def FragmentPlacement.toStandardEmbedding
    {builder : SystemBuilder} {child : System}
    (placement : FragmentPlacement builder child)
    (parentChecked : builder.check.isOk)
    (islandPrefixDisjoint : placement.islandPrefix.all (fun earlier =>
      child.islands.all fun nested => earlier.name != nested.name) = true)
    (connectionPrefixDisjoint : placement.connectionPrefix.all (fun earlier =>
      child.connections.all fun nested =>
        earlier.chan.name != nested.chan.name) = true)
    (connectionPrefixOutside : placement.connectionPrefix.all (fun earlier =>
      child.islands.all fun nested =>
        earlier.source != nested.name && earlier.sink != nested.name) = true)
    (childEndpoints : child.connections.all (fun connection =>
      (child.findIsland? connection.source).isSome &&
        (child.findIsland? connection.sink).isSome) = true)
    (boundary : System.fragmentBoundaryCheckB child
      (builder.certify parentChecked) = true)
    (resetPolicy : (builder.certify parentChecked).resetPolicy =
      child.resetPolicy)
    (coordinated : child.resetPolicy = .coordinated)
    (clockCompatible : ∀ (events : List System.RecoveryEvent),
      (builder.certify parentChecked).clockRel.accepts
          ((events.map (·.tick)).toArray) = true →
        child.clockRel.accepts ((events.map (·.tick)).toArray) = true) :
    System.StandardEmbedding (builder.certify parentChecked) child where
  islandPrefix := placement.islandPrefix
  islandSuffix := placement.islandSuffix
  connectionPrefix := placement.connectionPrefix
  connectionSuffix := placement.connectionSuffix
  islands := by simpa using placement.islands
  connections := by simpa using placement.connections
  islandPrefixDisjoint := islandPrefixDisjoint
  connectionPrefixDisjoint := connectionPrefixDisjoint
  connectionPrefixOutside := connectionPrefixOutside
  childEndpoints := childEndpoints
  boundary := boundary
  resetPolicy := resetPolicy
  coordinated := coordinated
  clockCompatible := clockCompatible

end SystemBuilder

namespace System

/-- A forward simulation from a parent System to an embedded child System.
`projectExternal` supplies the inputs that the child observes after its open
endpoints have been connected by the parent. -/
structure ExecutionProjection (parent child : System) where
  /-- A canonical child-shaped view of a parent state. It is used to compute
  state-dependent inputs when projections are composed; theorem statements
  continue to use the extensional `StateProjects` relation. -/
  projectState : parent.State → child.State := restrictState child
  projectState_projects : ∀ state,
    StateProjects parent child state (projectState state)
  islandIncluded : ∀ name,
    (child.findIsland? name).isSome = true →
      (parent.findIsland? name).isSome = true
  channelIncluded : ∀ name,
    (child.connections.find? fun connection =>
      connection.chan.name == name).isSome = true →
    (parent.connections.find? fun connection =>
      connection.chan.name == name).isSome = true
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

namespace StandardEmbedding

/-- Derive the ordinary identity-event execution projection from checked
fragment-builder provenance. All state/input/channel simulation obligations
are discharged here; a user of the standard include-and-close path supplies
only finite inventory evidence and the explicit clock/reset compatibility
premises stored in `StandardEmbedding`. -/
def toExecutionProjection {parent child : System}
    (embedding : StandardEmbedding parent child) :
    ExecutionProjection parent child where
  projectState_projects := fun state => restrictState_projects child state
  islandIncluded := by
    intro name present
    cases found : child.findIsland? name with
    | none => simp [found] at present
    | some island => simp [embedding.findIsland_eq found]
  channelIncluded := by
    intro name present
    cases found : child.connections.find? (fun connection =>
        connection.chan.name == name) with
    | none => simp [found] at present
    | some connection => simp [embedding.findConnection_eq found]
  projectEvent := id
  projectExternal := fun state observed =>
    parent.islandInput observed.event.tick state observed.external
  clockEvent := by intros; rfl
  resetEvent := by intros; rfl
  resetCompatible := by
    intro event valid
    have parentCoordinated : parent.resetPolicy = .coordinated :=
      embedding.resetPolicy.trans embedding.coordinated
    have none := recoveryEventOk_coordinated_noReset parent event
      parentCoordinated valid
    cases event with
    | mk tick resetIslands =>
        simp only at none
        subst resetIslands
        unfold System.recoveryEventOk
        rw [embedding.coordinated]
        rfl
  clockCompatible := by
    intro events valid
    simpa only [id_eq, List.map_id_fun] using
      embedding.clockCompatible events valid
  initial := by
    refine { time := rfl, island := ?_, channel := ?_ }
    · intro name present
      cases found : child.findIsland? name with
      | none => simp [found] at present
      | some island =>
          have parentFound := embedding.findIsland_eq found
          simp [System.reset, found, parentFound]
    · intro name present
      cases found : child.connections.find? (fun connection =>
          connection.chan.name == name) with
      | none => simp [found] at present
      | some connection =>
          have parentFound := embedding.findConnection_eq found
          simp [System.reset, found, parentFound]
  step := by
    intro parentState childState observed represents valid
    have parentCoordinated : parent.resetPolicy = .coordinated :=
      embedding.resetPolicy.trans embedding.coordinated
    have none := recoveryEventOk_coordinated_noReset parent observed.event
      parentCoordinated valid
    rw [parent.advanceRecovery_noReset observed.event observed.external
      parentState none]
    simp only [id_eq]
    rw [child.advanceRecovery_noReset observed.event
      (parent.islandInput observed.event.tick parentState observed.external)
      childState none]
    refine { time := by simp [System.advance, represents.time],
             island := ?_, channel := ?_ }
    · intro name present
      cases found : child.findIsland? name with
      | none => simp [found] at present
      | some island =>
          have parentFound := embedding.findIsland_eq found
          have stateEq := represents.island name (by simp [found])
          simp only [System.advance]
          rw [found, parentFound]
          rw [embedding.islandInput_eq parentState childState represents.data
            observed.event.tick observed.external name (by simp [found])]
          rw [stateEq]
    · intro name present
      cases found : child.connections.find? (fun connection =>
          connection.chan.name == name) with
      | none => simp [found] at present
      | some connection =>
          have member := List.mem_of_find?_eq_some found
          have parentFound := embedding.findConnection_eq found
          simp only [System.advance]
          rw [found, parentFound]
          dsimp only
          rw [embedding.connectionResult_eq parentState childState represents.data
            observed.event.tick connection member]

end StandardEmbedding

namespace ExecutionProjection

/-- Compose execution projections through a certified hierarchy. The
canonical state of the first projection supplies the state-dependent inputs
seen by the second; the public result remains the extensional fragment-state
relation. -/
def comp {outer middle inner : System}
    (outerMiddle : ExecutionProjection outer middle)
    (middleInner : ExecutionProjection middle inner) :
    ExecutionProjection outer inner where
  projectState := fun state =>
    middleInner.projectState (outerMiddle.projectState state)
  projectState_projects := by
    intro state
    exact StateProjects.trans
      (outerMiddle.projectState_projects state)
      (middleInner.projectState_projects (outerMiddle.projectState state))
      middleInner.islandIncluded middleInner.channelIncluded
  islandIncluded := by
    intro name present
    exact outerMiddle.islandIncluded name
      (middleInner.islandIncluded name present)
  channelIncluded := by
    intro name present
    exact outerMiddle.channelIncluded name
      (middleInner.channelIncluded name present)
  projectEvent := fun event =>
    middleInner.projectEvent (outerMiddle.projectEvent event)
  projectExternal := fun state observed =>
    middleInner.projectExternal (outerMiddle.projectState state)
      { event := outerMiddle.projectEvent observed.event
        external := outerMiddle.projectExternal state observed }
  clockEvent := by
    intro event clock
    rw [middleInner.clockEvent, outerMiddle.clockEvent]
  resetEvent := by
    intro event island
    rw [middleInner.resetEvent, outerMiddle.resetEvent]
  resetCompatible := by
    intro event valid
    exact middleInner.resetCompatible _
      (outerMiddle.resetCompatible event valid)
  clockCompatible := by
    intro events valid
    have middleValid := outerMiddle.clockCompatible events valid
    have innerValid := middleInner.clockCompatible
      (events.map outerMiddle.projectEvent) (by
        simpa [List.map_map] using middleValid)
    simpa [List.map_map] using innerValid
  initial := StateProjects.trans outerMiddle.initial middleInner.initial
    middleInner.islandIncluded middleInner.channelIncluded
  step := by
    intro outerState innerState observed outerInner valid
    let middleState := outerMiddle.projectState outerState
    have outerMiddleState : StateProjects outer middle outerState middleState :=
      outerMiddle.projectState_projects outerState
    have middleInnerState : StateProjects middle inner middleState innerState :=
      StateProjects.through outerInner outerMiddleState
        middleInner.islandIncluded middleInner.channelIncluded
    have middleValid := outerMiddle.resetCompatible observed.event valid
    have nextOuterMiddle := outerMiddle.step outerState middleState observed
      outerMiddleState valid
    have nextMiddleInner := middleInner.step middleState innerState
      { event := outerMiddle.projectEvent observed.event
        external := outerMiddle.projectExternal outerState observed }
      middleInnerState middleValid
    exact StateProjects.trans nextOuterMiddle nextMiddleInner
      middleInner.islandIncluded middleInner.channelIncluded

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

/-- Derive the standard parent-to-fragment projection when the parent retains
the fragment inventories at an exact, non-shadowed placement, closes its typed
endpoints, and preserves its coordinated reset and clock contract. Use
`ExecutionProjection` directly for state-transforming adapters and other
nonstandard embeddings. -/
def standardProjection
    {Interface : System → Type u}
    {TheoremBundle : (system : System) → Interface system → Type u}
    {parent : System}
    {fragment : _root_.Loom.Hw.System.SystemFragment Interface TheoremBundle}
    (embedding : System.StandardEmbedding parent fragment.system) :
    ExecutionProjection parent fragment :=
  embedding.toExecutionProjection

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
