-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Chan
import Loom.Hw.Semantics

/-!
# Typed channel assembly and multi-clock system semantics

`Design.cycle` is one synchronous step and stays exactly what it is. A
The public `System` composes named `Design` **islands** using width-typed
`Chan` handles. A replayable schedule decides which clock names tick at each
event. The earlier vector-indexed scheduling kernel remains available as
`ScheduledSystem`; it is useful for small proofs without assembly or channels.

The two load-bearing results, both **schedule-independent**:

* `advance_unticked` — an island that does not tick this event is unchanged.
  The per-event frame.
* `island_reachable` / `liftIsland` — the cumulative frame, and the payoff:
  **an island in a system only ever reaches states it could reach alone**, so
  any invariant proved of an island as an ordinary `Design` transports to the
  whole system, for *every* admissible schedule, in one line. This is the
  multi-clock generalization of `Frame.lean`'s single-cycle non-interference,
  and it is what keeps full-system proofs from scaling with the product of the
  domains: prove each island once, in plain `Design` land, and lift.

All-synchronous declarations lower to the existing `Design.par` and
`Design.connect` semantics. Cross-clock declarations execute against the
abstract bounded-channel semantics and deliberately cannot use that lowering:
physical toggle/FIFO implementations and their CDC refinement proofs remain a
separate backend boundary.
-/

namespace Loom.Hw

/-- Which islands tick at one clock event. A **set** of ticking domains, not a
single chosen one, so genuinely aligned edges — two islands clocked together —
are expressible, and a channel between co-ticking islands sees a same-event
exchange. -/
abbrev ClockEvent (n : Nat) := Fin n → Bool

/-- One clock event per time step. The `admissible` predicate below carves out
the legal schedules; the frame results here hold for *all* of them. -/
abbrev Schedule (n : Nat) := Nat → ClockEvent n

/-- A multi-clock system: `n` synchronous `Design` islands and a predicate
selecting admissible schedules (unconstrained by default — the frame theorems
never need it). -/
structure ScheduledSystem where
  n : Nat
  islands : Fin n → Design
  admissible : Schedule n → Prop := fun _ => True

/-- System state: one island state vector plus the event index. All Loom
designs share the state *type* `St`; islands do not alias because each holds
its own full `St`. -/
abbrev ScheduledSystem.State (sys : ScheduledSystem) := (Fin sys.n → St) × Nat

/-- Advance one event. Every ticking island runs its own `cycle`; the rest
hold. Reads see the pre-event vector and all ticked updates commit together,
consistent with `Design.cycle`'s own edge semantics. -/
def ScheduledSystem.advance (sys : ScheduledSystem) (e : ClockEvent sys.n)
    (st : Fin sys.n → St) : Fin sys.n → St :=
  fun i => if e i then (sys.islands i).cycle (st i) else st i

/-- The transition system under one fixed schedule — deterministic given the
schedule. The schedule quantifier lives in `System.Invariant`, not here. -/
def ScheduledSystem.tsysUnder (sys : ScheduledSystem) (sched : Schedule sys.n) : Loom.TSys where
  S := sys.State
  init := fun s => s.2 = 0 ∧ ∀ i, s.1 i = (sys.islands i).reset
  step := fun s s' => s'.2 = s.2 + 1 ∧ s'.1 = sys.advance (sched s.2) s.1

/-- A system invariant holds in every reachable state, under **every**
admissible schedule. The user never writes a schedule: "for all interleavings"
is what the definition *means*, exactly as "reads see pre-cycle state" is what
`Design.cycle` means. -/
def ScheduledSystem.Invariant (sys : ScheduledSystem) (P : (Fin sys.n → St) → Prop) : Prop :=
  ∀ sched, sys.admissible sched →
    (sys.tsysUnder sched).Invariant (fun s => P s.1)

/-! ## The frame -/

/-- Per-event frame: an island that does not tick is unchanged. -/
@[simp] theorem ScheduledSystem.advance_unticked (sys : ScheduledSystem) (e : ClockEvent sys.n)
    (st : Fin sys.n → St) {i : Fin sys.n} (h : e i = false) :
    sys.advance e st i = st i := by
  simp [ScheduledSystem.advance, h]

/-- A ticking island advances by exactly its own `cycle`. -/
@[simp] theorem ScheduledSystem.advance_ticked (sys : ScheduledSystem) (e : ClockEvent sys.n)
    (st : Fin sys.n → St) {i : Fin sys.n} (h : e i = true) :
    sys.advance e st i = (sys.islands i).cycle (st i) := by
  simp [ScheduledSystem.advance, h]

/-- **The core theorem.** In any reachable system state, under any schedule,
each island's state is reachable by that island *alone* — the system never
fabricates an island state the island could not reach on its own clock. -/
theorem ScheduledSystem.island_reachable (sys : ScheduledSystem) (sched : Schedule sys.n)
    {s : sys.State} (hr : (sys.tsysUnder sched).Reachable s) (i : Fin sys.n) :
    (sys.islands i).toTSys.Reachable (s.1 i) := by
  -- Generalize the reachable state so the induction motive is over it.
  suffices h : ∀ t, (sys.tsysUnder sched).Reachable t →
      (sys.islands i).toTSys.Reachable (t.1 i) from h s hr
  intro t ht
  induction ht with
  | init h =>
      rw [h.2 i]
      exact Loom.TSys.Reachable.init (show (sys.islands i).reset = _ from rfl)
  | step _ hstep ih =>
      rename_i a a' _
      obtain ⟨_, hadv⟩ := hstep
      rw [hadv]
      by_cases he : sched a.2 i = true
      · rw [sys.advance_ticked _ _ he]
        exact Loom.TSys.Reachable.step ih (show (sys.islands i).cycle (a.1 i) = _ from rfl)
      · rw [sys.advance_unticked _ _ (by simpa using he)]
        exact ih

/-- **The payoff.** An invariant of an island as an ordinary `Design` lifts to
a system invariant — for every admissible schedule — in one application. This
is the multi-clock `invariant_pullback`: island proofs are written in plain
`Design` land and never mention schedules, clocks, or the other islands. -/
theorem ScheduledSystem.liftIsland (sys : ScheduledSystem) (i : Fin sys.n) {Q : St → Prop}
    (hQ : (sys.islands i).toTSys.Invariant Q) :
    sys.Invariant (fun st => Q (st i)) := by
  intro sched _ s hr
  exact hQ _ (sys.island_reachable sched hr i)

/-- A conjunction of lifted island invariants is a system invariant — the
shape a full-system safety property takes before channel obligations are
added: `∧` of local invariants, each transported for free. -/
theorem ScheduledSystem.liftIsland₂ (sys : ScheduledSystem) (i j : Fin sys.n)
    {Q R : St → Prop}
    (hQ : (sys.islands i).toTSys.Invariant Q)
    (hR : (sys.islands j).toTSys.Invariant R) :
    sys.Invariant (fun st => Q (st i) ∧ R (st j)) := by
  intro sched hadm s hr
  exact ⟨sys.liftIsland i hQ sched hadm s hr, sys.liftIsland j hR sched hadm s hr⟩

/-! ## Typed named assembly

This is the ordinary-user surface. It lowers a one-clock assembly to the
existing `Design.par`/`Design.connect` semantics and retains clock/realization
data for the multiclock backend. Invalid endpoint, name, depth, or realization
combinations fail closed in `elaborate`.
-/

structure SystemIsland where
  name : String
  clock : String
  design : Design

structure SystemConnection where
  width : Nat
  chan : Chan width
  source : String
  sink : String

/-- Named system declaration. The only inter-island edge constructor is the
width-typed `connect`; there is intentionally no raw wire-crossing field. -/
structure System where
  islands : List SystemIsland := []
  connections : List SystemConnection := []

namespace System

def empty : System := {}

def island (sys : System) (name : String) (design : Design)
    (clock : String := "clk") : System :=
  { sys with islands := sys.islands ++ [⟨name, clock, design⟩] }

def connect (sys : System) {width : Nat} (chan : Chan width)
    (source sink : String) : System :=
  { sys with connections := sys.connections ++ [⟨width, chan, source, sink⟩] }

def islandPrefix (name : String) := name ++ "__"
def adapterPrefix (name : String) := "__channel_" ++ name ++ "__"

def findIsland? (sys : System) (name : String) : Option SystemIsland :=
  sys.islands.find? fun island => island.name == name

/-- One derived crossing-inventory row. Optional clocks preserve a useful
diagnostic even before the fail-closed assembly check reports a missing
endpoint. -/
structure CrossingInfo where
  channel : String
  width : Nat
  depth : Nat
  policy : FullCoTickPolicy
  realization : ChanRealization
  source : String
  sourceClock : Option String
  sink : String
  sinkClock : Option String
  deriving Repr

/-- Complete channel/crossing inventory, derived from the same declarations
used by semantics and lowering. -/
def crossingInventory (sys : System) : List CrossingInfo :=
  sys.connections.map fun connection =>
    { channel := connection.chan.name
      width := connection.width
      depth := connection.chan.depth
      policy := connection.chan.policy
      realization := connection.chan.realization
      source := connection.source
      sourceClock := (sys.findIsland? connection.source).map (fun island => island.clock)
      sink := connection.sink
      sinkClock := (sys.findIsland? connection.sink).map (fun island => island.clock) }

private def hasReg (d : Design) (name : String) (width : Nat) : Bool :=
  d.regs.any fun reg => reg.name == name && reg.width == width

private def hasInput (d : Design) (name : String) (width : Nat) : Bool :=
  d.inputs.any fun input => input.name == name && input.width == width

private def endpointOk (sys : System) (connection : SystemConnection) : Bool :=
  match sys.findIsland? connection.source, sys.findIsland? connection.sink with
  | some source, some sink =>
      hasReg source.design connection.chan.sourceValidName 1 &&
      hasReg source.design connection.chan.sourcePayloadName connection.width &&
      hasInput source.design connection.chan.sourceReadyName 1 &&
      hasInput source.design connection.chan.sourceAcceptedName 1 &&
      hasReg sink.design connection.chan.sinkPopName 1 &&
      hasInput sink.design connection.chan.sinkValidName 1 &&
      hasInput sink.design connection.chan.sinkPayloadName connection.width
  | _, _ => false

private def clocksOk (sys : System) (connection : SystemConnection) : Bool :=
  match sys.findIsland? connection.source, sys.findIsland? connection.sink with
  | some source, some sink =>
      match connection.chan.realization with
      | .synchronous => source.clock == sink.clock
      | .toggle | .asyncFifo => source.clock != sink.clock
  | _, _ => false

/-- Fail-closed structural gate for the named declaration. -/
def check (sys : System) : Except String Unit := do
  let islandNames := sys.islands.map (fun island => island.name)
  if islandNames.eraseDups.length != islandNames.length then
    throw "duplicate system island name"
  if islandNames.any (fun name => name.isEmpty) then
    throw "empty system island name"
  if sys.islands.any (fun island => island.clock.isEmpty) then
    throw "empty clock-domain name"
  let channelNames := sys.connections.map fun connection => connection.chan.name
  if channelNames.eraseDups.length != channelNames.length then
    throw "duplicate channel connection"
  for connection in sys.connections do
    if connection.chan.name.isEmpty then throw "empty channel name"
    if connection.chan.depth == 0 then
      throw s!"channel {connection.chan.name}: depth must be positive"
    if !sys.endpointOk connection then
      throw s!"channel {connection.chan.name}: generated endpoint missing or malformed"
    if !sys.clocksOk connection then
      throw s!"channel {connection.chan.name}: realization does not match endpoint clocks"

private def connectionWire? (connection : SystemConnection)
    (name : String) (width : Nat) : Option (Expr width) :=
  connection.chan.connectionWire
    (islandPrefix connection.source) (islandPrefix connection.sink)
    (adapterPrefix connection.chan.name) name width

private def wire? (connections : List SystemConnection)
    (name : String) (width : Nat) : Option (Expr width) :=
  connections.findSome? fun connection => connectionWire? connection name width

private def components (sys : System) : List Design :=
  (sys.islands.map fun island => island.design.prefixed (islandPrefix island.name)) ++
  (sys.connections.map fun connection =>
    connection.chan.adapter.prefixed (adapterPrefix connection.chan.name))

private def compose : List Design → Design
  | [] => { name := "empty", regs := [], mems := [], rules := [], outputs := [] }
  | first :: rest => rest.foldl Design.par first

private def composeChecked : List Design → Except String Design
  | [] => pure (compose [])
  | first :: rest => go first rest
  where
    go (acc : Design) : List Design → Except String Design
      | [] => pure acc
      | next :: remaining =>
          if acc.parOkB next then go (acc.par next) remaining
          else throw s!"component namespace collision: {acc.name} / {next.name}"

/-- Lower a valid all-synchronous system through the existing compositional
Design layer. Asynchronous realizations remain declarations for the scheduled
backend and are deliberately refused by this synchronous lowering. -/
def elaborate (sys : System) : Except String Design := do
  sys.check
  if sys.connections.any (fun connection =>
      connection.chan.realization != .synchronous) then
    throw "asynchronous channel requires the multiclock realization backend"
  let combined ← composeChecked sys.components
  let design := combined.connect (wire? sys.connections)
  pure design

/-- Safety of the actual lowered ordinary Design, useful for emission-facing
single-clock proofs. -/
def DesignInvariant (sys : System) (property : St → Prop) : Prop :=
  match sys.elaborate with
  | .ok design => design.toTSys.Invariant property
  | .error _ => False

/-! ### Executable named-clock semantics -/

/-- A replayable event names every clock that ticks atomically. Unlike a
function-valued event, this value can be printed directly into a failing test
artifact and replayed without a second schedule representation. -/
structure NamedClockEvent where
  clocks : List String
  deriving DecidableEq, Repr

def NamedClockEvent.fires (event : NamedClockEvent) (clock : String) : Bool :=
  event.clocks.contains clock

abbrev NamedSchedule := Nat → NamedClockEvent
abbrev SchedulePrefix := Array NamedClockEvent
abbrev ExternalInputs := Nat → String → InEnv

structure PackedQueue where
  width : Nat
  values : List (BitVec width)

private def PackedQueue.asWidth (queue : PackedQueue) (width : Nat) :
    List (BitVec width) :=
  if h : queue.width = width then h ▸ queue.values else []

private def packQueue {width : Nat} (values : List (BitVec width)) : PackedQueue :=
  ⟨width, values⟩

/-- State of the named system: independent island states, typed channel
queues, and an event counter. Names are safe keys because `System.check`
requires uniqueness before any theorem or run is accepted. -/
structure State (sys : System) where
  island : String → St
  channel : String → PackedQueue
  time : Nat

private def emptyState : St where
  regs := fun _ _ => 0
  mems := fun _ _ _ => 0

def reset (sys : System) : sys.State where
  island := fun name => match sys.findIsland? name with
    | some island => island.design.reset
    | none => emptyState
  channel := fun name => match sys.connections.find? (fun connection =>
      connection.chan.name == name) with
    | some connection => packQueue (width := connection.width) []
    | none => packQueue (width := 0) []
  time := 0

private def connectionQueue {sys : System} (state : sys.State)
    (connection : SystemConnection) :
    Chan.State connection.width :=
  (state.channel connection.chan.name).asWidth connection.width

private def connectionEvent (sys : System) (event : NamedClockEvent)
    (state : sys.State) (connection : SystemConnection) :
    Chan.Event connection.width :=
  let sourceTick := match sys.findIsland? connection.source with
    | some island => event.fires island.clock
    | none => false
  let sinkTick := match sys.findIsland? connection.sink with
    | some island => event.fires island.clock
    | none => false
  let sourceState := state.island connection.source
  let sinkState := state.island connection.sink
  let push := if sourceTick && connection.chan.sourceValid.eval sourceState != 0 then
      some (connection.chan.sourcePayload.eval sourceState) else none
  let pop := sinkTick &&
    (Expr.reg 1 connection.chan.sinkPopName).eval sinkState != 0
  { push, pop }

private def connectionResult (sys : System) (event : NamedClockEvent)
    (state : sys.State) (connection : SystemConnection) :
    Chan.Result connection.width :=
  connection.chan.step (connectionQueue state connection)
    (sys.connectionEvent event state connection)

private def boolValue (width : Nat) (h : width = 1) (value : Bool) : BitVec width :=
  h.symm ▸ if value then 1#1 else 0#1

private def connectionInput? (sys : System) (event : NamedClockEvent)
    (state : sys.State) (connection : SystemConnection)
    (islandName inputName : String) (width : Nat) : Option (BitVec width) :=
  let queue := connectionQueue state connection
  let action := sys.connectionEvent event state connection
  let result := connection.chan.step queue action
  let ready := (connection.chan.step queue
    { push := some 0, pop := action.pop }).accepted
  if islandName = connection.source &&
      inputName = connection.chan.sourceReadyName then
    if h : width = 1 then some (boolValue width h ready) else none
  else if islandName = connection.source &&
      inputName = connection.chan.sourceAcceptedName then
    if h : width = 1 then some (boolValue width h result.accepted) else none
  else if islandName = connection.sink &&
      inputName = connection.chan.sinkValidName then
    if h : width = 1 then some (boolValue width h (!queue.isEmpty)) else none
  else if islandName = connection.sink &&
      inputName = connection.chan.sinkPayloadName then
    if h : width = connection.width then
      some (h.symm ▸ queue.head?.getD 0)
    else none
  else none

private def inputFor (sys : System) (event : NamedClockEvent) (state : sys.State)
    (external : String → InEnv) (islandName : String) : InEnv :=
  fun inputName width =>
    (sys.connections.findSome? fun connection =>
      sys.connectionInput? event state connection islandName inputName width).getD
        (external islandName inputName width)

/-- One atomic named-clock event. Channel decisions and island inputs are all
computed from the pre-event state; selected islands and queues then commit
together. -/
def advance (sys : System) (event : NamedClockEvent) (external : String → InEnv)
    (state : sys.State) : sys.State where
  island := fun name => match sys.findIsland? name with
    | some island =>
        if event.fires island.clock then
          island.design.cycleOpen (sys.inputFor event state external name)
            (state.island name)
        else state.island name
    | none => state.island name
  channel := fun name => match sys.connections.find? (fun connection =>
      connection.chan.name == name) with
    | some connection => packQueue (sys.connectionResult event state connection).state
    | none => state.channel name
  time := state.time + 1

@[simp] theorem advance_island_unticked (sys : System) (event : NamedClockEvent)
    (external : String → InEnv) (state : sys.State) (island : SystemIsland)
    (found : sys.findIsland? island.name = some island)
    (unticked : event.fires island.clock = false) :
    (sys.advance event external state).island island.name = state.island island.name := by
  simp [advance, found, unticked]

@[simp] theorem advance_island_ticked (sys : System) (event : NamedClockEvent)
    (external : String → InEnv) (state : sys.State) (island : SystemIsland)
    (found : sys.findIsland? island.name = some island)
    (ticked : event.fires island.clock = true) :
    (sys.advance event external state).island island.name =
      island.design.cycleOpen (sys.inputFor event state external island.name)
        (state.island island.name) := by
  simp [advance, found, ticked]

def tsysUnder (sys : System) (schedule : NamedSchedule)
    (inputs : ExternalInputs) : Loom.TSys where
  S := sys.State
  init := (sys.reset = ·)
  step := fun state next =>
    next = sys.advance (schedule state.time) (inputs state.time) state

/-- Replay a finite schedule prefix from an explicit state. The same event
data drives proofs and executable regressions. -/
def runPrefixFrom (sys : System) (events : SchedulePrefix)
    (inputs : ExternalInputs) (initial : sys.State) : sys.State :=
  events.foldl (fun state event =>
    sys.advance event (inputs state.time) state) initial

/-- Replay a finite schedule prefix from system reset. -/
def runPrefix (sys : System) (events : SchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) : sys.State :=
  sys.runPrefixFrom events inputs sys.reset

/-- A system invariant hides both the schedule and external-input trace. It is
therefore valid for every relative clock rate and every environment unless a
future `ClockRel` or input contract is explicitly built into the System. -/
def Invariant (sys : System) (property : sys.State → Prop) : Prop :=
  sys.check.isOk ∧ ∀ schedule inputs, (sys.tsysUnder schedule inputs).Invariant property

def atIsland {sys : System} (name : String) (property : St → Prop)
    (state : sys.State) : Prop :=
  property (state.island name)

/-- Every reachable named-system island state is reachable in that island's
ordinary open semantics under arbitrary inputs. Channels completely mediate
the supplied input valuation; the global schedule otherwise disappears. -/
theorem island_reachable (sys : System) (island : SystemIsland)
    (found : sys.findIsland? island.name = some island)
    (schedule : NamedSchedule) (inputs : ExternalInputs) {state : sys.State}
    (reachable : (sys.tsysUnder schedule inputs).Reachable state) :
    (island.design.toAssumedOpenTSys (fun _ _ => True)).Reachable
      (state.island island.name) := by
  suffices h : ∀ target, (sys.tsysUnder schedule inputs).Reachable target →
      (island.design.toAssumedOpenTSys (fun _ _ => True)).Reachable
        (target.island island.name) from h state reachable
  intro target reachable
  induction reachable with
  | init initial =>
      rw [← initial]
      apply Loom.TSys.Reachable.init
      simp [reset, found]
  | step _ stepEq ih =>
      rename_i before after _
      rw [stepEq]
      by_cases ticked : (schedule before.time).fires island.clock = true
      · apply Loom.TSys.Reachable.step ih
        refine ⟨sys.inputFor (schedule before.time) before
          (inputs before.time) island.name, trivial, ?_⟩
        exact (sys.advance_island_ticked _ _ _ island found ticked).symm
      · simpa [sys.advance_island_unticked _ _ _ island found (by simpa using ticked)]
          using ih

/-- Public theorem-lifting combinator. Island authors prove an ordinary open
Design invariant; assembly transports it to every named-clock schedule. -/
theorem liftIsland (sys : System) (island : SystemIsland)
    (checked : sys.check.isOk)
    (found : sys.findIsland? island.name = some island) {property : St → Prop}
    (localInvariant :
      (island.design.toAssumedOpenTSys (fun _ _ => True)).Invariant property) :
    sys.Invariant (atIsland island.name property) := by
  constructor
  · exact checked
  · intro schedule inputs state reachable
    exact localInvariant _ (sys.island_reachable island found schedule inputs reachable)

/-- The degenerate one-island step is definitionally the existing semantics. -/
def singleStep (design : Design) (state : St) : St := design.cycle state

@[simp] theorem single_step (design : Design) (state : St) :
    singleStep design state = design.cycle state := rfl

end System

end Loom.Hw
