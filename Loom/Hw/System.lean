-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Chan
import Loom.Hw.Semantics

/-!
# Typed channel assembly and multi-clock system semantics

`Design.cycle` is one synchronous step and stays exactly what it is. The
public `System` composes named `Design` **islands** using width-typed
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
existing `Design.par`/`Design.connect` semantics and retains clock data for the
multiclock semantics. Invalid endpoints, names, and depths fail closed during
assembly. Physical CDC choices belong to a separate realization layer.
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

/-- One intentionally open channel endpoint on a checked hierarchical block.
It has generated endpoint state/ports but no queue connection until a parent
connects it to the opposite endpoint carrying the same typed `Chan`. -/
structure SystemOpenEndpoint where
  width : Nat
  chan : Chan width
  island : String

/-- Reset behavior is declaration data rather than an unstated convention.
`coordinated` admits only the power-on reset. `independentFlush` additionally
admits named live island resets through `SystemRecovery`: every channel
incident to a reset island is flushed, reset dominates a simultaneous tick,
and traffic resumes from the empty channel epoch. It never preserves or
silently replays pre-reset messages. -/
inductive SystemResetPolicy where
  | coordinated
  | independentFlush
  deriving DecidableEq, Repr

/-! ### Executable named-clock relations

The relation consumes the same finite prefixes used by replay and bounded
checking.  Its semantic interpretation below admits an infinite schedule only
when every finite prefix is accepted.  This makes safety proofs insensitive to
how a runner happens to generate schedules and leaves progress assumptions
explicit in the selected relation.
-/

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

/-- Executable admissibility predicate shared by proof semantics, replay, and
bounded schedule enumeration.  `accepts` is intentionally a `Bool`: a rejected
prefix is data a runner can report, not a second proof-only schedule language. -/
structure ClockRel where
  accepts : SchedulePrefix → Bool
  /-- Acceptance is closed under removing a suffix.  This is the executable
  safety condition that makes rejection detectable at its first bad prefix. -/
  prefixClosed : ∀ first rest,
    accepts (first ++ rest) = true → accepts first = true

namespace ClockRel

/-- Every finite schedule is admissible. -/
def unconstrained : ClockRel where
  accepts := fun _ => true
  prefixClosed := by intros; rfl

/-- At most one named clock may tick in each event. This is useful for proofs
that deliberately linearize clock edges, but it is stronger than physical
asynchrony: unrelated clocks can have coincident edges. -/
def interleaved : ClockRel where
  accepts := fun events =>
    events.all fun event => event.clocks.eraseDups.length ≤ 1
  prefixClosed := by
    intro first rest accepted
    rw [Array.all_append] at accepted
    exact (Bool.and_eq_true_iff.mp accepted).1

/-- Physically unrelated clocks with arbitrary phase. Coincident edges are
admitted because a `NamedClockEvent` can tick several domains atomically.
This is definitionally the unconstrained finite-prefix relation; progress and
clock-availability assumptions remain separate from safety admissibility. -/
def asynchronous : ClockRel := unconstrained

/-- Two named clocks always tick together; other clocks remain unconstrained. -/
def aligned (left right : String) : ClockRel where
  accepts := fun events =>
    events.all fun event => event.fires left == event.fires right
  prefixClosed := by
    intro first rest accepted
    rw [Array.all_append] at accepted
    exact (Bool.and_eq_true_iff.mp accepted).1

/-- Materialize exactly the prefix consumed by executable checking. -/
def prefixOf (schedule : NamedSchedule) (length : Nat) : SchedulePrefix :=
  ((List.range length).map schedule).toArray

/-- Infinite-schedule interpretation used by `System.Invariant`: every finite
prefix must pass the executable relation. -/
def Admits (rel : ClockRel) (schedule : NamedSchedule) : Prop :=
  ∀ length, rel.accepts (prefixOf schedule length) = true

@[simp] theorem unconstrained_admits (schedule : NamedSchedule) :
    unconstrained.Admits schedule := by
  intro length
  rfl

end ClockRel

/-- Generator-friendly declaration builder.  It cannot be simulated, proved,
or emitted until `certify`/`assemble` produces a checked `System`. -/
structure SystemBuilder where
  islands : List SystemIsland := []
  connections : List SystemConnection := []
  openSources : List SystemOpenEndpoint := []
  openSinks : List SystemOpenEndpoint := []
  /-- Reset contracts of flattened checked children. Final assembly requires
  exact agreement with the parent policy; hierarchy may not silently
  reinterpret a child's reset theorem boundary. -/
  includedResetPolicies : List SystemResetPolicy := []
  clockRel : ClockRel := .unconstrained
  resetPolicy : SystemResetPolicy := .coordinated

namespace System

def empty : SystemBuilder := {}

def _root_.Loom.Hw.SystemBuilder.island (sys : SystemBuilder) (name : String) (design : Design)
    (clock : String := "clk") : SystemBuilder :=
  { sys with islands := sys.islands ++ [⟨name, clock, design⟩] }

def _root_.Loom.Hw.SystemBuilder.connect (sys : SystemBuilder) {width : Nat} (chan : Chan width)
    (source sink : String) : SystemBuilder :=
  { sys with connections := sys.connections ++ [⟨width, chan, source, sink⟩] }

/-- Generator-level hierarchical source export. Typed application wrappers
live in `Multiclock`; this lowering records the open endpoint and generates
its adapter exactly once. -/
def _root_.Loom.Hw.SystemBuilder.openSource (sys : SystemBuilder) {width : Nat}
    (chan : Chan width) (source : String) : SystemBuilder :=
  { sys with
    islands := sys.islands.map fun island =>
      if island.name = source then { island with design := chan.withSource island.design }
      else island
    openSources := sys.openSources ++ [⟨width, chan, source⟩] }

/-- Generator-level hierarchical sink export. -/
def _root_.Loom.Hw.SystemBuilder.openSink (sys : SystemBuilder) {width : Nat}
    (chan : Chan width) (sink : String) : SystemBuilder :=
  { sys with
    islands := sys.islands.map fun island =>
      if island.name = sink then { island with design := chan.withSink island.design }
      else island
    openSinks := sys.openSinks ++ [⟨width, chan, sink⟩] }

/-- Exact erased identity check used when a parent closes a typed exported
endpoint. -/
def openEndpointMatches {width : Nat}
    (endpoint : SystemOpenEndpoint) (chan : Chan width) (island : String) : Bool :=
  endpoint.chan.name == chan.name && endpoint.width == width &&
    endpoint.chan.depth == chan.depth && endpoint.chan.policy == chan.policy &&
    endpoint.island == island

/-- Close two previously generated hierarchical endpoints without generating
their endpoint adapters a second time. Final `SystemBuilder.check` verifies
that the selected endpoints and channel declaration agree exactly. -/
def _root_.Loom.Hw.SystemBuilder.connectOpen (sys : SystemBuilder) {width : Nat}
    (chan : Chan width) (source sink : String) : SystemBuilder :=
  { sys with
    connections := sys.connections ++ [⟨width, chan, source, sink⟩]
    openSources := sys.openSources.filter fun endpoint =>
      !openEndpointMatches endpoint chan source
    openSinks := sys.openSinks.filter fun endpoint =>
      !openEndpointMatches endpoint chan sink }

/-- Select the legal relative-clock schedules without changing island code. -/
def _root_.Loom.Hw.SystemBuilder.withClockRel (sys : SystemBuilder)
    (clockRel : ClockRel) : SystemBuilder :=
  { sys with clockRel }

/-- Opt into the explicit independently resettable, flush-on-reset contract.
The ordinary coordinated policy remains the default. -/
def _root_.Loom.Hw.SystemBuilder.withIndependentReset (sys : SystemBuilder) :
    SystemBuilder :=
  { sys with resetPolicy := .independentFlush }

def islandPrefix (name : String) := name ++ "__"
def adapterPrefix (name : String) := "__channel_" ++ name ++ "__"

def _root_.Loom.Hw.SystemBuilder.findIsland? (sys : SystemBuilder)
    (name : String) : Option SystemIsland :=
  sys.islands.find? fun island => island.name == name

/-- One derived crossing-inventory row. Optional clocks preserve a useful
diagnostic even before the fail-closed assembly check reports a missing
endpoint. -/
structure CrossingInfo where
  channel : String
  width : Nat
  depth : Nat
  policy : FullCoTickPolicy
  source : String
  sourceClock : Option String
  sink : String
  sinkClock : Option String
  deriving Repr

/-- Complete channel/crossing inventory, derived from the same declarations
used by semantics and lowering. -/
def _root_.Loom.Hw.SystemBuilder.crossingInventory (sys : SystemBuilder) : List CrossingInfo :=
  sys.connections.map fun connection =>
    { channel := connection.chan.name
      width := connection.width
      depth := connection.chan.depth
      policy := connection.chan.policy
      source := connection.source
      sourceClock := (sys.findIsland? connection.source).map (fun island => island.clock)
      sink := connection.sink
      sinkClock := (sys.findIsland? connection.sink).map (fun island => island.clock) }

private def hasReg (d : Design) (name : String) (width : Nat) : Bool :=
  d.regs.any fun reg => reg.name == name && reg.width == width

private def hasInput (d : Design) (name : String) (width : Nat) : Bool :=
  d.inputs.any fun input => input.name == name && input.width == width

private def declaredEndpointNames (sys : SystemBuilder) (islandName : String) : List String :=
  (sys.connections.flatMap fun connection =>
    let sourceNames := if connection.source == islandName then
      [connection.chan.sourceValidName, connection.chan.sourcePayloadName,
        connection.chan.sourceReadyName, connection.chan.sourceAcceptedName]
    else []
    let sinkNames := if connection.sink == islandName then
      [connection.chan.sinkPopName, connection.chan.sinkValidName,
        connection.chan.sinkPayloadName]
    else []
    sourceNames ++ sinkNames) ++
  (sys.openSources.flatMap fun endpoint =>
    if endpoint.island == islandName then
      [endpoint.chan.sourceValidName, endpoint.chan.sourcePayloadName,
        endpoint.chan.sourceReadyName, endpoint.chan.sourceAcceptedName]
    else []) ++
  (sys.openSinks.flatMap fun endpoint =>
    if endpoint.island == islandName then
      [endpoint.chan.sinkPopName, endpoint.chan.sinkValidName,
        endpoint.chan.sinkPayloadName]
    else [])

/-- Generated channel coordinates are a reserved namespace. An island cannot
smuggle in a generated-looking input/register unless the same checked System
declares that endpoint for the island. -/
private def hasOnlyDeclaredEndpoints (sys : SystemBuilder) (island : SystemIsland) : Bool :=
  let allowed := declaredEndpointNames sys island.name
  let names := island.design.regs.map (·.name) ++ island.design.inputs.map (·.name)
  let reserved := "__loom_chan_".toList
  names.all fun name => !(name.toList.take reserved.length == reserved) ||
    List.contains allowed name

def _root_.Loom.Hw.SystemBuilder.endpointOk (sys : SystemBuilder)
    (connection : SystemConnection) : Bool :=
  match sys.findIsland? connection.source, sys.findIsland? connection.sink with
  | some source, some sink =>
      hasReg source.design connection.chan.sourceValidName 1 &&
      hasReg source.design connection.chan.sourcePayloadName connection.width &&
      hasInput source.design connection.chan.sourceReadyName 1 &&
      hasInput source.design connection.chan.sourceAcceptedName 1 &&
      source.design.maxWritesTo connection.chan.sourceValidName 1 ≤ 2 &&
      hasReg sink.design connection.chan.sinkPopName 1 &&
      hasInput sink.design connection.chan.sinkValidName 1 &&
      hasInput sink.design connection.chan.sinkPayloadName connection.width &&
      sink.design.maxWritesTo connection.chan.sinkPopName 1 ≤ 2
  | _, _ => false

private def sourceEndpointOk (sys : SystemBuilder)
    (endpoint : SystemOpenEndpoint) : Bool :=
  match sys.findIsland? endpoint.island with
  | some source =>
      hasReg source.design endpoint.chan.sourceValidName 1 &&
      hasReg source.design endpoint.chan.sourcePayloadName endpoint.width &&
      hasInput source.design endpoint.chan.sourceReadyName 1 &&
      hasInput source.design endpoint.chan.sourceAcceptedName 1 &&
      source.design.maxWritesTo endpoint.chan.sourceValidName 1 ≤ 2
  | none => false

private def sinkEndpointOk (sys : SystemBuilder)
    (endpoint : SystemOpenEndpoint) : Bool :=
  match sys.findIsland? endpoint.island with
  | some sink =>
      hasReg sink.design endpoint.chan.sinkPopName 1 &&
      hasInput sink.design endpoint.chan.sinkValidName 1 &&
      hasInput sink.design endpoint.chan.sinkPayloadName endpoint.width &&
      sink.design.maxWritesTo endpoint.chan.sinkPopName 1 ≤ 2
  | none => false

/-- Fail-closed structural gate for the named declaration. -/
def _root_.Loom.Hw.SystemBuilder.check (sys : SystemBuilder) : Except String Unit := do
  if !sys.includedResetPolicies.all (· == sys.resetPolicy) then
    throw "included System reset policy differs from parent; rebuild or explicitly adapt the child contract"
  let islandNames := sys.islands.map (fun island => island.name)
  if islandNames.eraseDups.length != islandNames.length then
    throw "duplicate system island name"
  if islandNames.any (fun name => name.isEmpty) then
    throw "empty system island name"
  if sys.islands.any (fun island => island.clock.isEmpty) then
    throw "empty clock-domain name"
  for island in sys.islands do
    if !hasOnlyDeclaredEndpoints sys island then
      throw s!"island {island.name}: undeclared generated channel endpoint"
  let channelNames := sys.connections.map fun connection => connection.chan.name
  let openSourceNames := sys.openSources.map fun endpoint => endpoint.chan.name
  let openSinkNames := sys.openSinks.map fun endpoint => endpoint.chan.name
  if channelNames.eraseDups.length != channelNames.length then
    throw "duplicate channel connection"
  if openSourceNames.eraseDups.length != openSourceNames.length then
    throw "duplicate open source endpoint"
  if openSinkNames.eraseDups.length != openSinkNames.length then
    throw "duplicate open sink endpoint"
  if channelNames.any (openSourceNames.contains ·) ||
      channelNames.any (openSinkNames.contains ·) then
    throw "connected channel also remains exported"
  for connection in sys.connections do
    if connection.chan.name.isEmpty then throw "empty channel name"
    if connection.chan.depth == 0 then
      throw s!"channel {connection.chan.name}: depth must be positive"
    match sys.findIsland? connection.source with
    | some source =>
        if 2 < source.design.maxWritesTo connection.chan.sourceValidName 1 then
          throw s!"channel {connection.chan.name}: multiple sends may execute in one source tick; select one payload or use an explicit arbiter"
    | none => pure ()
    match sys.findIsland? connection.sink with
    | some sink =>
        if 2 < sink.design.maxWritesTo connection.chan.sinkPopName 1 then
          throw s!"channel {connection.chan.name}: multiple consumes may execute in one sink tick; select one consumer or use an explicit arbiter"
    | none => pure ()
    if !sys.endpointOk connection then
      throw s!"channel {connection.chan.name}: generated endpoint missing or malformed"
  for endpoint in sys.openSources do
    if endpoint.chan.name.isEmpty then throw "empty open source channel name"
    if endpoint.chan.depth == 0 then
      throw s!"channel {endpoint.chan.name}: depth must be positive"
    if !sourceEndpointOk sys endpoint then
      throw s!"channel {endpoint.chan.name}: open source endpoint missing or malformed"
  for endpoint in sys.openSinks do
    if endpoint.chan.name.isEmpty then throw "empty open sink channel name"
    if endpoint.chan.depth == 0 then
      throw s!"channel {endpoint.chan.name}: depth must be positive"
    if !sinkEndpointOk sys endpoint then
      throw s!"channel {endpoint.chan.name}: open sink endpoint missing or malformed"

end System

/-- The public system value is structurally valid by construction.  Its only
constructor is private; raw declaration data remains in `SystemBuilder`. -/
structure System where
  private mk ::
  private decl : SystemBuilder
  checked : decl.check.isOk

namespace System

/-- Turn generator-friendly declaration data into the type accepted by
proof- and emission-facing APIs. -/
def _root_.Loom.Hw.SystemBuilder.assemble (decl : SystemBuilder) : Except String System :=
  match h : decl.check with
  | .ok _ => pure ⟨decl, by rw [h]; rfl⟩
  | .error message => throw message

/-- Kernel-checked assembly for declarations whose gate can be discharged at
elaboration time. -/
def _root_.Loom.Hw.SystemBuilder.certify (decl : SystemBuilder)
    (checked : decl.check.isOk) : System :=
  ⟨decl, checked⟩

def islands (sys : System) : List SystemIsland := sys.decl.islands
def connections (sys : System) : List SystemConnection := sys.decl.connections
def openSources (sys : System) : List SystemOpenEndpoint := sys.decl.openSources
def openSinks (sys : System) : List SystemOpenEndpoint := sys.decl.openSinks
def clockRel (sys : System) : ClockRel := sys.decl.clockRel
def resetPolicy (sys : System) : SystemResetPolicy := sys.decl.resetPolicy
def findIsland? (sys : System) (name : String) : Option SystemIsland :=
  sys.decl.findIsland? name

theorem findIsland?_name {sys : System} {name : String} {island : SystemIsland}
    (found : sys.findIsland? name = some island) : island.name = name := by
  unfold findIsland? SystemBuilder.findIsland? at found
  have aux : ∀ (islands : List SystemIsland),
      islands.find? (fun candidate => candidate.name == name) = some island →
        island.name = name := by
    intro islands
    induction islands with
    | nil => simp
    | cons head tail ih =>
        intro result
        simp only [List.find?] at result
        split at result
        · rename_i matchHead
          cases result
          simpa using matchHead
        · exact ih result
  exact aux sys.decl.islands found
def crossingInventory (sys : System) : List CrossingInfo :=
  sys.decl.crossingInventory
def check (sys : System) : Except String Unit := sys.decl.check

@[simp] theorem islands_certify (decl : SystemBuilder) (checked : decl.check.isOk) :
    (decl.certify checked).islands = decl.islands := rfl

@[simp] theorem connections_certify (decl : SystemBuilder) (checked : decl.check.isOk) :
    (decl.certify checked).connections = decl.connections := rfl

@[simp] theorem openSources_certify (decl : SystemBuilder) (checked : decl.check.isOk) :
    (decl.certify checked).openSources = decl.openSources := rfl

@[simp] theorem openSinks_certify (decl : SystemBuilder) (checked : decl.check.isOk) :
    (decl.certify checked).openSinks = decl.openSinks := rfl

@[simp] theorem findIsland?_certify (decl : SystemBuilder) (checked : decl.check.isOk)
    (name : String) : (decl.certify checked).findIsland? name = decl.findIsland? name := rfl

@[simp] theorem check_isOk (sys : System) : sys.check.isOk := sys.checked

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
Design layer. A cross-clock abstract channel remains meaningful to scheduled
semantics but is deliberately refused by this synchronous lowering. -/
def elaborate (sys : System) : Except String Design := do
  sys.check
  if sys.connections.any (fun connection =>
      match sys.findIsland? connection.source, sys.findIsland? connection.sink with
      | some source, some sink => source.clock != sink.clock
      | _, _ => true) then
    throw "cross-clock channel requires a certified multiclock realization"
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

structure PackedQueue where
  width : Nat
  values : List (BitVec width)

/-- Recover a statically typed queue view. A width mismatch is impossible for
a checked connection and fails closed for diagnostic/inspection callers. -/
def PackedQueue.asWidth (queue : PackedQueue) (width : Nat) :
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

/-- Coordinated power-on/reset state. Every island and abstract channel resets
together. There is deliberately no `resetIsland` transition: unilateral live
reset is unsupported until a channel flush/recovery contract is selected and
proved. -/
def reset (sys : System) : sys.State where
  island := fun name => match sys.findIsland? name with
    | some island => island.design.reset
    | none => emptyState
  channel := fun name => match sys.connections.find? (fun connection =>
      connection.chan.name == name) with
    | some connection => packQueue (width := connection.width) []
    | none => packQueue (width := 0) []
  time := 0

def connectionQueue {sys : System} (state : sys.State)
    (connection : SystemConnection) :
    Chan.State connection.width :=
  (state.channel connection.chan.name).asWidth connection.width

/-- Typed view of one declared channel queue, used by reusable system-level
safety properties. -/
def channelState {sys : System} (state : sys.State)
    (connection : SystemConnection) : Chan.State connection.width :=
  connectionQueue state connection

/-- Expert proof/debug view of the endpoint request selected for one checked
connection at an atomic named-clock event. -/
def connectionEvent (sys : System) (event : NamedClockEvent)
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

/-- The exact abstract-channel result committed by `advance`. -/
def connectionResult (sys : System) (event : NamedClockEvent)
    (state : sys.State) (connection : SystemConnection) :
    Chan.Result connection.width :=
  connection.chan.step (connectionQueue state connection)
    (sys.connectionEvent event state connection)

/-- Stable proof/debug view of one connection at one atomic event. Application
proofs can reason about typed queue and transfer values without unfolding the
string/width dispatch used to construct island input environments. -/
structure ResolvedConnectionStep (sys : System) (connection : SystemConnection) where
  queue : Chan.State connection.width
  request : Chan.Event connection.width
  result : Chan.Result connection.width
  sourceReady : Bool
  sinkValid : Bool
  sinkPayload : BitVec connection.width

def resolveConnection (sys : System) (event : NamedClockEvent)
    (state : sys.State) (connection : SystemConnection) :
    ResolvedConnectionStep sys connection :=
  let queue := sys.channelState state connection
  let request := sys.connectionEvent event state connection
  let result := connection.chan.step queue request
  let sourceReady := (connection.chan.step queue
    { push := some 0, pop := request.pop }).accepted
  { queue, request, result, sourceReady
    sinkValid := !queue.isEmpty
    sinkPayload := queue.head?.getD 0 }

@[simp] theorem resolveConnection_queue (sys : System) (event : NamedClockEvent)
    (state : sys.State) (connection : SystemConnection) :
    (sys.resolveConnection event state connection).queue =
      sys.channelState state connection := rfl

@[simp] theorem resolveConnection_request (sys : System) (event : NamedClockEvent)
    (state : sys.State) (connection : SystemConnection) :
    (sys.resolveConnection event state connection).request =
      sys.connectionEvent event state connection := rfl

@[simp] theorem resolveConnection_result (sys : System) (event : NamedClockEvent)
    (state : sys.State) (connection : SystemConnection) :
    (sys.resolveConnection event state connection).result =
      sys.connectionResult event state connection := rfl

@[simp] theorem resolveConnection_sinkValid (sys : System)
    (event : NamedClockEvent) (state : sys.State)
    (connection : SystemConnection) :
    (sys.resolveConnection event state connection).sinkValid =
      !(sys.channelState state connection).isEmpty := rfl

@[simp] theorem resolveConnection_sinkPayload (sys : System)
    (event : NamedClockEvent) (state : sys.State)
    (connection : SystemConnection) :
    (sys.resolveConnection event state connection).sinkPayload =
      (sys.channelState state connection).head?.getD 0 := rfl

def boolValue (width : Nat) (h : width = 1) (value : Bool) : BitVec width :=
  h.symm ▸ if value then 1#1 else 0#1

/-- Expert proof view of the generated input driven by one connection. -/
def connectionInput? (sys : System) (event : NamedClockEvent)
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

/-- Complete generated-plus-external input valuation for one island.  This is
public so optimized certified runners can prove they consume the identical
input plan used by `System.advance`. -/
def inputFor (sys : System) (event : NamedClockEvent) (state : sys.State)
    (external : String → InEnv) (islandName : String) : InEnv :=
  fun inputName width =>
    (sys.connections.findSome? fun connection =>
      sys.connectionInput? event state connection islandName inputName width).getD
        (external islandName inputName width)

/-- Public proof/execution boundary for the inputs selected for one island at
an event. Certified System simulators use this exact derived valuation; they
do not reconstruct channel wiring in a second implementation. -/
def islandInput (sys : System) (event : NamedClockEvent) (state : sys.State)
    (external : String → InEnv) (islandName : String) : InEnv :=
  sys.inputFor event state external islandName

/-- One atomic named-clock event. Channel decisions and island inputs are all
computed from the pre-event state; selected islands and queues then commit
together. -/
def advance (sys : System) (event : NamedClockEvent) (external : String → InEnv)
    (state : sys.State) : sys.State where
  island := fun name => match sys.findIsland? name with
    | some island =>
        if event.fires island.clock then
          island.design.cycleOpen (sys.islandInput event state external name)
            (state.island name)
        else state.island name
    | none => state.island name
  channel := fun name => match sys.connections.find? (fun connection =>
      connection.chan.name == name) with
    | some connection => packQueue (sys.connectionResult event state connection).state
    | none => state.channel name
  time := state.time + 1

@[simp] theorem channelState_reset (sys : System) (connection : SystemConnection)
    (found : sys.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection) :
    channelState sys.reset connection = [] := by
  unfold channelState connectionQueue
  simp only [reset]
  rw [found]
  simp [PackedQueue.asWidth, packQueue]

@[simp] theorem channelState_advance (sys : System) (event : NamedClockEvent)
    (external : String → InEnv) (state : sys.State)
    (connection : SystemConnection)
    (found : sys.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection) :
    channelState (sys.advance event external state) connection =
      (sys.connectionResult event state connection).state := by
  unfold channelState connectionQueue
  simp only [advance]
  rw [found]
  simp [PackedQueue.asWidth, packQueue]

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
      island.design.cycleOpen (sys.islandInput event state external island.name)
        (state.island island.name) := by
  simp [advance, found, ticked]

def tsysUnder (sys : System) (schedule : NamedSchedule)
    (inputs : ExternalInputs) : Loom.TSys where
  S := sys.State
  init := (sys.reset = ·)
  step := fun state next =>
    next = sys.advance (schedule state.time) (inputs state.time) state

/-- List-level runner used by trace theorems; the public array runner below is
the same executable schedule representation converted without reinterpretation. -/
def runEventsFrom (sys : System) (inputs : ExternalInputs) :
    sys.State → List NamedClockEvent → sys.State
  | state, [] => state
  | state, event :: rest =>
      sys.runEventsFrom inputs
        (sys.advance event (inputs state.time) state) rest

/-- The abstract events seen by one declared channel during the same system
run.  Endpoint actions are read from each pre-event state. -/
def channelEventsFrom (sys : System) (inputs : ExternalInputs)
    (connection : SystemConnection) :
    sys.State → List NamedClockEvent → List (Chan.Event connection.width)
  | _, [] => []
  | state, event :: rest =>
      sys.connectionEvent event state connection ::
        sys.channelEventsFrom inputs connection
          (sys.advance event (inputs state.time) state) rest

/-- Replay a finite schedule prefix from an explicit state. The same event
data drives proofs and executable regressions. -/
def runPrefixFrom (sys : System) (events : SchedulePrefix)
    (inputs : ExternalInputs) (initial : sys.State) : sys.State :=
  sys.runEventsFrom inputs initial events.toList

/-- System execution projects exactly to the abstract queue runner for every
declared channel. -/
theorem channelState_runEventsFrom (sys : System) (inputs : ExternalInputs)
    (connection : SystemConnection)
    (found : sys.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection)
    (initial : sys.State) (events : List NamedClockEvent) :
    channelState (sys.runEventsFrom inputs initial events) connection =
      (connection.chan.runTrace (channelState initial connection)
        (sys.channelEventsFrom inputs connection initial events)).state := by
  induction events generalizing initial with
  | nil => rfl
  | cons event rest ih =>
      simp only [runEventsFrom, channelEventsFrom, Chan.runTrace]
      rw [ih]
      rw [channelState_advance sys event (inputs initial.time) initial connection found]
      rfl

/-- End-to-end channel conservation through named-system composition.  Across
any finite multiclock execution, the initial queue followed by values accepted
from the source equals values delivered to the sink followed by the final
queue.  No schedule or endpoint-specific proof is exposed to callers. -/
theorem channelTraceConservation (sys : System) (inputs : ExternalInputs)
    (connection : SystemConnection)
    (found : sys.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection)
    (initial : sys.State) (events : List NamedClockEvent) :
    let trace := sys.channelEventsFrom inputs connection initial events
    channelState initial connection ++
        (connection.chan.runTrace (channelState initial connection) trace).accepted =
      (connection.chan.runTrace (channelState initial connection) trace).delivered ++
        channelState (sys.runEventsFrom inputs initial events) connection := by
  dsimp only
  rw [channelState_runEventsFrom sys inputs connection found initial events]
  exact connection.chan.runTrace_conservation (channelState initial connection)
    (sys.channelEventsFrom inputs connection initial events)

/-- Replay a finite schedule prefix from system reset. -/
def runPrefix (sys : System) (events : SchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) : sys.State :=
  sys.runPrefixFrom events inputs sys.reset

/-- Relation-respecting replay boundary.  Debug tools get the rejected prefix
back as an error instead of silently testing a schedule outside the theorem. -/
def runPrefixChecked (sys : System) (events : SchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) : Except String sys.State :=
  if sys.clockRel.accepts events then
    pure (sys.runPrefix events inputs)
  else
    throw "schedule prefix rejected by ClockRel"

/-- A system invariant hides both the schedule and external-input trace.  It
quantifies over precisely the schedules admitted by the executable `ClockRel`
stored in the same named declaration used by replay and inventory generation. -/
def Invariant (sys : System) (property : sys.State → Prop) : Prop :=
  ∀ schedule inputs, sys.clockRel.Admits schedule →
    (sys.tsysUnder schedule inputs).Invariant property

/-- A property of the complete channel store.  Unlike `atChannel`, this may
relate any number of queues (for example, conservation across a pipeline or a
mutual-exclusion condition across two request channels) without mentioning
island state or clock schedules. -/
def atChannels {sys : System}
    (property : (String → PackedQueue) → Prop) (state : sys.State) : Prop :=
  property state.channel

/-- Schedule-free proof package for a possibly relational, cross-channel
safety property.  Its step obligation is executable and local to one named
clock event; `lift` below discharges all admitted schedules once and for all. -/
structure ChannelInvariant (sys : System)
    (property : (String → PackedQueue) → Prop) where
  reset : property sys.reset.channel
  preserved : ∀ event external state, property state.channel →
    property (sys.advance event external state).channel

namespace ChannelInvariant

/-- Cross-channel safety properties compose before they are lifted, so users
do not reopen schedules to combine independently proved channel contracts. -/
def and {sys : System} {left right : (String → PackedQueue) → Prop}
    (hLeft : ChannelInvariant sys left) (hRight : ChannelInvariant sys right) :
    ChannelInvariant sys (fun channels => left channels ∧ right channels) where
  reset := ⟨hLeft.reset, hRight.reset⟩
  preserved event external state holds :=
    ⟨hLeft.preserved event external state holds.1,
      hRight.preserved event external state holds.2⟩

end ChannelInvariant

/-- Lift a property over the whole channel graph to a system invariant over
every schedule admitted by the `ClockRel` stored in this named `System`. -/
theorem liftChannels (sys : System) {property : (String → PackedQueue) → Prop}
    (certificate : ChannelInvariant sys property) :
    sys.Invariant (atChannels property) := by
  intro schedule inputs _ state reachable
  induction reachable with
  | init initial =>
      rw [← initial]
      exact certificate.reset
  | step _ stepEq ih =>
      rename_i before after _
      rw [stepEq]
      exact certificate.preserved (schedule before.time) (inputs before.time) before ih

def atIsland {sys : System} (name : String) (property : St → Prop)
    (state : sys.State) : Prop :=
  property (state.island name)

def atChannel {sys : System} (connection : SystemConnection)
    (property : Chan.State connection.width → Prop) (state : sys.State) : Prop :=
  property (channelState state connection)

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
    (found : sys.findIsland? island.name = some island) {property : St → Prop}
    (localInvariant :
    (island.design.toAssumedOpenTSys (fun _ _ => True)).Invariant property) :
    sys.Invariant (atIsland island.name property) := by
  intro schedule inputs _ state reachable
  exact localInvariant _ (sys.island_reachable island found schedule inputs reachable)

/-- System safety facts compose pointwise without reopening schedules. -/
theorem invariantAnd (sys : System) {left right : sys.State → Prop}
    (hLeft : sys.Invariant left) (hRight : sys.Invariant right) :
    sys.Invariant (fun state => left state ∧ right state) := by
  intro schedule inputs admitted state reachable
  exact ⟨hLeft schedule inputs admitted state reachable,
    hRight schedule inputs admitted state reachable⟩

/-- Reusable cross-island safety theorem: every declared channel remains
within its capacity under every admitted schedule and every environment.  It
is proved once from the abstract queue transition and composes independently
of either endpoint's local invariant. -/
theorem channelCapacityInvariant (sys : System) (connection : SystemConnection)
    (found : sys.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection) :
    sys.Invariant (atChannel connection fun queue => queue.length ≤ connection.chan.depth) := by
  intro schedule inputs _ state reachable
  induction reachable with
  | init initial =>
      simp only [atChannel]
      rw [← initial, channelState_reset sys connection found]
      simp
  | step _ stepEq ih =>
      rename_i before after _
      simp only [atChannel] at ih ⊢
      rw [stepEq, channelState_advance sys _ _ before connection found]
      exact connection.chan.noOverflow _ _ ih

end System

end Loom.Hw
