-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Syntax
import Mathlib.Data.Fin.Basic

/-!
# Technology-neutral asynchronous-queue storage

An asynchronous FIFO needs one independently clocked write port and one
independently clocked synchronous read port.  This file gives that leaf a
small digital contract without mentioning FPGA primitives, ASIC macros,
synthesis, or analog clock timing.

The contract deliberately leaves a simultaneous same-address read/write
unspecified.  FIFO protocol proofs must establish `CollisionFree` before they
may use the returned value.  Memory contents are arbitrary at reset; queue
pointers, rather than initialized data, determine which words are observable.
-/

namespace Loom.Hw.Cdc.AsyncQueueStorage

/-! ## Schedule-native ownership order

The port contract below only has to choose the value of a physical
same-edge/same-address collision.  Whether a FIFO is *allowed* to read a word,
or to reuse its slot, is a stronger protocol question.  It is stated here as
an explicit happens-before certificate rather than as a wall-clock aperture.
This keeps the theorem meaningful for arbitrary clock ratios and schedules.
-/

/-- A strict happens-before relation over indices in the executable global
schedule.  `before_event` makes it impossible to manufacture an ordering
edge between co-ticking actions in the same event. -/
structure HappensBefore where
  before : Nat → Nat → Prop
  transitive : ∀ {a b c}, before a b → before b c → before a c
  before_event : ∀ {a b}, before a b → a < b

namespace HappensBefore

theorem irreflexive (hb : HappensBefore) (event : Nat) : ¬hb.before event event := by
  intro impossible
  exact (Nat.lt_irrefl event) (hb.before_event impossible)

theorem asymmetric (hb : HappensBefore) {a b : Nat}
    (ordered : hb.before a b) : ¬hb.before b a := by
  intro reverse
  exact (Nat.lt_asymm (hb.before_event ordered) (hb.before_event reverse))

end HappensBefore

/-- Parameters that affect storage semantics and therefore must agree exactly
with a selected physical binding. -/
structure Parameters where
  width : Nat
  depth : Nat
  readLatency : Nat
  depthPositive : 0 < depth
  readLatencyPositive : 0 < readLatency

/-- One generation's ownership chain for a physical slot.  Publication and
acquisition are separate named events so a proof must exhibit an actual
synchronization path; numeric event order alone cannot discharge the fields.

The chain is deliberately two-sided:

`write → publish-write → acquire-write → read → publish-read → acquire-read → reuse`.

The final event is the next generation's write to the same address. -/
structure SlotGeneration (p : Parameters) (hb : HappensBefore) where
  address : Fin p.depth
  generation : Nat
  writeEvent : Nat
  publishWriteEvent : Nat
  acquireWriteEvent : Nat
  readEvent : Nat
  publishReadEvent : Nat
  acquireReadEvent : Nat
  reuseWriteEvent : Nat
  write_published : hb.before writeEvent publishWriteEvent
  publication_acquired : hb.before publishWriteEvent acquireWriteEvent
  acquired_before_read : hb.before acquireWriteEvent readEvent
  read_published : hb.before readEvent publishReadEvent
  readPublication_acquired : hb.before publishReadEvent acquireReadEvent
  acquired_before_reuse : hb.before acquireReadEvent reuseWriteEvent

namespace SlotGeneration

theorem write_before_read {p : Parameters} {hb : HappensBefore}
    (use : SlotGeneration p hb) : hb.before use.writeEvent use.readEvent :=
  hb.transitive (hb.transitive use.write_published use.publication_acquired)
    use.acquired_before_read

theorem read_before_reuse {p : Parameters} {hb : HappensBefore}
    (use : SlotGeneration p hb) : hb.before use.readEvent use.reuseWriteEvent :=
  hb.transitive (hb.transitive use.read_published use.readPublication_acquired)
    use.acquired_before_reuse

/-- The ownership proof itself rules out both dangerous co-tick cases.  This
is the bridge from the protocol-level happens-before statement to a RAM
leaf's much narrower collision precondition. -/
theorem write_ne_read_event {p : Parameters} {hb : HappensBefore}
    (use : SlotGeneration p hb) : use.writeEvent ≠ use.readEvent := by
  exact Nat.ne_of_lt (hb.before_event use.write_before_read)

theorem read_ne_reuse_event {p : Parameters} {hb : HappensBefore}
    (use : SlotGeneration p hb) : use.readEvent ≠ use.reuseWriteEvent := by
  exact Nat.ne_of_lt (hb.before_event use.read_before_reuse)

end SlotGeneration

/-- One global scheduled event.  A port command is active only when its
domain ticks in this event. -/
structure Event (p : Parameters) where
  writeTick : Bool := false
  write : Option (Fin p.depth × BitVec p.width) := none
  readTick : Bool := false
  read : Option (Fin p.depth) := none
  deriving DecidableEq, Repr

def Event.activeWrite {p : Parameters} (event : Event p) :
    Option (Fin p.depth × BitVec p.width) :=
  if event.writeTick then event.write else none

def Event.activeRead {p : Parameters} (event : Event p) : Option (Fin p.depth) :=
  if event.readTick then event.read else none

/-- The only behavior intentionally absent from the storage contract.  This
is a schedule predicate, not a wall-clock aperture. -/
def CollisionFree {p : Parameters} (event : Event p) : Prop :=
  match event.activeWrite, event.activeRead with
  | some (writeAddress, _), some readAddress => writeAddress ≠ readAddress
  | _, _ => True

instance {p : Parameters} (event : Event p) : Decidable (CollisionFree event) := by
  unfold CollisionFree
  cases writeEq : event.activeWrite with
  | none => exact isTrue trivial
  | some write =>
      rcases write with ⟨address, value⟩
      cases readEq : event.activeRead with
      | none => exact isTrue trivial
      | some read => exact inferInstance

/-- Reference digital state. `readPipeline` contains responses waiting for
future read-domain ticks; its empty reset is independent of memory contents. -/
structure ReferenceState (p : Parameters) where
  memory : Fin p.depth → BitVec p.width
  readPipeline : List (Option (BitVec p.width))

structure Result (State : Type) (p : Parameters) where
  state : State
  response : Option (BitVec p.width)

/-- Advance a positive-latency pipeline by one read-domain tick.  At latency
one, the newly sampled word is returned by the same abstract edge (that is,
after the edge); larger latencies retain exactly `latency - 1` pending slots. -/
def advancePipeline {width : Nat} (latency : Nat)
    (pending : List (Option (BitVec width)))
    (incoming : Option (BitVec width)) :
    Option (BitVec width) × List (Option (BitVec width)) :=
  let extended := pending ++ [incoming]
  if extended.length < latency then
    (none, extended)
  else
    (extended.head?.join, extended.drop 1)

def writeMemory {p : Parameters}
    (memory : Fin p.depth → BitVec p.width)
    (write : Option (Fin p.depth × BitVec p.width)) :
    Fin p.depth → BitVec p.width :=
  match write with
  | none => memory
  | some (address, value) => fun query =>
      if query = address then value else memory query

/-- Canonical storage semantics.  Reads sample pre-event memory.  That choice
is observable only on a forbidden collision; at distinct addresses pre/post
memory agree. -/
def referenceStep {p : Parameters} (state : ReferenceState p) (event : Event p) :
    Result (ReferenceState p) p :=
  let write := event.activeWrite
  let read := event.activeRead
  let sampled := read.map state.memory
  let (response, pipeline) :=
    if event.readTick then
      advancePipeline p.readLatency state.readPipeline sampled
    else
      (none, state.readPipeline)
  { state :=
      { memory := writeMemory state.memory write
        readPipeline := pipeline }
    response }

@[simp] theorem referenceStep_memory {p : Parameters}
    (state : ReferenceState p) (event : Event p) :
    (referenceStep state event).state.memory =
      writeMemory state.memory event.activeWrite := rfl

/-- An executable storage implementation and its checked refinement to the
technology-neutral reference semantics.  Correctness is required exactly on
the collision-free events that a client protocol promises to generate. -/
structure Implementation (p : Parameters) where
  State : Type
  reset : (Fin p.depth → BitVec p.width) → State
  step : State → Event p → Result State p
  Rep : ReferenceState p → State → Prop
  reset_refines : ∀ initial,
    Rep ⟨initial, []⟩ (reset initial)
  step_refines : ∀ {reference concrete} (event : Event p),
    CollisionFree event → Rep reference concrete →
    let expected := referenceStep reference event
    let actual := step concrete event
    Rep expected.state actual.state ∧ actual.response = expected.response

namespace Implementation

def runReference {p : Parameters} :
    ReferenceState p → List (Event p) → ReferenceState p
  | state, [] => state
  | state, event :: rest =>
      runReference (referenceStep state event).state rest

def run {p : Parameters} (implementation : Implementation p) :
    implementation.State → List (Event p) → implementation.State
  | state, [] => state
  | state, event :: rest =>
      implementation.run (implementation.step state event).state rest

/-- Parametric finite-run theorem used to show that the storage hypothesis is
both reusable and non-vacuous. -/
theorem run_refines {p : Parameters} (implementation : Implementation p)
    {reference : ReferenceState p} {concrete : implementation.State}
    (events : List (Event p))
    (collisionFree : ∀ event ∈ events, CollisionFree event)
    (rep : implementation.Rep reference concrete) :
    implementation.Rep
      (runReference reference events)
      (implementation.run concrete events) := by
  induction events generalizing reference concrete with
  | nil => simpa [runReference, run] using rep
  | cons event rest ih =>
      have eventSafe : CollisionFree event := collisionFree event (by simp)
      have one := implementation.step_refines event eventSafe rep
      exact ih
        (fun candidate member => collisionFree candidate (by simp [member])) one.1

end Implementation

/-- A completely theorem-covered executable leaf.  It is the semantic shape
that the later ordinary-Design register-bank implementation must compile to;
unlike FPGA/ASIC macro bindings it introduces no datasheet assumption. -/
def registerBank (p : Parameters) : Implementation p where
  State := ReferenceState p
  reset := fun initial => ⟨initial, []⟩
  step := referenceStep
  Rep := Eq
  reset_refines := by intros; rfl
  step_refines := by
    intro reference concrete event _ equal
    subst concrete
    exact ⟨rfl, rfl⟩

/-- Read-during-write behavior selected on a concrete two-port memory.  The
FIFO proof makes same-address collisions unreachable, so it is insensitive to
this choice, but the emitted choice is still recorded rather than hidden. -/
inductive WriteMode where
  | readFirst
  | writeFirst
  | noChange
  deriving DecidableEq, Repr

/-- Configuration values serialized into a structural primitive instance.
This data is separate from `Parameters` so agreement cannot be a convention.
`outputRegisters` records the primitive/macro pipeline setting whose effect
must already be reflected in the total `readLatency`. -/
structure Configuration where
  width : Nat
  depth : Nat
  readLatency : Nat
  writeMode : WriteMode
  outputRegisters : Nat
  deriving DecidableEq, Repr

def Parameters.configuration (p : Parameters)
    (writeMode : WriteMode := .readFirst) (outputRegisters : Nat := 0) : Configuration :=
  ⟨p.width, p.depth, p.readLatency, writeMode, outputRegisters⟩

/-- The only two admissible trust shapes for a storage binding. A portable
compiled implementation carries a proof; a technology macro carries exactly
one named external contract assumption. -/
inductive BindingBasis where
  | proved
  | assumed (assumption : String)
  deriving DecidableEq, Repr

/-- A target binding carries a proof that the instance configuration shipped
to the renderer is the exact contract instance used by the theorem.  A
physical leaf may additionally name its one external assumption. -/
structure Binding (p : Parameters) where
  name : String
  configuration : Configuration
  agreesWidth : configuration.width = p.width
  agreesDepth : configuration.depth = p.depth
  agreesReadLatency : configuration.readLatency = p.readLatency
  basis : BindingBasis

def Binding.externalAssumption {p : Parameters} (binding : Binding p) : Option String :=
  match binding.basis with
  | .proved => none
  | .assumed assumption => some assumption

/-- Fixed logical port contract presented to a target storage renderer. Clock
and signal names are supplied by structural assembly; these quantities define
their types and response timing. -/
structure PhysicalLeafInterface where
  width : Nat
  depth : Nat
  addressWidth : Nat
  readLatency : Nat
  deriving DecidableEq, Repr

def Parameters.physicalLeafInterface (p : Parameters) : PhysicalLeafInterface :=
  { width := p.width
    depth := p.depth
    addressWidth := Nat.log2 (p.depth - 1) + 1
    readLatency := p.readLatency }

/-- Artifact-boundary package for a target-refined storage leaf. The renderer
is fed the exact derived port interface and checked `Binding.configuration`;
it cannot receive a second, drifting width/depth/latency record. Correctness
of an assumed macro body is the binding's one named downstream obligation,
not a Loom theorem. -/
structure PhysicalLeaf (p : Parameters) where
  binding : Binding p
  moduleName : String
  renderModule : String → PhysicalLeafInterface → Configuration → String

def PhysicalLeaf.moduleText {p : Parameters} (leaf : PhysicalLeaf p) : String :=
  leaf.renderModule leaf.moduleName p.physicalLeafInterface
    leaf.binding.configuration

@[simp] theorem PhysicalLeaf.rendered_configuration_exact {p : Parameters}
    (leaf : PhysicalLeaf p) :
    leaf.moduleText = leaf.renderModule leaf.moduleName p.physicalLeafInterface
      leaf.binding.configuration := rfl

/-- The portable register-bank binding is unconditional. -/
def registerBankBinding (p : Parameters) : Binding p where
  name := "loom.register-bank"
  configuration := p.configuration
  agreesWidth := rfl
  agreesDepth := rfl
  agreesReadLatency := rfl
  basis := .proved

end Loom.Hw.Cdc.AsyncQueueStorage
