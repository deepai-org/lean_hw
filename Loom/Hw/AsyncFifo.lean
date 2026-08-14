-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ChanRefinement
import Loom.Hw.GrayCode
import Loom.Hw.AsyncQueueStorage
import Mathlib.Data.Nat.ModEq

/-!
# Concrete dual-clock FIFO model and channel refinement

This is the logical model of the stock Gray-pointer asynchronous FIFO.  It is
not an ideal queue: storage, source/read counters, and the two synchronized
remote-pointer views are explicit.  A synchronizer view may lag adversarially
but is clamped between its previous value and the current remote counter.  That
is the conservative digital consequence of sampling a Gray counter: the local
domain may see an older adjacent value, never a value from the future.

The implementation deliberately records only transfers the concrete endpoint
actually accepts.  A stale remote pointer can therefore delay a transfer, but
cannot create overflow, underflow, duplication, or reordering.  The refinement
below relates those concrete transfers to `Chan.step`.
-/

namespace Loom.Hw.Cdc.AsyncFifo

open Loom.Hw

variable {w : Nat}

/-- One executable global event. `readSample` and `writeSample` are adversarial
requests for the newly synchronized remote-pointer views; `sample` below
restricts them to the physically safe old-to-current interval. -/
structure Request (width : Nat) where
  /-- Common reset is represented by `reset`; these flags model independent
  release.  A held domain cannot transfer or advance its synchronizer. -/
  sourceReleased : Bool := true
  sinkReleased : Bool := true
  sourceTick : Bool := false
  sinkTick : Bool := false
  push : Option (BitVec width) := none
  pop : Bool := false
  readSample : Nat := 0
  writeSample : Nat := 0
  deriving DecidableEq, Repr

/-- Concrete state corresponding directly to a dual-port memory, local binary
pointers, and the decoded outputs of the two Gray synchronizer chains. -/
structure State (width : Nat) where
  storage : Nat → BitVec width
  writeCount : Nat
  readCount : Nat
  /-- First destination-domain synchronizer stage for the read pointer. -/
  readStage0 : Nat
  readSeenByWrite : Nat
  /-- First destination-domain synchronizer stage for the write pointer. -/
  writeStage0 : Nat
  writeSeenByRead : Nat

def reset (width : Nat) : State width where
  storage := fun _ => 0
  writeCount := 0
  readCount := 0
  readStage0 := 0
  readSeenByWrite := 0
  writeStage0 := 0
  writeSeenByRead := 0

/-- Common assertion is represented by starting at `reset`.  During the
release phase each domain may remain held for an arbitrary number of global
events, but once released it stays released. -/
structure ReleaseSchedule (requests : List (Request w)) : Prop where
  sourceMonotone : requests.Pairwise fun earlier later =>
    earlier.sourceReleased = true → later.sourceReleased = true
  sinkMonotone : requests.Pairwise fun earlier later =>
    earlier.sinkReleased = true → later.sinkReleased = true

/-- Executable adversarial synchronizer abstraction: retain the old view or
advance it by any amount up to the remote domain's current counter. -/
def sample (old current requested : Nat) : Nat :=
  max old (min requested current)

/-- Schedule-native validity witness for one synchronized pointer
observation. Sequence numbers are unbounded so monotonicity remains meaningful
across finite-width Gray-code wrap. `heldBySource` records that the observation
is a past source state; `notBeforePrevious` prevents the synchronizer from
moving backward in source-history order. -/
structure SampledPointerValidity (old current sampled code : Nat) : Prop where
  notBeforePrevious : old ≤ sampled
  heldBySource : sampled ≤ current
  grayCode : code = Gray.encode sampled

/-- Source-clock history used by the stronger trace-level sampling theorem.
The history is indexed by source ticks, not by the finite-width pointer value,
so `monotone` remains meaningful across Gray-code wrap.  A source edge may
hold or advance the logical counter by one; it may never skip a generation. -/
structure PointerHistory where
  countAt : Nat → Nat
  monotone : Monotone countAt
  step : ∀ tick, countAt (tick + 1) = countAt tick ∨
    countAt (tick + 1) = countAt tick + 1

/-- A synchronized observation names the actual source tick whose codeword it
contains.  Monotonicity is about this history position, not numeric comparison
of a wrapped hardware pointer.  `available` says the named source state is in
the causal past of the destination observation. -/
structure HistorySample (history : PointerHistory)
    (previousSourceTick observationTick sourceTick code : Nat) : Prop where
  notBeforePrevious : previousSourceTick ≤ sourceTick
  available : sourceTick ≤ observationTick
  codeword : code = Gray.encode (history.countAt sourceTick)

/-- Standalone sampled-pointer validity lemma.  Downstream occupancy,
collision-freedom, and unread-data proofs consume this named result rather
than rebuilding the source-history argument independently. -/
theorem sampledPointer_from_history (history : PointerHistory)
    {previousSourceTick observationTick sourceTick : Nat}
    (forward : previousSourceTick ≤ sourceTick)
    (past : sourceTick ≤ observationTick) :
    HistorySample history previousSourceTick observationTick sourceTick
      (Gray.encode (history.countAt sourceTick)) where
  notBeforePrevious := forward
  available := past
  codeword := rfl

/-- A history sample can never move backward in the source sequence, and is
an exact codeword the source held—not a bitwise mixture. -/
theorem HistorySample.valid_past_codeword {history : PointerHistory}
    {previousSourceTick observationTick sourceTick code : Nat}
    (sample : HistorySample history previousSourceTick observationTick sourceTick code) :
    previousSourceTick ≤ sourceTick ∧ sourceTick ≤ observationTick ∧
      code = Gray.encode (history.countAt sourceTick) :=
  ⟨sample.notBeforePrevious, sample.available, sample.codeword⟩

theorem sample_old_le (old current requested : Nat) :
    old ≤ sample old current requested := by
  simp [sample]

theorem sample_le_current {old current requested : Nat} (ordered : old ≤ current) :
    sample old current requested ≤ current := by
  simp [sample, ordered]

/-- Two distinct positions less than one ring circumference apart cannot
alias after reduction modulo the depth. This is the arithmetic core of slot
collision freedom. -/
private theorem mod_ne_of_ordered_distance {a b depth : Nat}
    (ordered : a ≤ b) (different : a ≠ b)
    (distance : b - a < depth) : a % depth ≠ b % depth := by
  intro equalMod
  have congruent : Nat.ModEq depth a b := equalMod
  have divides : depth ∣ b - a := (Nat.modEq_iff_dvd' ordered).mp congruent
  have differencePositive : 0 < b - a := Nat.sub_pos_of_lt (lt_of_le_of_ne ordered different)
  have depthLe : depth ≤ b - a := Nat.le_of_dvd differencePositive divides
  omega

/-- Load-bearing sampled-pointer lemma: every admitted observation denotes a
Gray codeword from the source's actual monotone counter history and never
rolls that history backward. -/
theorem sampledPointerValidity {old current requested : Nat}
    (ordered : old ≤ current) :
    SampledPointerValidity old current (sample old current requested)
      (Gray.encode (sample old current requested)) where
  notBeforePrevious := sample_old_le old current requested
  heldBySource := sample_le_current ordered
  grayCode := rfl

/-- Canonical logical source history of the FIFO counter.  Accepted transfers
advance by exactly one, so every generation from zero through the current
unbounded counter was an actual source state even when global-clock events
between transfers stuttered. -/
def generationHistory : PointerHistory where
  countAt := id
  monotone := fun _ _ ordered => ordered
  step := fun _ => Or.inr rfl

/-- Trace-facing form of `sampledPointerValidity`: the executable sampler's
result is an exact past generation codeword and its history position is
monotone. This is the named lemma consumed by later FIFO/storage proofs. -/
theorem sampledPointerHistoryValidity {old current requested : Nat}
    (ordered : old ≤ current) :
    HistorySample generationHistory old current (sample old current requested)
      (Gray.encode (sample old current requested)) :=
  sampledPointer_from_history generationHistory
    (sample_old_le old current requested) (sample_le_current ordered)

def accepted (c : Chan w) (state : State w) (request : Request w) :
    Option (BitVec w) :=
  if request.sourceReleased && request.sourceTick then
    if state.writeCount - state.readSeenByWrite < c.depth then request.push
    else none
  else none

def delivered (c : Chan w) (state : State w) (request : Request w) : Option (BitVec w) :=
  if request.sinkReleased && request.sinkTick && request.pop &&
      state.readCount < state.writeSeenByRead then
    some (state.storage (state.readCount % c.depth))
  else none

structure Result (width : Nat) where
  state : State width
  accepted : Option (BitVec width)
  delivered : Option (BitVec width)

/-- One simultaneous pair of source/destination edges. Decisions and the
delivered word use pre-event state; memory, pointers, and synchronizer views
commit together. -/
def step (c : Chan w) (state : State w) (request : Request w) : Result w :=
  let accepted := accepted c state request
  let delivered := delivered c state request
  let nextWrite := state.writeCount + if accepted.isSome then 1 else 0
  let nextRead := state.readCount + if delivered.isSome then 1 else 0
  let storage := match accepted with
    | some value => Function.update state.storage (state.writeCount % c.depth) value
    | none => state.storage
  { state :=
      { storage
        writeCount := nextWrite
        readCount := nextRead
        readStage0 :=
          if request.sourceReleased && request.sourceTick then
            sample state.readStage0 state.readCount request.readSample
          else state.readStage0
        readSeenByWrite :=
          if request.sourceReleased && request.sourceTick then
            state.readStage0
          else state.readSeenByWrite
        writeStage0 :=
          if request.sinkReleased && request.sinkTick then
            sample state.writeStage0 state.writeCount request.writeSample
          else state.writeStage0
        writeSeenByRead :=
          if request.sinkReleased && request.sinkTick then
            state.writeStage0
          else state.writeSeenByRead }
    accepted
    delivered }

@[simp] theorem step_storage (c : Chan w) (state : State w) (request : Request w) :
    (step c state request).state.storage =
      match accepted c state request with
      | some value => Function.update state.storage (state.writeCount % c.depth) value
      | none => state.storage := by
  rfl

/-- A source domain held in reset-release cannot mutate storage or either
local source-owned pointer. The peer may continue its own legal activity. -/
theorem source_held (c : Chan w) (state : State w) (request : Request w)
    (held : request.sourceReleased = false) :
    (step c state request).accepted = none ∧
      (step c state request).state.writeCount = state.writeCount ∧
      (step c state request).state.readSeenByWrite = state.readSeenByWrite ∧
      (step c state request).state.storage = state.storage := by
  simp [step, accepted, held]

/-- The dual held-domain fact: no read is authorized and neither
read-domain-owned pointer advances before destination release. -/
theorem sink_held (c : Chan w) (state : State w) (request : Request w)
    (held : request.sinkReleased = false) :
    (step c state request).delivered = none ∧
      (step c state request).state.readCount = state.readCount ∧
      (step c state request).state.writeSeenByRead = state.writeSeenByRead := by
  simp [step, delivered, held]

/-- On every concrete FIFO step, the write pointer's Gray code is unchanged
or changes in exactly one bit.  This connects the executable model's accepted
transfer to the generic Gray-adjacency theorem without making a claim about
analog synchronizer resolution. -/
theorem writeGray_step (c : Chan w) (state : State w) (request : Request w) :
    Gray.encode state.writeCount = Gray.encode (step c state request).state.writeCount ∨
      ∃ bit, Gray.encode state.writeCount ^^^
        Gray.encode (step c state request).state.writeCount = 2 ^ bit := by
  cases acceptedEq : accepted c state request with
  | none =>
      left
      simp [step, acceptedEq]
  | some value =>
      right
      simpa [step, acceptedEq] using Gray.succ_xor_oneBit state.writeCount

/-- The corresponding one-bit-or-stutter fact for successful reads. -/
theorem readGray_step (c : Chan w) (state : State w) (request : Request w) :
    Gray.encode state.readCount = Gray.encode (step c state request).state.readCount ∨
      ∃ bit, Gray.encode state.readCount ^^^
        Gray.encode (step c state request).state.readCount = 2 ^ bit := by
  cases deliveredEq : delivered c state request with
  | none =>
      left
      simp [step, deliveredEq]
  | some value =>
      right
      simpa [step, deliveredEq] using Gray.succ_xor_oneBit state.readCount

/-- The abstract event contains successful physical transfers, not merely
requests that a stale full/empty flag may conservatively stall. -/
def observedEvent (c : Chan w) (state : State w) (request : Request w) : Chan.Event w :=
  { push := accepted c state request
    pop := (delivered c state request).isSome }

/-- Representation relation between the concrete dual-clock state and the
abstract FIFO sequence. The synchronized views are explicitly conservative. -/
structure Rep (c : Chan w) (queue : Chan.State w) (state : State w) : Prop where
  positiveDepth : 0 < c.depth
  countersOrdered : state.readCount ≤ state.writeCount
  bounded : state.writeCount - state.readCount ≤ c.depth
  writerViewBounded : state.writeCount - state.readSeenByWrite ≤ c.depth
  lengthEq : queue.length = state.writeCount - state.readCount
  readStagesOrdered : state.readSeenByWrite ≤ state.readStage0
  readStageSafe : state.readStage0 ≤ state.readCount
  readViewSafe : state.readSeenByWrite ≤ state.readCount
  writeStagesOrdered : state.writeSeenByRead ≤ state.writeStage0
  writeStageSafe : state.writeStage0 ≤ state.writeCount
  writeViewLower : state.readCount ≤ state.writeSeenByRead
  writeViewSafe : state.writeSeenByRead ≤ state.writeCount
  storage : ∀ (offset : Nat) (present : offset < queue.length),
    state.storage ((state.readCount + offset) % c.depth) = queue[offset]

theorem rep_reset (c : Chan w) (positiveDepth : 0 < c.depth) :
    Rep c [] (reset w) where
  positiveDepth := positiveDepth
  countersOrdered := by simp [reset]
  bounded := by simp [reset]
  writerViewBounded := by simp [reset]
  lengthEq := by simp [reset]
  readStagesOrdered := by simp [reset]
  readStageSafe := by simp [reset]
  readViewSafe := by simp [reset]
  writeStagesOrdered := by simp [reset]
  writeStageSafe := by simp [reset]
  writeViewLower := by simp [reset]
  writeViewSafe := by simp [reset]
  storage := by simp

/-- A concrete source acceptance implies genuine abstract space even when the
writer's synchronized read pointer is stale. -/
theorem space_of_accepted (c : Chan w) (queue : Chan.State w)
    (state : State w) (request : Request w) (rep : Rep c queue state)
    (didAccept : (accepted c state request).isSome = true) :
    queue.length < c.depth := by
  unfold accepted at didAccept
  split at didAccept
  · rename_i sourceTick
    split at didAccept
    · rename_i space
      have occupancyLe :=
        Nat.sub_le_sub_left rep.readViewSafe state.writeCount
      rw [rep.lengthEq]
      omega
    · simp at didAccept
  · simp at didAccept

/-- A concrete delivery implies that the abstract queue is nonempty; a stale
write-pointer view can suppress a read but can never authorize underflow. -/
theorem nonempty_of_delivered (c : Chan w) (queue : Chan.State w)
    (state : State w) (request : Request w) (rep : Rep c queue state)
    (didDeliver : (delivered c state request).isSome = true) :
    0 < queue.length := by
  unfold delivered at didDeliver
  split at didDeliver <;> simp_all
  rename_i enabled
  have pointerLt : state.readCount < state.writeSeenByRead := enabled.2
  have actualLt : state.readCount < state.writeCount :=
    lt_of_lt_of_le pointerLt rep.writeViewSafe
  rw [rep.lengthEq]
  exact Nat.sub_pos_of_lt actualLt

/-- If both endpoints transfer in one logical event, the physical ring ports
address different slots. In particular, a full queue cannot rely on a RAM's
read-during-write mode to implement exchange: the writer's conservative
synchronized read view refuses that push until genuine space is visible. -/
theorem accepted_delivered_addresses_distinct (c : Chan w)
    (queue : Chan.State w) (state : State w) (request : Request w)
    (rep : Rep c queue state)
    (didAccept : (accepted c state request).isSome = true)
    (didDeliver : (delivered c state request).isSome = true) :
    state.readCount % c.depth ≠ state.writeCount % c.depth := by
  have nonempty := nonempty_of_delivered c queue state request rep didDeliver
  have room := space_of_accepted c queue state request rep didAccept
  have strictCounters : state.readCount < state.writeCount := by
    rw [rep.lengthEq] at nonempty
    exact Nat.sub_pos_iff_lt.mp nonempty
  have distance : state.writeCount - state.readCount < c.depth := by
    rw [← rep.lengthEq]
    exact room
  exact mod_ne_of_ordered_distance (Nat.le_of_lt strictCounters)
    (Nat.ne_of_lt strictCounters) distance

/-- Storage contract instance selected by a channel. The executable FIFO
currently consumes a one-edge synchronous response; deeper physical leaves
insert their declared response pipeline behind the same ownership theorem. -/
def storageParameters (c : Chan w) (positiveDepth : 0 < c.depth) :
    AsyncQueueStorage.Parameters :=
  { width := w
    depth := c.depth
    readLatency := 1
    depthPositive := positiveDepth
    readLatencyPositive := by decide }

/-- The actual finite-ring port operation generated by one FIFO event. Only
successful transfers activate a storage port. -/
def storageEvent (c : Chan w) (positiveDepth : 0 < c.depth)
    (state : State w) (request : Request w) :
    AsyncQueueStorage.Event (storageParameters c positiveDepth) :=
  let write := (accepted c state request).map fun value =>
    (⟨state.writeCount % c.depth, Nat.mod_lt _ positiveDepth⟩, value)
  let read := if (delivered c state request).isSome then
    some ⟨state.readCount % c.depth, Nat.mod_lt _ positiveDepth⟩ else none
  { writeTick := write.isSome
    write
    readTick := read.isSome
    read }

@[simp] theorem storageEvent_activeWrite (c : Chan w) (positiveDepth : 0 < c.depth)
    (state : State w) (request : Request w) :
    (storageEvent c positiveDepth state request).activeWrite =
      (accepted c state request).map (fun value =>
        (⟨state.writeCount % c.depth, Nat.mod_lt _ positiveDepth⟩, value)) := by
  cases acceptedEq : accepted c state request <;>
    simp [storageEvent, AsyncQueueStorage.Event.activeWrite, acceptedEq]

/-- The FIFO discharges the storage leaf's collision precondition from its
queue representation invariant; it is not assumed from a clock ratio or RAM
write-mode setting. -/
theorem storageEvent_collisionFree (c : Chan w) (queue : Chan.State w)
    (state : State w) (request : Request w) (rep : Rep c queue state) :
    AsyncQueueStorage.CollisionFree
      (storageEvent c rep.positiveDepth state request) := by
  cases acceptEq : accepted c state request with
  | none => simp [storageEvent, AsyncQueueStorage.CollisionFree,
      AsyncQueueStorage.Event.activeWrite, acceptEq]
  | some value =>
      cases deliverEq : delivered c state request with
      | none => simp [storageEvent, AsyncQueueStorage.CollisionFree,
          AsyncQueueStorage.Event.activeWrite, AsyncQueueStorage.Event.activeRead,
          acceptEq, deliverEq]
      | some deliveredValue =>
          have distinct := accepted_delivered_addresses_distinct c queue state request rep
            (by simp [acceptEq]) (by simp [deliverEq])
          simp [storageEvent, AsyncQueueStorage.CollisionFree,
            AsyncQueueStorage.Event.activeWrite, AsyncQueueStorage.Event.activeRead,
            acceptEq, deliverEq, distinct.symm]

/-- Any storage implementation satisfying the technology-neutral contract
therefore takes the same finite-ring step as the reference leaf on every FIFO
event. This is the parametric handoff point used by the eventual composed FIFO
refinement; no primitive, vendor, or synthesis behavior appears here. -/
theorem storageImplementation_step (c : Chan w) (queue : Chan.State w)
    (state : State w) (request : Request w) (fifoRep : Rep c queue state)
    (implementation : AsyncQueueStorage.Implementation
      (storageParameters c fifoRep.positiveDepth))
    {reference : AsyncQueueStorage.ReferenceState
      (storageParameters c fifoRep.positiveDepth)}
    {concrete : implementation.State}
    (storageRep : implementation.Rep reference concrete) :
    let event := storageEvent c fifoRep.positiveDepth state request
    let expected := AsyncQueueStorage.referenceStep reference event
    let actual := implementation.step concrete event
    implementation.Rep expected.state actual.state ∧
      actual.response = expected.response := by
  exact implementation.step_refines _
    (storageEvent_collisionFree c queue state request fifoRep) storageRep

/-- When a concrete read succeeds, its memory word is exactly the abstract
queue head. -/
theorem delivered_eq_head (c : Chan w) (queue : Chan.State w)
    (state : State w) (request : Request w) (rep : Rep c queue state)
    {value : BitVec w} (didDeliver : delivered c state request = some value) :
    queue.head? = some value := by
  have nonempty : 0 < queue.length :=
    nonempty_of_delivered c queue state request rep (by simp [didDeliver])
  have stored := rep.storage 0 nonempty
  unfold delivered at didDeliver
  split at didDeliver
  · simp only [Option.some.injEq] at didDeliver
    have atHead : queue[0] = value := by
      rw [← didDeliver]
      simpa using stored.symm
    simpa [List.head?_eq_getElem?, List.getElem?_eq_getElem nonempty] using atHead
  · simp at didDeliver

/-- Successful concrete transfers make exactly the same accept/deliver
decision as the abstract queue event that records those transfers. -/
theorem transfer_refines (c : Chan w) (queue : Chan.State w)
    (state : State w) (request : Request w) (rep : Rep c queue state) :
    let physical := step c state request
    let abstract := c.step queue (observedEvent c state request)
    abstract.accepted = physical.accepted.isSome ∧
      abstract.delivered = physical.delivered := by
  dsimp only
  change (c.step queue
      { push := accepted c state request,
        pop := (delivered c state request).isSome }).accepted =
        (accepted c state request).isSome ∧
    (c.step queue
      { push := accepted c state request,
        pop := (delivered c state request).isSome }).delivered =
        delivered c state request
  cases acceptedEq : accepted c state request with
  | none =>
      cases deliveredEq : delivered c state request with
      | none => simp [Chan.step]
      | some value =>
          have head := delivered_eq_head c queue state request rep deliveredEq
          cases queue with
          | nil => simp at head
          | cons first rest =>
              simp only [List.head?_cons, Option.some.injEq] at head
              subst value
              simp [Chan.step]
  | some value =>
      have space := space_of_accepted c queue state request rep (by simp [acceptedEq])
      cases deliveredEq : delivered c state request with
      | none =>
          simp [Chan.step, space]
      | some deliveredValue =>
          have head := delivered_eq_head c queue state request rep deliveredEq
          cases queue with
          | nil => simp at head
          | cons first rest =>
              simp only [List.head?_cons, Option.some.injEq] at head
              subst deliveredValue
              have room : rest.length + 1 < c.depth := by simpa using space
              simp [Chan.step, room]

private theorem readSampleSafe (state : State w) (request : Request w)
    (nextRead : Nat) (ordered : state.readSeenByWrite ≤ state.readStage0)
    (oldSafe : state.readStage0 ≤ nextRead) :
    (if request.sourceReleased = true ∧ request.sourceTick = true then
        state.readStage0
      else state.readSeenByWrite) ≤ nextRead := by
  split
  · exact oldSafe
  · exact le_trans ordered oldSafe

private theorem writeSampleSafe (state : State w) (request : Request w)
    (nextWrite : Nat) (ordered : state.writeSeenByRead ≤ state.writeStage0)
    (oldSafe : state.writeStage0 ≤ nextWrite) :
    (if request.sinkReleased = true ∧ request.sinkTick = true then
        state.writeStage0
      else state.writeSeenByRead) ≤ nextWrite := by
  split
  · exact oldSafe
  · exact le_trans ordered oldSafe

private theorem writeSampleLower (state : State w) (request : Request w)
    (nextRead : Nat)
    (stagesOrdered : state.writeSeenByRead ≤ state.writeStage0)
    (readOld : nextRead ≤ state.writeSeenByRead) :
    nextRead ≤
      (if request.sinkReleased = true ∧ request.sinkTick = true then
          state.writeStage0
        else state.writeSeenByRead) := by
  split
  · exact le_trans readOld stagesOrdered
  · exact readOld

private theorem readStagesOrdered_step (c : Chan w) (state : State w) (request : Request w)
    (ordered : state.readSeenByWrite ≤ state.readStage0) :
    (step c state request).state.readSeenByWrite ≤
      (step c state request).state.readStage0 := by
  simp only [step]
  split <;> simp_all [sample_old_le]

private theorem readStageSafe_step (c : Chan w) (state : State w) (request : Request w)
    (safe : state.readStage0 ≤ state.readCount) :
    (step c state request).state.readStage0 ≤
      (step c state request).state.readCount := by
  simp only [step]
  split
  · exact le_trans (sample_le_current safe) (Nat.le_add_right _ _)
  · exact le_trans safe (Nat.le_add_right _ _)

private theorem writeStagesOrdered_step (c : Chan w) (state : State w) (request : Request w)
    (ordered : state.writeSeenByRead ≤ state.writeStage0) :
    (step c state request).state.writeSeenByRead ≤
      (step c state request).state.writeStage0 := by
  simp only [step]
  split <;> simp_all [sample_old_le]

private theorem writeStageSafe_step (c : Chan w) (state : State w) (request : Request w)
    (safe : state.writeStage0 ≤ state.writeCount) :
    (step c state request).state.writeStage0 ≤
      (step c state request).state.writeCount := by
  simp only [step]
  split
  · exact le_trans (sample_le_current safe) (Nat.le_add_right _ _)
  · exact le_trans safe (Nat.le_add_right _ _)

private theorem pointerLt_of_delivered (c : Chan w) (state : State w) (request : Request w)
    {value : BitVec w} (didDeliver : delivered c state request = some value) :
    state.readCount < state.writeSeenByRead := by
  unfold delivered at didDeliver
  split at didDeliver
  · rename_i enabled
    have facts : ((request.sinkReleased = true ∧ request.sinkTick = true) ∧
        request.pop = true) ∧
        state.readCount < state.writeSeenByRead := by simpa using enabled
    exact facts.2
  · simp at didDeliver

private theorem writerViewBounded_step (c : Chan w) (state : State w)
    (request : Request w)
    (stagesOrdered : state.readSeenByWrite ≤ state.readStage0)
    (oldBound : state.writeCount - state.readSeenByWrite ≤ c.depth) :
    (step c state request).state.writeCount -
        (step c state request).state.readSeenByWrite ≤ c.depth := by
  have seenLower : state.readSeenByWrite ≤
      (if request.sourceReleased && request.sourceTick then
          state.readStage0
        else state.readSeenByWrite) := by
    split
    · exact stagesOrdered
    · rfl
  cases acceptEq : accepted c state request with
  | none =>
      have nextBound :=
        le_trans (Nat.sub_le_sub_left seenLower state.writeCount) oldBound
      simpa [step, acceptEq] using nextBound
  | some value =>
      have room : state.writeCount - state.readSeenByWrite < c.depth := by
        unfold accepted at acceptEq
        split at acceptEq
        · split at acceptEq
          · assumption
          · simp at acceptEq
        · simp at acceptEq
      have estimate : state.writeCount + 1 - state.readSeenByWrite ≤ c.depth := by
        omega
      have nextBound := le_trans
        (Nat.sub_le_sub_left seenLower (state.writeCount + 1)) estimate
      simpa [step, acceptEq] using nextBound

/-- One physical FIFO event preserves the full concrete/abstract
representation relation.  Pointer-view staleness may suppress transfers but
cannot change the sequence represented by storage and the local counters. -/
theorem rep_step (c : Chan w) (queue : Chan.State w)
    (state : State w) (request : Request w) (rep : Rep c queue state) :
    Rep c (c.step queue (observedEvent c state request)).state
      (step c state request).state := by
  have countersOrdered := rep.countersOrdered
  have occupancyBounded := rep.bounded
  have queueLengthEq := rep.lengthEq
  have readViewSafe := rep.readViewSafe
  have writeViewLower := rep.writeViewLower
  have writeViewSafe := rep.writeViewSafe
  cases acceptedEq : accepted c state request with
  | none =>
      cases deliveredEq : delivered c state request with
      | none =>
          have queueStep :
              (c.step queue (observedEvent c state request)).state = queue := by
            simp [observedEvent, acceptedEq, deliveredEq, Chan.step]
          rw [queueStep]
          refine
            { positiveDepth := rep.positiveDepth
              countersOrdered := ?_
              bounded := ?_
              writerViewBounded := ?_
              lengthEq := ?_
              readStagesOrdered := readStagesOrdered_step c state request rep.readStagesOrdered
              readStageSafe := readStageSafe_step c state request rep.readStageSafe
              readViewSafe := ?_
              writeStagesOrdered := writeStagesOrdered_step c state request rep.writeStagesOrdered
              writeStageSafe := writeStageSafe_step c state request rep.writeStageSafe
              writeViewLower := ?_
              writeViewSafe := ?_
              storage := ?_ }
          · simpa [step, acceptedEq, deliveredEq] using rep.countersOrdered
          · simpa [step, acceptedEq, deliveredEq] using rep.bounded
          · exact writerViewBounded_step c state request rep.readStagesOrdered
              rep.writerViewBounded
          · simpa [step, acceptedEq, deliveredEq] using rep.lengthEq
          · simp [step, acceptedEq, deliveredEq]
            exact readSampleSafe state request state.readCount rep.readStagesOrdered
              rep.readStageSafe
          · simp [step, acceptedEq, deliveredEq]
            exact writeSampleLower state request state.readCount
              rep.writeStagesOrdered rep.writeViewLower
          · simp [step, acceptedEq, deliveredEq]
            exact writeSampleSafe state request state.writeCount rep.writeStagesOrdered
              rep.writeStageSafe
          · intro offset present
            simpa [step, acceptedEq, deliveredEq] using rep.storage offset present
      | some deliveredValue =>
          have head := delivered_eq_head c queue state request rep deliveredEq
          cases queue with
          | nil => simp at head
          | cons first rest =>
              simp only [List.head?_cons, Option.some.injEq] at head
              subst deliveredValue
              have queueStep :
                  (c.step (first :: rest) (observedEvent c state request)).state = rest := by
                simp [observedEvent, acceptedEq, deliveredEq, Chan.step]
              rw [queueStep]
              have pointerLt := pointerLt_of_delivered c state request deliveredEq
              refine
                { positiveDepth := rep.positiveDepth
                  countersOrdered := ?_
                  bounded := ?_
                  writerViewBounded := ?_
                  lengthEq := ?_
                  readStagesOrdered := readStagesOrdered_step c state request rep.readStagesOrdered
                  readStageSafe := readStageSafe_step c state request rep.readStageSafe
                  readViewSafe := ?_
                  writeStagesOrdered := writeStagesOrdered_step c state request rep.writeStagesOrdered
                  writeStageSafe := writeStageSafe_step c state request rep.writeStageSafe
                  writeViewLower := ?_
                  writeViewSafe := ?_
                  storage := ?_ }
              · simp [step, acceptedEq, deliveredEq]
                exact Nat.succ_le_of_lt (lt_of_lt_of_le pointerLt rep.writeViewSafe)
              · simp [step, acceptedEq, deliveredEq]
                omega
              · exact writerViewBounded_step c state request rep.readStagesOrdered
                  rep.writerViewBounded
              · simp [step, acceptedEq, deliveredEq]
                have lengthEq := queueLengthEq
                simp only [List.length_cons] at lengthEq
                omega
              · simp [step, acceptedEq, deliveredEq]
                exact readSampleSafe state request (state.readCount + 1)
                  rep.readStagesOrdered (le_trans rep.readStageSafe (Nat.le_succ _))
              · simp [step, acceptedEq, deliveredEq]
                exact writeSampleLower state request (state.readCount + 1)
                  rep.writeStagesOrdered (by omega)
              · simp [step, acceptedEq, deliveredEq]
                exact writeSampleSafe state request state.writeCount
                  rep.writeStagesOrdered rep.writeStageSafe
              · intro offset present
                have oldPresent : offset + 1 < (first :: rest).length := by simp; omega
                have stored := rep.storage (offset + 1) oldPresent
                simp only [List.getElem_cons_succ] at stored
                simpa [step, acceptedEq, deliveredEq, Nat.add_assoc,
                  Nat.add_left_comm, Nat.add_comm] using stored
  | some acceptedValue =>
      have room := space_of_accepted c queue state request rep (by simp [acceptedEq])
      cases deliveredEq : delivered c state request with
      | none =>
          have queueStep :
              (c.step queue (observedEvent c state request)).state =
                queue ++ [acceptedValue] := by
            simp [observedEvent, acceptedEq, deliveredEq, Chan.step, room]
          rw [queueStep]
          refine
            { positiveDepth := rep.positiveDepth
              countersOrdered := ?_
              bounded := ?_
              writerViewBounded := ?_
              lengthEq := ?_
              readStagesOrdered := readStagesOrdered_step c state request rep.readStagesOrdered
              readStageSafe := readStageSafe_step c state request rep.readStageSafe
              readViewSafe := ?_
              writeStagesOrdered := writeStagesOrdered_step c state request rep.writeStagesOrdered
              writeStageSafe := writeStageSafe_step c state request rep.writeStageSafe
              writeViewLower := ?_
              writeViewSafe := ?_
              storage := ?_ }
          · simp [step, acceptedEq, deliveredEq]
            exact le_trans countersOrdered (Nat.le_succ _)
          · simp [step, acceptedEq, deliveredEq]
            have counterRoom : state.writeCount - state.readCount < c.depth := by
              rw [← queueLengthEq]
              exact room
            have nextEq : (state.writeCount + 1) - state.readCount =
                (state.writeCount - state.readCount) + 1 := by omega
            omega
          · exact writerViewBounded_step c state request rep.readStagesOrdered
              rep.writerViewBounded
          · simp [step, acceptedEq, deliveredEq]
            have nextEq : (state.writeCount + 1) - state.readCount =
                (state.writeCount - state.readCount) + 1 := by omega
            rw [nextEq, ← queueLengthEq]
          · simp [step, acceptedEq, deliveredEq]
            exact readSampleSafe state request state.readCount rep.readStagesOrdered
              rep.readStageSafe
          · simp [step, acceptedEq, deliveredEq]
            exact writeSampleLower state request state.readCount
              rep.writeStagesOrdered rep.writeViewLower
          · simp [step, acceptedEq, deliveredEq]
            exact writeSampleSafe state request (state.writeCount + 1)
              rep.writeStagesOrdered (le_trans rep.writeStageSafe (Nat.le_succ _))
          · intro offset present
            by_cases old : offset < queue.length
            · have notWrite : state.readCount + offset ≠ state.writeCount := by
                intro equal
                have : offset = state.writeCount - state.readCount := by omega
                omega
              have addressOrdered : state.readCount + offset ≤ state.writeCount := by
                omega
              have addressDistance :
                  state.writeCount - (state.readCount + offset) < c.depth := by
                omega
              have notWriteMod :
                  (state.readCount + offset) % c.depth ≠
                    state.writeCount % c.depth :=
                mod_ne_of_ordered_distance addressOrdered
                  notWrite addressDistance
              simpa [step, acceptedEq, deliveredEq,
                Function.update_of_ne notWriteMod, List.getElem_append_left old] using
                  rep.storage offset old
            · have last : offset = queue.length := by
                simp only [List.length_append, List.length_cons, List.length_nil] at present
                omega
              subst offset
              have atWrite : state.readCount + queue.length = state.writeCount := by
                rw [queueLengthEq]
                exact Nat.add_sub_of_le countersOrdered
              simp [step, acceptedEq, deliveredEq, atWrite]
      | some deliveredValue =>
          have head := delivered_eq_head c queue state request rep deliveredEq
          cases queue with
          | nil => simp at head
          | cons first rest =>
              simp only [List.head?_cons, Option.some.injEq] at head
              subst deliveredValue
              have room' : rest.length + 1 < c.depth := by simpa using room
              have queueStep :
                  (c.step (first :: rest) (observedEvent c state request)).state =
                    rest ++ [acceptedValue] := by
                simp [observedEvent, acceptedEq, deliveredEq, Chan.step, room']
              rw [queueStep]
              have pointerLt := pointerLt_of_delivered c state request deliveredEq
              refine
                { positiveDepth := rep.positiveDepth
                  countersOrdered := ?_
                  bounded := ?_
                  writerViewBounded := ?_
                  lengthEq := ?_
                  readStagesOrdered := readStagesOrdered_step c state request rep.readStagesOrdered
                  readStageSafe := readStageSafe_step c state request rep.readStageSafe
                  readViewSafe := ?_
                  writeStagesOrdered := writeStagesOrdered_step c state request rep.writeStagesOrdered
                  writeStageSafe := writeStageSafe_step c state request rep.writeStageSafe
                  writeViewLower := ?_
                  writeViewSafe := ?_
                  storage := ?_ }
              · simp [step, acceptedEq, deliveredEq]
                exact countersOrdered
              · simp [step, acceptedEq, deliveredEq]
                simpa [Nat.add_sub_add_right] using occupancyBounded
              · exact writerViewBounded_step c state request rep.readStagesOrdered
                  rep.writerViewBounded
              · simp [step, acceptedEq, deliveredEq]
                have lengthEq := queueLengthEq
                simp only [List.length_cons] at lengthEq
                omega
              · simp [step, acceptedEq, deliveredEq]
                exact readSampleSafe state request (state.readCount + 1)
                  rep.readStagesOrdered (le_trans rep.readStageSafe (Nat.le_succ _))
              · simp [step, acceptedEq, deliveredEq]
                exact writeSampleLower state request (state.readCount + 1)
                  rep.writeStagesOrdered (by omega)
              · simp [step, acceptedEq, deliveredEq]
                exact writeSampleSafe state request (state.writeCount + 1)
                  rep.writeStagesOrdered
                  (le_trans rep.writeStageSafe (Nat.le_succ _))
              · intro offset present
                by_cases old : offset < rest.length
                · have oldPresent : offset + 1 < (first :: rest).length := by simp; omega
                  have notWrite : state.readCount + 1 + offset ≠ state.writeCount := by
                    intro equal
                    have lengthEq : rest.length + 1 =
                        state.writeCount - state.readCount := by
                      simpa using queueLengthEq
                    omega
                  have stored := rep.storage (offset + 1) oldPresent
                  simp only [List.getElem_cons_succ] at stored
                  have notWrite' : offset + (state.readCount + 1) ≠ state.writeCount := by
                    omega
                  have addressOrdered :
                      offset + (state.readCount + 1) ≤ state.writeCount := by omega
                  have addressDistance :
                      state.writeCount - (offset + (state.readCount + 1)) < c.depth := by
                    omega
                  have notWriteMod :
                      (offset + (state.readCount + 1)) % c.depth ≠
                        state.writeCount % c.depth :=
                    mod_ne_of_ordered_distance addressOrdered
                      notWrite' addressDistance
                  simpa [step, acceptedEq, deliveredEq,
                    Function.update_of_ne notWriteMod, List.getElem_append_left old,
                    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using stored
                · have last : offset = rest.length := by
                    simp only [List.length_append, List.length_cons, List.length_nil] at present
                    omega
                  subst offset
                  have atWrite : state.readCount + 1 + rest.length = state.writeCount := by
                    have lengthEq := queueLengthEq
                    simp only [List.length_cons] at lengthEq
                    omega
                  simp [step, acceptedEq, deliveredEq, atWrite]

/-- The executable stock asynchronous FIFO model is certified against the
abstract channel.  The request type includes clock edges and adversarial
synchronizer samples, so the inherited trace theorem quantifies over both. -/
def refinement (c : Chan w) (positiveDepth : 0 < c.depth) : Chan.Refinement c where
  ConcreteState := State w
  Request := Request w
  reset := reset w
  step := fun state request =>
    let result := step c state request
    { state := result.state, accepted := result.accepted,
      delivered := result.delivered }
  Rep := Rep c
  reset_refines := rep_reset c positiveDepth
  step_refines := by
    intro queue state request rep
    dsimp only
    exact ⟨rep_step c queue state request rep,
      transfer_refines c queue state request rep⟩

/-! ## Parametric composition with a finite storage implementation -/

namespace WithStorage

variable (c : Chan w) (positiveDepth : 0 < c.depth)

abbrev Params := storageParameters c positiveDepth

/-- Executable composed state. `reference` is a ghost copy of the narrow
storage semantics used to join the independently certified FIFO-control and
storage refinements; `storage` is the selected implementation's real state. -/
structure State (implementation : AsyncQueueStorage.Implementation (Params c positiveDepth)) where
  fifo : AsyncFifo.State w
  storage : implementation.State
  reference : AsyncQueueStorage.ReferenceState (Params c positiveDepth)

def initialMemory : Fin c.depth → BitVec w := fun _ => 0

def reset (implementation : AsyncQueueStorage.Implementation (Params c positiveDepth)) :
    State c positiveDepth implementation where
  fifo := AsyncFifo.reset w
  storage := implementation.reset (initialMemory c)
  reference := ⟨initialMemory c, []⟩

def step (implementation : AsyncQueueStorage.Implementation (Params c positiveDepth))
    (state : State c positiveDepth implementation) (request : Request w) :
    Chan.ConcreteResult (State c positiveDepth implementation) w :=
  let portEvent := storageEvent c positiveDepth state.fifo request
  let storageResult := implementation.step state.storage portEvent
  let referenceResult := AsyncQueueStorage.referenceStep state.reference portEvent
  let fifoResult := AsyncFifo.step c state.fifo request
  { state :=
      { fifo := fifoResult.state
        storage := storageResult.state
        reference := referenceResult.state }
    accepted := fifoResult.accepted
    delivered := storageResult.response }

/-- The abstract queue, finite-ring control model, reference storage, and
selected implementation all describe the same live contents. -/
structure Rep (implementation : AsyncQueueStorage.Implementation (Params c positiveDepth))
    (queue : Chan.State w) (state : State c positiveDepth implementation) : Prop where
  fifo : AsyncFifo.Rep c queue state.fifo
  storage : implementation.Rep state.reference state.storage
  pipelineEmpty : state.reference.readPipeline = []
  memory : ∀ address : Fin c.depth,
    state.reference.memory address = state.fifo.storage address.val

private theorem memory_step
    (implementation : AsyncQueueStorage.Implementation (Params c positiveDepth))
    (queue : Chan.State w) (state : State c positiveDepth implementation)
    (request : Request w) (rep : Rep c positiveDepth implementation queue state) :
    let portEvent := storageEvent c positiveDepth state.fifo request
    let referenceResult := AsyncQueueStorage.referenceStep state.reference portEvent
    let fifoResult := AsyncFifo.step c state.fifo request
    ∀ address : Fin c.depth,
      referenceResult.state.memory address = fifoResult.state.storage address.val := by
  dsimp only
  intro address
  cases acceptEq : accepted c state.fifo request with
  | none =>
      rw [AsyncQueueStorage.referenceStep_memory, storageEvent_activeWrite]
      simp [AsyncQueueStorage.writeMemory, acceptEq, rep.memory]
  | some value =>
      by_cases same : address.val = state.fifo.writeCount % c.depth
      · have finSame : address =
            ⟨state.fifo.writeCount % c.depth, Nat.mod_lt _ positiveDepth⟩ := by
          exact Fin.ext same
        subst address
        rw [AsyncQueueStorage.referenceStep_memory, storageEvent_activeWrite]
        simp [AsyncQueueStorage.writeMemory, acceptEq]
      · have finDifferent : address ≠
            ⟨state.fifo.writeCount % c.depth, Nat.mod_lt _ positiveDepth⟩ := by
          intro equal
          exact same (congrArg Fin.val equal)
        rw [AsyncQueueStorage.referenceStep_memory, storageEvent_activeWrite]
        simp [AsyncQueueStorage.writeMemory, acceptEq, same, finDifferent, rep.memory]

/-- A latency-one storage leaf never retains a response after a read-domain
edge. This small invariant is what makes the composed implementation consume
the selected leaf's response rather than a parallel ghost-memory lookup. -/
private theorem reference_pipeline_empty
    (implementation : AsyncQueueStorage.Implementation (Params c positiveDepth))
    (queue : Chan.State w) (state : State c positiveDepth implementation)
    (request : Request w) (rep : Rep c positiveDepth implementation queue state) :
    (AsyncQueueStorage.referenceStep state.reference
      (storageEvent c positiveDepth state.fifo request)).state.readPipeline = [] := by
  cases tick : (storageEvent c positiveDepth state.fifo request).readTick
  · simp [AsyncQueueStorage.referenceStep, tick, rep.pipelineEmpty]
  · simp [AsyncQueueStorage.referenceStep, tick, AsyncQueueStorage.advancePipeline,
      storageParameters, rep.pipelineEmpty]

/-- The actual selected storage response is the word authorized by the FIFO
control state. The implementation contract supplies the first equality; the
finite-ring mirror and latency-one pipeline supply the second. -/
private theorem storage_response_eq
    (implementation : AsyncQueueStorage.Implementation (Params c positiveDepth))
    (queue : Chan.State w) (state : State c positiveDepth implementation)
    (request : Request w) (rep : Rep c positiveDepth implementation queue state) :
    (implementation.step state.storage
      (storageEvent c positiveDepth state.fifo request)).response =
        (AsyncFifo.step c state.fifo request).delivered := by
  have refined := storageImplementation_step c queue state.fifo request rep.fifo
    implementation rep.storage
  rw [refined.2]
  change (AsyncQueueStorage.referenceStep state.reference
      (storageEvent c positiveDepth state.fifo request)).response =
    AsyncFifo.delivered c state.fifo request
  cases deliveredEq : AsyncFifo.delivered c state.fifo request with
  | none =>
      simp [AsyncQueueStorage.referenceStep, storageEvent, deliveredEq]
  | some value =>
      have addressValue := rep.memory
        ⟨state.fifo.readCount % c.depth, Nat.mod_lt _ positiveDepth⟩
      have fifoValue :
          state.fifo.storage (state.fifo.readCount % c.depth) = value := by
        unfold AsyncFifo.delivered at deliveredEq
        split at deliveredEq <;> simp_all
      simp [AsyncQueueStorage.referenceStep, storageEvent, deliveredEq,
        AsyncQueueStorage.Event.activeRead, AsyncQueueStorage.advancePipeline,
        storageParameters, rep.pipelineEmpty, addressValue, fifoValue]

theorem rep_reset
    (implementation : AsyncQueueStorage.Implementation (Params c positiveDepth)) :
    Rep c positiveDepth implementation [] (reset c positiveDepth implementation) where
  fifo := AsyncFifo.rep_reset c positiveDepth
  storage := implementation.reset_refines (initialMemory c)
  pipelineEmpty := rfl
  memory := by intro; rfl

theorem rep_step
    (implementation : AsyncQueueStorage.Implementation (Params c positiveDepth))
    (queue : Chan.State w) (state : State c positiveDepth implementation)
    (request : Request w) (rep : Rep c positiveDepth implementation queue state) :
    let physical := step c positiveDepth implementation state request
    let abstract := c.step queue physical.event
    Rep c positiveDepth implementation abstract.state physical.state ∧
      abstract.accepted = physical.accepted.isSome ∧
      abstract.delivered = physical.delivered := by
  dsimp only
  have fifoNext := AsyncFifo.rep_step c queue state.fifo request rep.fifo
  have transfers := AsyncFifo.transfer_refines c queue state.fifo request rep.fifo
  have storageNext := storageImplementation_step c queue state.fifo request rep.fifo
    implementation rep.storage
  have responseEq := storage_response_eq c positiveDepth implementation
    queue state request rep
  have eventEq : (step c positiveDepth implementation state request).event =
      observedEvent c state.fifo request := by
    apply congrArg₂ Chan.EventData.mk
    · rfl
    · simp [step, responseEq, AsyncFifo.step]
  rw [eventEq]
  exact ⟨
    { fifo := fifoNext
      storage := storageNext.1
      pipelineEmpty := reference_pipeline_empty c positiveDepth implementation
        queue state request rep
      memory := memory_step c positiveDepth implementation queue state request rep },
    transfers.1,
    by
      change _ = (implementation.step state.storage
        (storageEvent c positiveDepth state.fifo request)).response
      rw [responseEq]
      exact transfers.2⟩

/-- **One technology-neutral FIFO theorem.** Every implementation of
`AsyncQueueStorage` yields a channel refinement. The inherited trace theorem
quantifies over arbitrary request schedules, synchronizer choices, and reset
release skew; the only implementation-specific premise is the storage
contract itself. -/
def refinement
    (implementation : AsyncQueueStorage.Implementation (Params c positiveDepth)) :
    Chan.Refinement c where
  ConcreteState := State c positiveDepth implementation
  Request := Request w
  reset := reset c positiveDepth implementation
  step := step c positiveDepth implementation
  Rep := Rep c positiveDepth implementation
  reset_refines := rep_reset c positiveDepth implementation
  step_refines := by
    intro queue state request rep
    exact rep_step c positiveDepth implementation queue state request rep

end WithStorage

/-- Common assertion followed by arbitrary, independently skewed monotone
release is covered by the same all-traces refinement theorem.  The proof does
not use the release discipline: safety actually holds for the stronger set of
all gating traces.  Progress theorems may use `release` separately. -/
theorem equivalent_under_release_skew (c : Chan w) (positiveDepth : 0 < c.depth)
    (requests : List (Request w)) (_release : ReleaseSchedule requests) :
    let implementation := refinement c positiveDepth
    let abstract := c.runTrace []
      (implementation.observedEvents implementation.reset requests)
    let physical := implementation.runConcrete implementation.reset requests
    implementation.Rep abstract.state physical.state ∧
      physical.accepted = abstract.accepted ∧
      physical.delivered = abstract.delivered :=
  (refinement c positiveDepth).equivalent requests

end Loom.Hw.Cdc.AsyncFifo
