-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.ClockGauntlet.Liveness

/-! Normalization bridge from the finite liveness certificate to arbitrary
invariant protocol states. -/

namespace Machines.Multiclock.ClockGauntlet.Execution

open Loom.Hw
open Machines.Multiclock.ClockGauntlet

def shiftProtocol (amount : Nat) (state : ProtocolState) : ProtocolState :=
  { state with
    nextPacket := state.nextPacket + amount
    expectedSequence := state.expectedSequence + amount }

theorem protocolAdvance_shift (clockEvent : NamedClockEvent)
    (state : ProtocolState) (amount : Nat)
    (sourceOpen : state.nextPacket < packetCount)
    (shiftedOpen : state.nextPacket + amount < packetCount) :
    protocolAdvance clockEvent (shiftProtocol amount state) =
      shiftProtocol amount (protocolAdvance clockEvent state) := by
  cases hs : clockEvent.fires "source_clk" <;>
    cases ht : clockEvent.fires "transform_clk" <;>
    cases hc : clockEvent.fires "checker_clk" <;>
    simp [protocolAdvance, shiftProtocol, hs, ht, hc, sourceOpen, shiftedOpen] <;>
      omega

theorem protocolAdvance_nextPacket_le (clockEvent : NamedClockEvent)
    (state : ProtocolState) :
    (protocolAdvance clockEvent state).nextPacket ≤ state.nextPacket + 1 := by
  simp [protocolAdvance]
  split <;> omega

theorem runProtocol_nextPacket_le (state : ProtocolState)
    (events : List NamedClockEvent) :
    (runProtocol state events).nextPacket ≤ state.nextPacket + events.length := by
  induction events generalizing state with
  | nil => simp [runProtocol]
  | cons next rest ih =>
      simp only [runProtocol, List.length_cons]
      have step := protocolAdvance_nextPacket_le next state
      have tail := ih (protocolAdvance next state)
      omega

theorem runProtocol_shift (state : ProtocolState) (amount : Nat)
    (events : List NamedClockEvent)
    (sourceOpen : state.nextPacket + events.length < packetCount)
    (shiftedOpen : state.nextPacket + amount + events.length < packetCount) :
    runProtocol (shiftProtocol amount state) events =
      shiftProtocol amount (runProtocol state events) := by
  induction events generalizing state with
  | nil => rfl
  | cons next rest ih =>
      simp only [runProtocol, List.length_cons] at sourceOpen shiftedOpen ⊢
      have sourceNow : state.nextPacket < packetCount := by omega
      have shiftedNow : state.nextPacket + amount < packetCount := by omega
      rw [protocolAdvance_shift next state amount sourceNow shiftedNow]
      apply ih
      · have step := protocolAdvance_nextPacket_le next state
        omega
      · have step := protocolAdvance_nextPacket_le next state
        simp at step ⊢
        omega

def rankRepresentativeCode (state : ProtocolState) : Nat :=
  min (packetCount - state.nextPacket) 7 +
    8 * protocolInvariantControls state

theorem rankRepresentativeCode_lt (state : ProtocolState)
    (invariant : ProtocolInvariant state) :
    rankRepresentativeCode state < 1152 := by
  rcases invariant with ⟨_, _, _, firstBound, secondBound, _⟩
  cases hsv : state.sourceValid <;> cases htp : state.transformPending <;>
    cases htv : state.transformValid <;> cases hcp : state.checkerPop <;>
    simp [rankRepresentativeCode, protocolInvariantControls, boolNat,
      Machines.Multiclock.ClockGauntlet.packetCount, hsv, htp, htv, hcp] <;> omega

theorem rankRepresentative_code (state : ProtocolState)
    (invariant : ProtocolInvariant state) :
    rankRepresentative (rankRepresentativeCode state) =
      if state.nextPacket < 249 then
        shiftProtocol (249 - state.nextPacket) state
      else state := by
  rcases invariant with
    ⟨conserve, nextBound, expectedBound, firstBound, secondBound,
      checkerBound, pendingBound, pendingValid⟩
  have conserveNat :
      state.nextPacket + boolNat state.checkerPop =
        state.expectedSequence + boolNat state.sourceValid + state.firstLength +
          state.secondLength +
            boolNat (state.transformValid && !state.transformPending) := by
    have casted := congrArg Int.toNat conserve
    simpa using casted
  simp [Machines.Multiclock.ClockGauntlet.packetCount] at nextBound expectedBound
  let remaining := min (256 - state.nextPacket) 7
  have remainingLt : remaining < 8 := by simp [remaining]
  have codeMod : rankRepresentativeCode state % 8 = remaining := by
    simp [rankRepresentativeCode, remaining, Machines.Multiclock.ClockGauntlet.packetCount,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt remainingLt]
  have codeDiv : rankRepresentativeCode state / 8 =
      protocolInvariantControls state := by
    simp [rankRepresentativeCode, remaining, Machines.Multiclock.ClockGauntlet.packetCount,
      Nat.add_mul_div_left, Nat.div_eq_of_lt remainingLt]
  obtain ⟨sourceEq, pendingEq, validEq, checkerEq, firstEq, secondEq⟩ :=
    protocolInvariantControls_decode state firstBound secondBound
  simp only [rankRepresentative]
  rw [codeMod, codeDiv, sourceEq, pendingEq, validEq, checkerEq, firstEq,
    secondEq]
  by_cases boundary : state.nextPacket < 249
  · simp only [if_pos boundary]
    have remainingEq : remaining = 7 := by simp [remaining]; omega
    apply ProtocolState.ext <;> simp [shiftProtocol]
    · change 256 - remaining = state.nextPacket + (249 - state.nextPacket)
      rw [remainingEq]
      omega
    · change 256 - remaining + boolNat state.checkerPop -
        (boolNat state.sourceValid + state.firstLength + state.secondLength +
          boolNat (state.transformValid && !state.transformPending)) =
        state.expectedSequence + (249 - state.nextPacket)
      rw [remainingEq]
      omega
  · simp only [if_neg boundary]
    have remainingEq : remaining = 256 - state.nextPacket := by
      simp [remaining]
      omega
    apply ProtocolState.ext <;> simp
    · change 256 - remaining = state.nextPacket
      rw [remainingEq]
      omega
    · change 256 - remaining + boolNat state.checkerPop -
        (boolNat state.sourceValid + state.firstLength + state.secondLength +
          boolNat (state.transformValid && !state.transformPending)) =
        state.expectedSequence
      rw [remainingEq]
      omega

theorem protocolInvariant_expected_le_next (state : ProtocolState)
    (invariant : ProtocolInvariant state) :
    state.expectedSequence ≤ state.nextPacket := by
  rcases invariant with ⟨conserve, _, _, _, _, checkerBound, _, _⟩
  cases hcp : state.checkerPop <;>
    simp [boolNat, hcp] at conserve checkerBound ⊢ <;> omega

theorem protocolInvariant_shift (state : ProtocolState) (amount : Nat)
    (invariant : ProtocolInvariant state)
    (nextBound : state.nextPacket + amount ≤ packetCount)
    (expectedBound : state.expectedSequence + amount ≤ packetCount) :
    ProtocolInvariant (shiftProtocol amount state) := by
  rcases invariant with
    ⟨conserve, _, _, firstBound, secondBound, checkerBound, pendingBound,
      pendingValid⟩
  refine ⟨?_, nextBound, expectedBound, firstBound, secondBound,
    checkerBound, pendingBound, pendingValid⟩
  simp only [shiftProtocol]
  have conserveNat :
      state.nextPacket + boolNat state.checkerPop =
        state.expectedSequence + boolNat state.sourceValid + state.firstLength +
          state.secondLength +
            boolNat (state.transformValid && !state.transformPending) := by
    have casted := congrArg Int.toNat conserve
    simpa using casted
  have shiftedNat :
      (state.nextPacket + amount) + boolNat state.checkerPop =
        (state.expectedSequence + amount) + boolNat state.sourceValid +
          state.firstLength + state.secondLength +
            boolNat (state.transformValid && !state.transformPending) := by
    omega
  have shiftedInt := congrArg Int.ofNat shiftedNat
  simpa only [Int.ofNat_eq_coe, Int.natCast_add] using shiftedInt

theorem protocolPhaseRank_shift (state : ProtocolState) (amount : Nat)
    (bound : state.nextPacket + amount ≤ packetCount) :
    protocolPhaseRank (shiftProtocol amount state) + 14 * amount =
      protocolPhaseRank state := by
  simp [protocolPhaseRank, protocolRank, protocolProgressReady, shiftProtocol,
    boolNat]
  simp [Machines.Multiclock.ClockGauntlet.packetCount] at bound ⊢
  omega

theorem protocolAdvance_expectedSequence_le (clockEvent : NamedClockEvent)
    (state : ProtocolState) :
    (protocolAdvance clockEvent state).expectedSequence ≤
      state.expectedSequence + 1 := by
  simp [protocolAdvance]
  split <;> omega

theorem runProtocol_expectedSequence_le (state : ProtocolState)
    (events : List NamedClockEvent) :
    (runProtocol state events).expectedSequence ≤
      state.expectedSequence + events.length := by
  induction events generalizing state with
  | nil => simp [runProtocol]
  | cons next rest ih =>
      simp only [runProtocol, List.length_cons]
      have step := protocolAdvance_expectedSequence_le next state
      have tail := ih (protocolAdvance next state)
      omega

/-- Every invariant incomplete protocol state completes or strictly decreases
the phase-aware rank after an arbitrary legal six-event block. -/
theorem protocol_block_progress (state : ProtocolState)
    (invariant : ProtocolInvariant state)
    (incomplete : protocolComplete state = false)
    {masks : List Nat} (length : masks.length = 6)
    (follows : FollowsRankGap 0 0 0 masks) :
    protocolComplete (runProtocol state (masks.map event)) = true ∨
      protocolPhaseRank (runProtocol state (masks.map event)) <
        protocolPhaseRank state := by
  let code := rankRepresentativeCode state
  have codeBound : code < 1152 := rankRepresentativeCode_lt state invariant
  have representativeEq := rankRepresentative_code state invariant
  by_cases far : state.nextPacket < 249
  · let amount := 249 - state.nextPacket
    have nextShift : state.nextPacket + amount = 249 := by
      simp [amount]
      omega
    have expectedLe := protocolInvariant_expected_le_next state invariant
    have expectedShift : state.expectedSequence + amount ≤ packetCount := by
      change state.expectedSequence + amount ≤ 256
      omega
    have representativeInvariant : ProtocolInvariant (rankRepresentative code) := by
      rw [representativeEq, if_pos far]
      exact protocolInvariant_shift state amount invariant (by
        simp [nextShift, Machines.Multiclock.ClockGauntlet.packetCount]) expectedShift
    have representativeExpected :
        (rankRepresentative code).expectedSequence ≤ 249 := by
      rw [representativeEq, if_pos far]
      simp [shiftProtocol]
      omega
    have representativeIncomplete :
        protocolComplete (rankRepresentative code) = false := by
      simp only [protocolComplete, beq_eq_false_iff_ne]
      simp [Machines.Multiclock.ClockGauntlet.packetCount]
      omega
    have progress := rankRepresentative_block_progress codeBound
      representativeInvariant representativeIncomplete length follows
    have representativeGrowth := runProtocol_expectedSequence_le
      (rankRepresentative code) (masks.map event)
    have representativeEndLt :
        (runProtocol (rankRepresentative code) (masks.map event)).expectedSequence <
          256 := by
      simp [List.length_map, length] at representativeGrowth
      omega
    have shiftedRun := runProtocol_shift state amount (masks.map event) (by
      simp [length, Machines.Multiclock.ClockGauntlet.packetCount]
      omega) (by
      simp [List.length_map, length, nextShift,
        Machines.Multiclock.ClockGauntlet.packetCount])
    rcases progress with completed | decreased
    · change (((runProtocol (rankRepresentative code)
          (masks.map event)).expectedSequence == 256) = true) at completed
      simp at completed
      omega
    · right
      rw [representativeEq, if_pos far, shiftedRun] at decreased
      change protocolPhaseRank
          (shiftProtocol amount (runProtocol state (masks.map event))) <
        protocolPhaseRank (shiftProtocol amount state) at decreased
      have finishNext := runProtocol_nextPacket_le state (masks.map event)
      have finishBound :
          (runProtocol state (masks.map event)).nextPacket + amount ≤
            packetCount := by
        simp [List.length_map, length] at finishNext
        simp [Machines.Multiclock.ClockGauntlet.packetCount]
        omega
      have startRank := protocolPhaseRank_shift state amount (by
        simp [nextShift, Machines.Multiclock.ClockGauntlet.packetCount])
      have finishRank := protocolPhaseRank_shift
        (runProtocol state (masks.map event)) amount finishBound
      omega
  · have representativeExact : rankRepresentative code = state := by
      simpa [code, if_neg far] using representativeEq
    have representativeInvariant : ProtocolInvariant (rankRepresentative code) := by
      simpa [representativeExact] using invariant
    have representativeIncomplete :
        protocolComplete (rankRepresentative code) = false := by
      simpa [representativeExact] using incomplete
    have progress := rankRepresentative_block_progress codeBound
      representativeInvariant representativeIncomplete length follows
    simpa [representativeExact] using progress

theorem protocolAdvance_expectedSequence_mono (clockEvent : NamedClockEvent)
    (state : ProtocolState) :
    state.expectedSequence ≤
      (protocolAdvance clockEvent state).expectedSequence := by
  simp [protocolAdvance]

theorem runProtocol_expectedSequence_mono (state : ProtocolState)
    (events : List NamedClockEvent) :
    state.expectedSequence ≤ (runProtocol state events).expectedSequence := by
  induction events generalizing state with
  | nil => simp [runProtocol]
  | cons next rest ih =>
      simp only [runProtocol]
      exact le_trans (protocolAdvance_expectedSequence_mono next state)
        (ih (protocolAdvance next state))

theorem protocolComplete_run (state : ProtocolState)
    (events : List NamedClockEvent) (invariant : ProtocolInvariant state)
    (complete : protocolComplete state = true) :
    protocolComplete (runProtocol state events) = true := by
  have finalInvariant := protocolInvariant_run state events invariant
  have monotone := runProtocol_expectedSequence_mono state events
  rcases finalInvariant with ⟨_, _, finalBound, _⟩
  simp [protocolComplete] at complete ⊢
  omega

def eventMasks (events : List NamedClockEvent) : List Nat :=
  events.map protocolEventMask

theorem runProtocol_eventMasks (state : ProtocolState)
    (events : List NamedClockEvent) :
    runProtocol state ((eventMasks events).map event) =
      runProtocol state events := by
  induction events generalizing state with
  | nil => rfl
  | cons next rest ih =>
      simp only [eventMasks, List.map_cons, List.map_map, runProtocol]
      rw [protocolAdvance_eventMask]
      simpa [eventMasks, Function.comp_def] using
        ih (protocolAdvance next state)

/-- An arbitrary-order six-event block in which each sliding three-event
window contains source, transform, and checker ticks. Coincident and extra
ticks are allowed. -/
def BoundedTickBlock (events : List NamedClockEvent) : Prop :=
  events.length = 6 ∧ FollowsRankGap 0 0 0 (eventMasks events)

def BoundedTickBlocks (blocks : List (List NamedClockEvent)) : Prop :=
  ∀ block ∈ blocks, BoundedTickBlock block

def runProtocolBlocks : ProtocolState → List (List NamedClockEvent) → ProtocolState
  | state, [] => state
  | state, block :: rest =>
      runProtocolBlocks (runProtocol state block) rest

theorem runProtocolBlocks_invariant (state : ProtocolState)
    (blocks : List (List NamedClockEvent)) (invariant : ProtocolInvariant state) :
    ProtocolInvariant (runProtocolBlocks state blocks) := by
  induction blocks generalizing state with
  | nil => simpa [runProtocolBlocks] using invariant
  | cons block rest ih =>
      simp only [runProtocolBlocks]
      exact ih _ (protocolInvariant_run state block invariant)

theorem protocolComplete_runBlocks (state : ProtocolState)
    (blocks : List (List NamedClockEvent)) (invariant : ProtocolInvariant state)
    (complete : protocolComplete state = true) :
    protocolComplete (runProtocolBlocks state blocks) = true := by
  induction blocks generalizing state with
  | nil => simpa [runProtocolBlocks] using complete
  | cons block rest ih =>
      simp only [runProtocolBlocks]
      exact ih _ (protocolInvariant_run state block invariant)
        (protocolComplete_run state block invariant complete)

theorem protocolPhaseRank_pos (state : ProtocolState) :
    0 < protocolPhaseRank state := by
  cases ready : protocolProgressReady state <;>
    simp [protocolPhaseRank, boolNat, ready]
  have second : state.secondLength = 2 := by
    simp [protocolProgressReady] at ready
    exact ready.2
  simp [protocolRank, boolNat, second]

theorem runProtocolBlocks_rank_budget (state : ProtocolState)
    (blocks : List (List NamedClockEvent)) (invariant : ProtocolInvariant state)
    (bounded : BoundedTickBlocks blocks)
    (finalIncomplete : protocolComplete (runProtocolBlocks state blocks) = false) :
    protocolPhaseRank (runProtocolBlocks state blocks) + blocks.length ≤
      protocolPhaseRank state := by
  induction blocks generalizing state with
  | nil => simp [runProtocolBlocks]
  | cons block rest ih =>
      have blockBound := bounded block (by simp)
      have restBound : BoundedTickBlocks rest := by
        intro next member
        exact bounded next (by simp [member])
      have stateIncomplete : protocolComplete state = false := by
        cases completeEq : protocolComplete state
        · rfl
        · have finalComplete := protocolComplete_runBlocks state
              (block :: rest) invariant completeEq
          rw [finalIncomplete] at finalComplete
          contradiction
      rcases blockBound with ⟨blockLength, blockFollows⟩
      have progress := protocol_block_progress state invariant stateIncomplete
        (by simpa [eventMasks, blockLength]) blockFollows
      rw [runProtocol_eventMasks] at progress
      rcases progress with blockComplete | decreased
      · have finalComplete := protocolComplete_runBlocks (runProtocol state block)
            rest (protocolInvariant_run state block invariant) blockComplete
        have finalIncomplete' :
            protocolComplete (runProtocolBlocks (runProtocol state block) rest) =
              false := by
          simpa [runProtocolBlocks] using finalIncomplete
        rw [finalIncomplete'] at finalComplete
        contradiction
      · have tailBudget := ih (runProtocol state block)
            (protocolInvariant_run state block invariant) restBound finalIncomplete
        simp only [runProtocolBlocks, List.length_cons]
        omega

/-- Schedule-independent bounded completion: 3,585 arbitrary-order fair
six-event blocks suffice for all 256 packets. This is a 21,510-event finite
prefix bound and permits coincident ticks and changing phase/order. -/
theorem bounded_completion_blocks
    (blocks : List (List NamedClockEvent))
    (count : blocks.length = 3585)
    (bounded : BoundedTickBlocks blocks) :
    protocolComplete (runProtocolBlocks protocolReset blocks) = true := by
  cases completeEq : protocolComplete (runProtocolBlocks protocolReset blocks)
  · have budget := runProtocolBlocks_rank_budget protocolReset blocks
        protocolInvariant_reset bounded completeEq
    have positive := protocolPhaseRank_pos
      (runProtocolBlocks protocolReset blocks)
    rw [count, protocolPhaseRank_reset] at budget
    omega
  · rfl

theorem runProtocol_append_public (state : ProtocolState)
    (first second : List NamedClockEvent) :
    runProtocol state (first ++ second) =
      runProtocol (runProtocol state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons next rest ih =>
      simpa [runProtocol] using ih (protocolAdvance next state)

theorem runProtocolBlocks_eq_flatten (state : ProtocolState)
    (blocks : List (List NamedClockEvent)) :
    runProtocolBlocks state blocks = runProtocol state blocks.flatten := by
  induction blocks generalizing state with
  | nil => rfl
  | cons block rest ih =>
      simp only [runProtocolBlocks, List.flatten_cons]
      rw [runProtocol_append_public]
      exact ih (runProtocol state block)

theorem bounded_completion_schedule
    (blocks : List (List NamedClockEvent))
    (count : blocks.length = 3585)
    (bounded : BoundedTickBlocks blocks) :
    protocolComplete (runProtocol protocolReset blocks.flatten) = true := by
  rw [← runProtocolBlocks_eq_flatten]
  exact bounded_completion_blocks blocks count bounded

theorem boundedTickBlocks_flatten_length
    (blocks : List (List NamedClockEvent))
    (bounded : BoundedTickBlocks blocks) :
    blocks.flatten.length = 6 * blocks.length := by
  induction blocks with
  | nil => simp
  | cons block rest ih =>
      have blockBound := bounded block (by simp)
      have restBound : BoundedTickBlocks rest := by
        intro next member
        exact bounded next (by simp [member])
      rw [List.flatten_cons, List.length_append, blockBound.1, ih restBound,
        List.length_cons]
      omega

theorem protocolComplete_protocolState_iff (fast : FastState) :
    protocolComplete (protocolState fast) = livenessComplete fast := by
  rfl

/-- If the protocol execution completes, the optimized evaluator reaches an
exactly corresponding completion at some prefix. The proof advances the
machine/System correspondence only while completion is still pending. -/
theorem exists_fast_completion_prefix (fast : FastState)
    (semantic : system.State) (state : ProtocolState)
    (events : List NamedClockEvent) (rep : Represents fast semantic)
    (stateEq : protocolState fast = state)
    (invariant : ProtocolInvariant state)
    (finalComplete : protocolComplete (runProtocol state events) = true) :
    ∃ headEvents tailEvents, events = headEvents ++ tailEvents ∧
      protocolComplete (protocolState (runFast fast headEvents)) = true := by
  induction events generalizing fast semantic state with
  | nil =>
      refine ⟨[], [], rfl, ?_⟩
      simpa [runProtocol, runFast, stateEq] using finalComplete
  | cons next rest ih =>
      cases completeEq : protocolComplete state
      · have expectedLt := protocolIncomplete_expected_lt state invariant completeEq
        have invariantCopy := invariant
        rcases invariantCopy with
          ⟨_, nextBound, _, firstBound, secondBound, structural⟩
        have ready : ProtocolReady state :=
          ⟨nextBound, expectedLt, by simpa [sourceToTransform] using firstBound,
            by simpa [transformToChecker] using secondBound⟩
        let nextFast := advance next fast
        let nextSemantic := system.advance next (fun _ _ => 0) semantic
        let nextState := protocolAdvance next state
        have nextRep : Represents nextFast nextSemantic := by
          exact advance_represents next fast semantic rep
        have nextStateEq : protocolState nextFast = nextState := by
          dsimp [nextFast, nextState]
          rw [protocolState_advance next fast semantic rep
            (by simpa [stateEq] using ready)]
          exact congrArg (protocolAdvance next) stateEq
        have nextInvariant : ProtocolInvariant nextState :=
          protocolInvariant_advance next state invariant
        have tailComplete : protocolComplete (runProtocol nextState rest) = true := by
          simpa [runProtocol, nextState] using finalComplete
        obtain ⟨headEvents, tailEvents, restEq, headComplete⟩ :=
          ih nextFast nextSemantic nextState nextRep nextStateEq nextInvariant
            tailComplete
        refine ⟨next :: headEvents, tailEvents, ?_, ?_⟩
        · simp [restEq]
        · simpa [runFast, nextFast] using headComplete
      · refine ⟨[], next :: rest, rfl, ?_⟩
        simpa [runFast, stateEq] using completeEq

/-- Exact semantic binding for the arbitrary-order bounded completion theorem.
The witness prefix is at most 21,510 events and its optimized state represents
the public `System.runEventsFrom` state for the same named-clock events. -/
theorem bounded_completion_semantic_prefix
    (blocks : List (List NamedClockEvent))
    (count : blocks.length = 3585)
    (bounded : BoundedTickBlocks blocks) :
    ∃ headEvents tailEvents,
      blocks.flatten = headEvents ++ tailEvents ∧
      headEvents.length ≤ 21510 ∧
      livenessComplete (runFast reset headEvents) = true ∧
      Represents (runFast reset headEvents)
        (system.runEventsFrom noInputs system.reset headEvents) := by
  have abstractComplete := bounded_completion_schedule blocks count bounded
  obtain ⟨headEvents, tailEvents, split, headComplete⟩ :=
    exists_fast_completion_prefix reset system.reset protocolReset blocks.flatten
      reset_represents protocolState_reset protocolInvariant_reset abstractComplete
  refine ⟨headEvents, tailEvents, split, ?_, ?_, reset_run_represents headEvents⟩
  · have totalLength := boundedTickBlocks_flatten_length blocks bounded
    have headLength : headEvents.length ≤ blocks.flatten.length := by
      rw [split, List.length_append]
      omega
    rw [count] at totalLength
    omega
  · rw [← protocolComplete_protocolState_iff]
    exact headComplete

end Machines.Multiclock.ClockGauntlet.Execution
