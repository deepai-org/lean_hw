-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.ClockGauntlet.Design
import Machines.Multiclock.ClockGauntlet.Bounded
import Machines.Multiclock.ClockGauntlet.Certification
import Loom.Hw.TraceContract

/-! Schedule-independent Clock Gauntlet proof surface. -/

namespace Machines.Multiclock.ClockGauntlet

open Loom.Hw

def noInputs : ExternalInputs := fun _ _ _ _ => 0

def firstEvents (events : List NamedClockEvent) :=
  system.channelEventsFrom noInputs firstConnection system.reset events

def secondEvents (events : List NamedClockEvent) :=
  system.channelEventsFrom noInputs secondConnection system.reset events

def acceptedInputTrace (events : List NamedClockEvent) : List (BitVec 32) :=
  (sourceToTransform.runTrace [] (firstEvents events)).accepted

def transformInputTrace (events : List NamedClockEvent) : List (BitVec 32) :=
  (sourceToTransform.runTrace [] (firstEvents events)).delivered

def acceptedOutputTrace (events : List NamedClockEvent) : List (BitVec 32) :=
  (transformToChecker.runTrace [] (secondEvents events)).accepted

def deliveredOutputTrace (events : List NamedClockEvent) : List (BitVec 32) :=
  (transformToChecker.runTrace [] (secondEvents events)).delivered

/-- The arithmetic used by the ordinary synchronous transform island is
exactly the public pure packet function, independently of any clock ratio. -/
theorem transformExpr_correct (state : St) (value : Expr 32) :
    (transformExpr value).eval state = transformValue (value.eval state) := by
  rfl

/-- On a fresh readable input and writable output, the ordinary transform
island stages exactly the pure transformed word and requests one input pop. -/
theorem transform_transfer_step (state : St) (input : InEnv)
    (canRead : sourceToTransform.canDeq.eval
      (state.setInputs transform.inputs input) = 1#1)
    (canWrite : transformToChecker.canEnq.eval
      (state.setInputs transform.inputs input) = 1#1) :
    let next := transform.cycleOpen input state
    next.regs transformToChecker.sourcePayloadName 32 =
        transformValue (input sourceToTransform.sinkPayloadName 32) ∧
      next.regs transformToChecker.sourceValidName 1 = 1#1 ∧
      next.regs sourceToTransform.sinkPopName 1 = 1#1 := by
  simp [Design.cycleOpen, Design.cycle, transform, Chan.withSource,
    Chan.withSink, transformBody, Chan.enq, Chan.pop, Chan.canDeq,
    Chan.canEnq, Chan.sourceValid, Chan.sourceAccepted, Chan.sourceReady,
    Chan.sourcePayloadName, Chan.sourceValidName, Chan.sourceReadyName,
    Chan.sourceAcceptedName, Chan.sinkPayloadName, Chan.sinkValidName,
    Chan.sinkPopName, Chan.stem, Act.run, Expr.eval, St.setInputs, RegEnv.set,
    sourceToTransform, transformToChecker] at canRead canWrite ⊢
  repeat' first | split
  all_goals simp_all [transformExpr_correct, transformValue, Chan.deq,
    Chan.sinkPayloadName, Chan.stem, Expr.eval]

/-- A previously staged transfer retires both halves of the registered
handshake when the output endpoint reports acceptance. -/
theorem transform_retire_step (state : St) (input : InEnv)
    (valid : transformToChecker.sourceValid.eval
      (state.setInputs transform.inputs input) = 1#1)
    (pop : (Expr.reg 1 sourceToTransform.sinkPopName).eval
      (state.setInputs transform.inputs input) = 1#1)
    (accepted : transformToChecker.sourceAccepted.eval
      (state.setInputs transform.inputs input) = 1#1) :
    let next := transform.cycleOpen input state
    next.regs transformToChecker.sourceValidName 1 = 0#1 ∧
      next.regs sourceToTransform.sinkPopName 1 = 0#1 := by
  simp [Design.cycleOpen, Design.cycle, transform, Chan.withSource,
    Chan.withSink, transformBody, Chan.enq, Chan.pop, Chan.canDeq,
    Chan.canEnq, Chan.sourceValid, Chan.sourceAccepted, Chan.sourceReady,
    Chan.sourcePayloadName, Chan.sourceValidName, Chan.sourceReadyName,
    Chan.sourceAcceptedName, Chan.sinkPayloadName, Chan.sinkValidName,
    Chan.sinkPopName, Chan.stem, Act.run, Expr.eval, St.setInputs, RegEnv.set,
    sourceToTransform, transformToChecker] at valid pop accepted ⊢
  repeat' first | split
  all_goals simp_all

/-- With no transfer already pending, a blocked input or output leaves both
registered handshake halves quiescent. -/
theorem transform_blocked_step (state : St) (input : InEnv)
    (valid : transformToChecker.sourceValid.eval
      (state.setInputs transform.inputs input) = 0#1)
    (pop : (Expr.reg 1 sourceToTransform.sinkPopName).eval
      (state.setInputs transform.inputs input) = 0#1)
    (blocked : sourceToTransform.canDeq.eval
        (state.setInputs transform.inputs input) ≠ 1#1 ∨
      transformToChecker.canEnq.eval
        (state.setInputs transform.inputs input) ≠ 1#1) :
    let next := transform.cycleOpen input state
    next.regs transformToChecker.sourceValidName 1 = 0#1 ∧
      next.regs sourceToTransform.sinkPopName 1 = 0#1 := by
  rcases blocked with blocked | blocked
  all_goals
    simp [Design.cycleOpen, Design.cycle, transform, Chan.withSource,
      Chan.withSink, transformBody, Chan.enq, Chan.pop, Chan.canDeq,
      Chan.canEnq, Chan.sourceValid, Chan.sourceAccepted, Chan.sourceReady,
      Chan.sourcePayloadName, Chan.sourceValidName, Chan.sourceReadyName,
      Chan.sourceAcceptedName, Chan.sinkPayloadName, Chan.sinkValidName,
      Chan.sinkPopName, Chan.stem, Act.run, Expr.eval, St.setInputs, RegEnv.set,
      sourceToTransform, transformToChecker] at valid pop blocked ⊢
  all_goals repeat' first | split
  all_goals simp_all

private def transformInputAt (event : NamedClockEvent) (state : system.State) : InEnv :=
  system.islandInput event state (fun _ _ _ => 0) "transform"

private theorem transform_sink_valid_input (event : NamedClockEvent)
    (state : system.State) :
    transformInputAt event state sourceToTransform.sinkValidName 1 =
      if (System.channelState state firstConnection).isEmpty then 0#1 else 1#1 := by
  have connectionsEq : system.connections = [firstConnection, secondConnection] := by
    rfl
  simp [transformInputAt, System.islandInput, System.inputFor,
    System.connectionInput?, System.connectionQueue, System.channelState,
    System.boolValue, connectionsEq, firstConnection, secondConnection,
    sourceToTransform, transformToChecker, Chan.sinkValidName, Chan.stem]

private theorem transform_sink_payload_input (event : NamedClockEvent)
    (state : system.State) :
    transformInputAt event state sourceToTransform.sinkPayloadName 32 =
      (System.channelState state firstConnection).head?.getD 0 := by
  have connectionsEq : system.connections = [firstConnection, secondConnection] := by
    rfl
  simp [transformInputAt, System.islandInput, System.inputFor,
    System.connectionInput?, System.connectionQueue, System.channelState,
    connectionsEq, firstConnection, secondConnection,
    sourceToTransform, transformToChecker, Chan.sourceReadyName,
    Chan.sourceAcceptedName, Chan.sinkValidName, Chan.sinkPayloadName, Chan.stem]

private theorem transform_source_accepted_input (event : NamedClockEvent)
    (state : system.State) :
    transformInputAt event state transformToChecker.sourceAcceptedName 1 =
      if (system.connectionResult event state secondConnection).accepted then 1#1 else 0#1 := by
  have connectionsEq : system.connections = [firstConnection, secondConnection] := by
    rfl
  simp [transformInputAt, System.islandInput, System.inputFor,
    System.connectionInput?, System.connectionResult, System.connectionQueue,
    System.boolValue, connectionsEq, firstConnection, secondConnection,
    sourceToTransform, transformToChecker, Chan.sourceReadyName,
    Chan.sourceAcceptedName, Chan.sinkValidName, Chan.sinkPayloadName, Chan.stem]

private theorem transform_source_ready_input (event : NamedClockEvent)
    (state : system.State) :
    transformInputAt event state transformToChecker.sourceReadyName 1 =
      if (transformToChecker.step (System.channelState state secondConnection)
          { push := some 0,
            pop := (system.connectionEvent event state secondConnection).pop }).accepted
      then 1#1 else 0#1 := by
  have connectionsEq : system.connections = [firstConnection, secondConnection] := by
    rfl
  simp [transformInputAt, System.islandInput, System.inputFor,
    System.connectionInput?, System.connectionQueue, System.channelState,
    System.boolValue, connectionsEq, firstConnection, secondConnection,
    sourceToTransform, transformToChecker, Chan.sourceReadyName,
    Chan.sourceAcceptedName, Chan.sinkValidName, Chan.sinkPayloadName, Chan.stem]

private theorem Chan.head?_step_no_pop {w : Nat} (c : Chan w) (q : Chan.State w)
    (event : Chan.Event w) (nonempty : q ≠ []) (noPop : event.pop = false) :
    (c.step q event).state.head? = q.head? := by
  rcases event with ⟨push, pop⟩
  simp only at noPop
  subst pop
  cases q with
  | nil => contradiction
  | cons head tail =>
      cases push <;> simp [Chan.step]
      split <;> rfl

private theorem room_after_no_push_of_probe (q : Chan.State 32) (pop : Bool)
    (bounded : q.length ≤ transformToChecker.depth)
    (accepted : (transformToChecker.step q { push := some 0, pop }).accepted = true) :
    (transformToChecker.step q { push := none, pop }).state.length <
      transformToChecker.depth := by
  simp [transformToChecker] at bounded
  simp [transformToChecker, Chan.step] at accepted ⊢
  by_cases popped : pop = true ∧ q ≠ []
  · simp [popped]
    have tail_length : q.tail.length + 1 = q.length := by
      cases q <;> simp_all
    omega
  · simp [popped] at accepted ⊢
    omega

private def pendingValid (state : system.State) : BitVec 1 :=
  transformToChecker.sourceValid.eval (state.island "transform")

private def pendingPop (state : system.State) : BitVec 1 :=
  (Expr.reg 1 sourceToTransform.sinkPopName).eval (state.island "transform")

private def pendingPayload (state : system.State) : BitVec 32 :=
  transformToChecker.sourcePayload.eval (state.island "transform")

/-- The transform's registered source and sink requests represent one and the
same pending word. The input queue retains that word until the registered pop
is observed, so no extra ghost queue is needed. -/
private def TransferPending (state : system.State) : Prop :=
  pendingValid state = pendingPop state ∧
  (pendingValid state = 1#1 →
    (System.channelState state firstConnection).head? = some
      (pendingPayload state |> fun _ =>
        (System.channelState state firstConnection).head?.getD 0) ∧
    pendingPayload state = transformValue
      ((System.channelState state firstConnection).head?.getD 0) ∧
    (System.channelState state secondConnection).length < transformToChecker.depth)

private theorem transferPending_reset : TransferPending system.reset := by
  have transformFound : system.findIsland? "transform" =
      some ⟨"transform", "transform_clk", transform⟩ := by rfl
  have transformReset : (system.reset.island "transform") = transform.reset := by
    simp [System.reset, transformFound]
  have firstReset := System.channelState_reset system firstConnection (by rfl)
  have secondReset := System.channelState_reset system secondConnection (by rfl)
  unfold TransferPending
  rw [show pendingValid system.reset = 0#1 by
      simp [pendingValid, transformReset, transform, Chan.withSource,
        Chan.withSink, transformBody, sourceToTransform, transformToChecker,
        Chan.sourceValid, Chan.sourceValidName, Chan.sourcePayloadName,
        Chan.sinkPopName, Chan.stem, Design.reset, Expr.eval, RegEnv.set]]
  rw [show pendingPop system.reset = 0#1 by
      simp [pendingPop, transformReset, transform, Chan.withSource, Chan.withSink,
        transformBody, sourceToTransform, transformToChecker,
        Chan.sourceValidName, Chan.sourcePayloadName, Chan.sinkPopName,
        Chan.stem, Design.reset, Expr.eval, RegEnv.set]]
  simp [firstReset, secondReset,
    firstConnection, secondConnection, sourceToTransform, transformToChecker,
    pendingValid, pendingPop]

private theorem bit_cases (value : BitVec 1) : value = 0#1 ∨ value = 1#1 := by
  have bound : value.toNat < 2 := by simpa using value.isLt
  have cases : value.toNat = 0 ∨ value.toNat = 1 := by omega
  rcases cases with zero | one
  · exact Or.inl (BitVec.toNat_inj.mp (by simp [zero]))
  · exact Or.inr (BitVec.toNat_inj.mp (by simp [one]))

set_option maxRecDepth 10000 in
/-- Every pending registered pop from the first crossing and push into the
second crossing is one atomic logical transform transfer. -/
private theorem transfer_step_coupling (event : NamedClockEvent)
    (state : system.State) (pending : TransferPending state) :
    (transformToChecker.acceptedValues
        (System.channelState state secondConnection)
        (system.connectionEvent event state secondConnection)) =
      (sourceToTransform.deliveredValues
        (System.channelState state firstConnection)
        (system.connectionEvent event state firstConnection)).map transformValue := by
  rcases pending with ⟨requests, payload⟩
  have transformFound : system.findIsland? "transform" =
      some ⟨"transform", "transform_clk", transform⟩ := by rfl
  have checkerFound : system.findIsland? "checker" =
      some ⟨"checker", "checker_clk", checker⟩ := by rfl
  rcases bit_cases (pendingValid state) with valid | valid
  · have pop : pendingPop state = 0#1 := by simpa [valid] using requests.symm
    have validReg : (state.island "transform").regs
        transformToChecker.sourceValidName 1 = 0#1 := by
      simpa [pendingValid, Chan.sourceValid, Expr.eval] using valid
    have popReg : (state.island "transform").regs
        sourceToTransform.sinkPopName 1 = 0#1 := by
      simpa [pendingPop, Expr.eval] using pop
    simp [System.connectionEvent, firstConnection, secondConnection,
      sourceToTransform, transformToChecker, transformFound, checkerFound,
      Chan.acceptedValues, Chan.deliveredValues, Chan.step, Chan.sourceValid,
      Chan.sourcePayload, Chan.sourceValidName, Chan.sourcePayloadName,
      Chan.sinkPopName, Chan.stem, Expr.eval] at validReg popReg ⊢
    simp [validReg, popReg]
  · have pop : pendingPop state = 1#1 := by simpa [valid] using requests.symm
    have facts := payload valid
    rcases facts with ⟨nonempty, transformed, room⟩
    have validReg : (state.island "transform").regs
        transformToChecker.sourceValidName 1 = 1#1 := by
      simpa [pendingValid, Chan.sourceValid, Expr.eval] using valid
    have popReg : (state.island "transform").regs
        sourceToTransform.sinkPopName 1 = 1#1 := by
      simpa [pendingPop, Expr.eval] using pop
    have payloadReg : (state.island "transform").regs
        transformToChecker.sourcePayloadName 32 = transformValue
          ((System.channelState state firstConnection).head?.getD 0) := by
      simpa [pendingPayload, Chan.sourcePayload, Expr.eval] using transformed
    have firstNotEmpty : !(System.channelState state firstConnection).isEmpty = true := by
      cases queue : System.channelState state firstConnection with
      | nil => simp [queue] at nonempty
      | cons head tail => rfl
    have secondRoom :
        (System.channelState state secondConnection).length < 2 := by
      simpa [transformToChecker] using room
    simp [System.connectionEvent, firstConnection, secondConnection,
      sourceToTransform, transformToChecker, transformFound, checkerFound,
      Chan.acceptedValues, Chan.deliveredValues, Chan.step, Chan.sourceValid,
      Chan.sourcePayload, Chan.sourceValidName, Chan.sourcePayloadName,
      Chan.sinkPopName, Chan.stem, Expr.eval] at validReg popReg payloadReg firstNotEmpty secondRoom nonempty ⊢
    by_cases tick : event.fires "transform_clk" = true
    · simp [tick, validReg, popReg, payloadReg, firstNotEmpty, secondRoom]
      cases queue : System.channelState state firstConnection with
      | nil =>
          have queue' : System.channelState state
              ⟨32, ({ name := "source_to_transform", depth := 2 } : Chan 32),
                "source", "transform"⟩ = [] := by
            simpa [firstConnection, sourceToTransform] using queue
          rw [queue'] at firstNotEmpty
          contradiction
      | cons head tail =>
          have queue' : System.channelState state
              ⟨32, ({ name := "source_to_transform", depth := 2 } : Chan 32),
                "source", "transform"⟩ = head :: tail := by
            simpa [firstConnection, sourceToTransform] using queue
          rw [queue']
          rfl
    · simp [tick]

set_option maxRecDepth 10000 in
private theorem transferPending_advance (event : NamedClockEvent)
    (state : system.State) (pending : TransferPending state)
    (firstBound : (System.channelState state firstConnection).length ≤
      sourceToTransform.depth)
    (secondBound : (System.channelState state secondConnection).length ≤
      transformToChecker.depth) :
    TransferPending (system.advance event (fun _ _ _ => 0) state) := by
  rcases pending with ⟨requests, payload⟩
  have transformFound : system.findIsland? "transform" =
      some ⟨"transform", "transform_clk", transform⟩ := by rfl
  have firstFound : system.connections.find? (fun candidate =>
      candidate.chan.name == firstConnection.chan.name) = some firstConnection := by rfl
  have secondFound : system.connections.find? (fun candidate =>
      candidate.chan.name == secondConnection.chan.name) = some secondConnection := by rfl
  have firstNext := System.channelState_advance system event (fun _ _ _ => 0)
    state firstConnection firstFound
  have secondNext := System.channelState_advance system event (fun _ _ _ => 0)
    state secondConnection secondFound
  by_cases tick : event.fires "transform_clk" = true
  · have transformNext := System.advance_island_ticked system event
      (fun _ _ _ => 0) state ⟨"transform", "transform_clk", transform⟩
      transformFound tick
    rcases bit_cases (pendingValid state) with valid | valid
    · have pop : pendingPop state = 0#1 := by simpa [valid] using requests.symm
      have validReg : (state.island "transform").regs
          transformToChecker.sourceValidName 1 = 0#1 := by
        simpa [pendingValid, Chan.sourceValid, Expr.eval] using valid
      have popReg : (state.island "transform").regs
          sourceToTransform.sinkPopName 1 = 0#1 := by
        simpa [pendingPop, Expr.eval] using pop
      let input := transformInputAt event state
      let driven := (state.island "transform").setInputs transform.inputs input
      have validDriven : transformToChecker.sourceValid.eval driven = 0#1 := by
        simp [driven, transform, Chan.withSource, Chan.withSink, St.setInputs,
          Chan.sourceValid, Expr.eval]
        exact validReg
      have popDriven : (Expr.reg 1 sourceToTransform.sinkPopName).eval driven = 0#1 := by
        simp [driven, transform, Chan.withSource, Chan.withSink, St.setInputs, Expr.eval]
        exact popReg
      by_cases canRead : sourceToTransform.canDeq.eval driven = 1#1
      · by_cases canWrite : transformToChecker.canEnq.eval driven = 1#1
        · have staged := transform_transfer_step (state.island "transform") input
            canRead canWrite
          have nextTransform : (system.advance event (fun _ _ _ => 0) state).island
              "transform" = transform.cycleOpen input (state.island "transform") := by
            simpa [input, transformInputAt] using transformNext
          have nextPayload : pendingPayload
              (system.advance event (fun _ _ _ => 0) state) =
              transformValue (input sourceToTransform.sinkPayloadName 32) := by
            rw [pendingPayload, nextTransform]
            simpa [Chan.sourcePayload, Expr.eval] using staged.1
          have nextValid : pendingValid
              (system.advance event (fun _ _ _ => 0) state) = 1#1 := by
            rw [pendingValid, nextTransform]
            simpa [Chan.sourceValid, Expr.eval] using staged.2.1
          have nextPop : pendingPop
              (system.advance event (fun _ _ _ => 0) state) = 1#1 := by
            rw [pendingPop, nextTransform]
            simpa [Expr.eval] using staged.2.2
          have sinkDriven : (Expr.reg 1 sourceToTransform.sinkValidName).eval driven =
              input sourceToTransform.sinkValidName 1 := by
            simp [driven, transform, Chan.withSource, Chan.withSink, St.setInputs,
              Expr.eval, sourceToTransform, transformToChecker, Chan.sinkValidName,
              Chan.sinkPayloadName, Chan.sourceReadyName, Chan.sourceAcceptedName,
              Chan.stem, transformBody]
          have sinkInput : input sourceToTransform.sinkValidName 1 =
              if (System.channelState state firstConnection).isEmpty then 0#1 else 1#1 := by
            simpa [input] using transform_sink_valid_input event state
          have firstNonempty : System.channelState state firstConnection ≠ [] := by
            intro empty
            rw [show sourceToTransform.canDeq.eval driven =
                (Expr.reg 1 sourceToTransform.sinkValidName).eval driven &&&
                  ~~~(Expr.reg 1 sourceToTransform.sinkPopName).eval driven by
              rfl] at canRead
            rw [popDriven, sinkDriven, sinkInput, empty] at canRead
            contradiction
          have firstPopFalse :
              (system.connectionEvent event state firstConnection).pop = false := by
            simp [System.connectionEvent, firstConnection, transformFound, tick,
              sourceToTransform, Chan.sinkPopName, Chan.stem, Expr.eval]
            simpa [sourceToTransform, Chan.sinkPopName, Chan.stem] using popReg
          have firstHeadNext :
              (System.channelState (system.advance event (fun _ _ _ => 0) state)
                firstConnection).head? =
              (System.channelState state firstConnection).head? := by
            rw [firstNext]
            exact Chan.head?_step_no_pop sourceToTransform
              (System.channelState state firstConnection)
              (system.connectionEvent event state firstConnection)
              firstNonempty firstPopFalse
          have firstSome : (System.channelState state firstConnection).head? =
              some ((System.channelState state firstConnection).head?.getD 0) := by
            cases queue : System.channelState state firstConnection with
            | nil => simp [queue] at firstNonempty
            | cons head tail => simp [queue]
          have payloadInput : input sourceToTransform.sinkPayloadName 32 =
              (System.channelState state firstConnection).head?.getD 0 := by
            simpa [input] using transform_sink_payload_input event state
          have secondRoomNext :
              (System.channelState (system.advance event (fun _ _ _ => 0) state)
                secondConnection).length < transformToChecker.depth := by
            rw [secondNext]
            have readyDriven : transformToChecker.sourceReady.eval driven =
                input transformToChecker.sourceReadyName 1 := by
              simp [driven, transform, Chan.withSource, Chan.withSink, St.setInputs,
                Chan.sourceReady, Expr.eval, sourceToTransform, transformToChecker,
                Chan.sinkValidName, Chan.sinkPayloadName, Chan.sourceReadyName,
                Chan.sourceAcceptedName, Chan.stem, transformBody]
            have readyInput : input transformToChecker.sourceReadyName 1 =
                if (transformToChecker.step (System.channelState state secondConnection)
                    { push := some 0,
                      pop := (system.connectionEvent event state secondConnection).pop }).accepted
                then 1#1 else 0#1 := by
              simpa [input] using transform_source_ready_input event state
            have ready : input transformToChecker.sourceReadyName 1 = 1#1 := by
              simp only [Chan.canEnq, Expr.eval] at canWrite
              rw [validDriven, readyDriven] at canWrite
              rcases bit_cases (transformToChecker.sourceAccepted.eval driven) with
                accepted | accepted <;> simp [accepted] at canWrite
              all_goals
                have numeric := congrArg BitVec.toNat canWrite
                have bound := (input transformToChecker.sourceReadyName 1).isLt
                apply BitVec.toNat_inj.mp
                simp at numeric bound ⊢
                omega
            have probeAccepted :
                (transformToChecker.step (System.channelState state secondConnection)
                    { push := some 0,
                      pop := (system.connectionEvent event state secondConnection).pop }).accepted = true := by
              rw [readyInput] at ready
              cases acceptedEq : (transformToChecker.step
                  (System.channelState state secondConnection)
                  { push := some 0,
                    pop := (system.connectionEvent event state secondConnection).pop }).accepted with
              | false =>
                  rw [acceptedEq] at ready
                  contradiction
              | true => rfl
            have secondPushNone :
                (system.connectionEvent event state secondConnection).push = none := by
              simp [System.connectionEvent, secondConnection, transformFound, tick,
                transformToChecker, Chan.sourceValid, Expr.eval]
              simpa [transformToChecker, Chan.sourceValidName, Chan.stem] using validReg
            unfold System.connectionResult
            rw [show system.connectionEvent event state secondConnection =
                { push := none,
                  pop := (system.connectionEvent event state secondConnection).pop } by
              cases actionEq : system.connectionEvent event state secondConnection with
              | mk push pop =>
                  have pushNone : push = none := by
                    simpa [actionEq] using secondPushNone
                  subst push
                  rfl]
            exact room_after_no_push_of_probe _ _ secondBound probeAccepted
          unfold TransferPending
          refine ⟨?_, ?_⟩
          · rw [nextValid, nextPop]
          · intro _
            refine ⟨?_, ?_, secondRoomNext⟩
            · rw [firstHeadNext]
              exact firstSome
            · rw [nextPayload, payloadInput, firstHeadNext]
        · have blocked := transform_blocked_step (state.island "transform") input
            (by simpa [driven] using validDriven) (by simpa [driven] using popDriven)
            (Or.inr canWrite)
          have nextTransform : (system.advance event (fun _ _ _ => 0) state).island
              "transform" = transform.cycleOpen input (state.island "transform") := by
            simpa [input, transformInputAt] using transformNext
          unfold TransferPending
          have nextValid : pendingValid
              (system.advance event (fun _ _ _ => 0) state) = 0#1 := by
            rw [pendingValid, nextTransform]
            simpa [Chan.sourceValid, Expr.eval] using blocked.1
          have nextPop : pendingPop
              (system.advance event (fun _ _ _ => 0) state) = 0#1 := by
            rw [pendingPop, nextTransform]
            simpa [Expr.eval] using blocked.2
          refine ⟨?_, ?_⟩
          · rw [nextValid, nextPop]
          · intro impossible
            rw [nextValid] at impossible
            contradiction
      · have blocked := transform_blocked_step (state.island "transform") input
          (by simpa [driven] using validDriven) (by simpa [driven] using popDriven)
          (Or.inl canRead)
        have nextTransform : (system.advance event (fun _ _ _ => 0) state).island
            "transform" = transform.cycleOpen input (state.island "transform") := by
          simpa [input, transformInputAt] using transformNext
        unfold TransferPending
        have nextValid : pendingValid
            (system.advance event (fun _ _ _ => 0) state) = 0#1 := by
          rw [pendingValid, nextTransform]
          simpa [Chan.sourceValid, Expr.eval] using blocked.1
        have nextPop : pendingPop
            (system.advance event (fun _ _ _ => 0) state) = 0#1 := by
          rw [pendingPop, nextTransform]
          simpa [Expr.eval] using blocked.2
        refine ⟨?_, ?_⟩
        · rw [nextValid, nextPop]
        · intro impossible
          rw [nextValid] at impossible
          contradiction
    · have pop : pendingPop state = 1#1 := by simpa [valid] using requests.symm
      rcases payload valid with ⟨_, _, room⟩
      have checkerFound : system.findIsland? "checker" =
          some ⟨"checker", "checker_clk", checker⟩ := by rfl
      have validReg : (state.island "transform").regs
          transformToChecker.sourceValidName 1 = 1#1 := by
        simpa [pendingValid, Chan.sourceValid, Expr.eval] using valid
      have popReg : (state.island "transform").regs
          sourceToTransform.sinkPopName 1 = 1#1 := by
        simpa [pendingPop, Expr.eval] using pop
      have roomLiteral : (System.channelState state
          ⟨32, ({ name := "transform_to_checker", depth := 2 } : Chan 32),
            "transform", "checker"⟩).length < 2 := by
        simpa [secondConnection, transformToChecker] using room
      have validLiteral : (state.island "transform").regs
          "__loom_chan_transform_to_checker_src_valid" 1 = 1#1 := by
        simpa [transformToChecker, Chan.sourceValidName, Chan.stem] using validReg
      have roomQueue : (System.connectionQueue state
          ⟨32, ({ name := "transform_to_checker", depth := 2 } : Chan 32),
            "transform", "checker"⟩).length < 2 := by
        simpa [System.channelState] using roomLiteral
      have secondAccepted :
          (system.connectionResult event state secondConnection).accepted = true := by
        unfold System.connectionResult
        simp [System.connectionEvent, secondConnection, transformFound, checkerFound,
          tick, transformToChecker, Chan.step, Chan.sourceValid,
          Chan.sourcePayload, Expr.eval, validLiteral, roomQueue]
        intro zero
        have zeroLiteral : (state.island "transform").regs
            "__loom_chan_transform_to_checker_src_valid" 1 = 0#1 := by
          simpa [Chan.sourceValidName, Chan.stem] using zero
        rw [validLiteral] at zeroLiteral
        contradiction
      let input := transformInputAt event state
      have acceptedInput : input transformToChecker.sourceAcceptedName 1 = 1#1 := by
        dsimp [input]
        rw [transform_source_accepted_input]
        simp [secondAccepted]
      have validDriven : transformToChecker.sourceValid.eval
          ((state.island "transform").setInputs transform.inputs input) = 1#1 := by
        simp [transform, Chan.withSource, Chan.withSink, St.setInputs, RegEnv.set,
          Chan.sourceValid, Expr.eval]
        exact validReg
      have popDriven : (Expr.reg 1 sourceToTransform.sinkPopName).eval
          ((state.island "transform").setInputs transform.inputs input) = 1#1 := by
        simp [transform, Chan.withSource, Chan.withSink, St.setInputs, RegEnv.set,
          Expr.eval]
        exact popReg
      have acceptedDriven : transformToChecker.sourceAccepted.eval
          ((state.island "transform").setInputs transform.inputs input) = 1#1 := by
        simp [transform, Chan.withSource, Chan.withSink, transformBody,
          St.setInputs, RegEnv.set, Chan.sourceAccepted, Expr.eval, acceptedInput,
          sourceToTransform, transformToChecker, Chan.sourceAcceptedName,
          Chan.sinkValidName, Chan.stem]
        simpa [transformToChecker, Chan.sourceAcceptedName, Chan.stem] using acceptedInput
      have retired := transform_retire_step (state.island "transform") input
        validDriven popDriven acceptedDriven
      have nextTransform : (system.advance event (fun _ _ _ => 0) state).island
          "transform" = transform.cycleOpen input (state.island "transform") := by
        simpa [input, transformInputAt] using transformNext
      have nextValid : pendingValid (system.advance event (fun _ _ _ => 0) state) = 0#1 := by
        rw [pendingValid, nextTransform]
        exact retired.1
      have nextPop : pendingPop (system.advance event (fun _ _ _ => 0) state) = 0#1 := by
        rw [pendingPop, nextTransform]
        exact retired.2
      unfold TransferPending
      refine ⟨?_, ?_⟩
      · rw [nextValid, nextPop]
      · intro impossible
        rw [nextValid] at impossible
        contradiction
  · have unticked : event.fires "transform_clk" = false :=
      Bool.eq_false_of_not_eq_true tick
    have transformNext := System.advance_island_unticked system event
      (fun _ _ _ => 0) state ⟨"transform", "transform_clk", transform⟩
      transformFound unticked
    rcases bit_cases (pendingValid state) with valid | valid
    · have pop : pendingPop state = 0#1 := by simpa [valid] using requests.symm
      unfold TransferPending
      have nextValid : pendingValid (system.advance event (fun _ _ _ => 0) state) = 0#1 := by
        unfold pendingValid
        rw [show (system.advance event (fun _ _ _ => 0) state).island "transform" =
          state.island "transform" by simpa using transformNext]
        simpa [pendingValid, Chan.sourceValid, Expr.eval] using valid
      have nextPop : pendingPop (system.advance event (fun _ _ _ => 0) state) = 0#1 := by
        unfold pendingPop
        rw [show (system.advance event (fun _ _ _ => 0) state).island "transform" =
          state.island "transform" by simpa using transformNext]
        simpa [pendingPop, Expr.eval] using pop
      refine ⟨?_, ?_⟩
      · rw [nextValid, nextPop]
      · intro impossible
        rw [nextValid] at impossible
        contradiction
    · have pop : pendingPop state = 1#1 := by simpa [valid] using requests.symm
      rcases payload valid with ⟨nonempty, transformed, room⟩
      have sourceFound : system.findIsland? "source" =
          some ⟨"source", "source_clk", source⟩ := by rfl
      have checkerFound : system.findIsland? "checker" =
          some ⟨"checker", "checker_clk", checker⟩ := by rfl
      have sameTransform : (system.advance event (fun _ _ _ => 0) state).island
          "transform" = state.island "transform" := by simpa using transformNext
      have nextValid : pendingValid (system.advance event (fun _ _ _ => 0) state) = 1#1 := by
        unfold pendingValid
        rw [sameTransform]
        simpa [pendingValid, Chan.sourceValid, Expr.eval] using valid
      have nextPop : pendingPop (system.advance event (fun _ _ _ => 0) state) = 1#1 := by
        unfold pendingPop
        rw [sameTransform]
        simpa [pendingPop, Expr.eval] using pop
      have nextPayload : pendingPayload (system.advance event (fun _ _ _ => 0) state) =
          pendingPayload state := by
        unfold pendingPayload
        rw [sameTransform]
      have firstHeadNext :
          (System.channelState (system.advance event (fun _ _ _ => 0) state)
            firstConnection).head? =
          (System.channelState state firstConnection).head? := by
        rw [firstNext]
        unfold System.connectionResult
        simp [System.connectionEvent, firstConnection, sourceFound, transformFound,
          unticked, sourceToTransform, Chan.step]
        cases queue : System.channelState state firstConnection with
        | nil => simp [queue] at nonempty
        | cons head tail =>
            have queue' : System.connectionQueue state
                ⟨32, ({ name := "source_to_transform", depth := 2 } : Chan 32),
                  "source", "transform"⟩ = head :: tail := by
              simpa [System.channelState, firstConnection, sourceToTransform] using queue
            change _ = List.head? (System.connectionQueue state
              ⟨32, ({ name := "source_to_transform", depth := 2 } : Chan 32),
                "source", "transform"⟩)
            rw [queue']
            by_cases push : event.fires "source_clk" = true ∧
                ¬Expr.eval (state.island "source")
                  ({ name := "source_to_transform", depth := 2 } : Chan 32).sourceValid = 0#1
            · simp [push]
              split <;> rfl
            · simp [push]
      have secondRoomNext :
          (System.channelState (system.advance event (fun _ _ _ => 0) state)
            secondConnection).length < transformToChecker.depth := by
        rw [secondNext]
        unfold System.connectionResult
        simp [System.connectionEvent, secondConnection, transformFound, checkerFound,
          unticked, transformToChecker, Chan.step] at room ⊢
        cases queue : System.channelState state secondConnection with
        | nil =>
            have queue' : System.connectionQueue state
                ⟨32, ({ name := "transform_to_checker", depth := 2 } : Chan 32),
                  "transform", "checker"⟩ = [] := by
              simpa [System.channelState, secondConnection, transformToChecker] using queue
            rw [queue']
            simp
        | cons head tail =>
            have queue' : System.connectionQueue state
                ⟨32, ({ name := "transform_to_checker", depth := 2 } : Chan 32),
                  "transform", "checker"⟩ = head :: tail := by
              simpa [System.channelState, secondConnection, transformToChecker] using queue
            have queueState' : System.channelState state
                ⟨32, ({ name := "transform_to_checker", depth := 2 } : Chan 32),
                  "transform", "checker"⟩ = head :: tail := by
              simpa [secondConnection, transformToChecker] using queue
            have short : (head :: tail).length < 2 := by
              have room' : (System.channelState state
                  ⟨32, ({ name := "transform_to_checker", depth := 2 } : Chan 32),
                    "transform", "checker"⟩).length < 2 := by
                simpa [secondConnection, transformToChecker] using room
              rwa [queueState'] at room'
            rw [queue']
            cases tail with
            | nil => split <;> simp
            | cons next rest => simp at short; omega
      unfold TransferPending
      refine ⟨?_, ?_⟩
      · rw [nextValid, nextPop]
      · intro _
        refine ⟨?_, ?_, secondRoomNext⟩
        · rw [firstHeadNext]
          exact nonempty
        · rw [nextPayload, firstHeadNext]
          exact transformed

private theorem run_preserves_transfer_facts (state : system.State)
    (events : List NamedClockEvent) (pending : TransferPending state)
    (firstBound : (System.channelState state firstConnection).length ≤
      sourceToTransform.depth)
    (secondBound : (System.channelState state secondConnection).length ≤
      transformToChecker.depth) :
    let final := system.runEventsFrom noInputs state events
    TransferPending final ∧
      (System.channelState final firstConnection).length ≤ sourceToTransform.depth ∧
      (System.channelState final secondConnection).length ≤ transformToChecker.depth := by
  induction events generalizing state with
  | nil => exact ⟨pending, firstBound, secondBound⟩
  | cons event rest ih =>
      simp only [System.runEventsFrom]
      apply ih
      · exact transferPending_advance event state pending firstBound secondBound
      · rw [System.channelState_advance system event (noInputs state.time) state
            firstConnection (by rfl)]
        exact sourceToTransform.noOverflow _ _ firstBound
      · rw [System.channelState_advance system event (noInputs state.time) state
            secondConnection (by rfl)]
        exact transformToChecker.noOverflow _ _ secondBound

private theorem transfer_facts_from_reset (events : List NamedClockEvent) :
    let final := system.runEventsFrom noInputs system.reset events
    TransferPending final ∧
      (System.channelState final firstConnection).length ≤ sourceToTransform.depth ∧
      (System.channelState final secondConnection).length ≤ transformToChecker.depth := by
  apply run_preserves_transfer_facts system.reset events transferPending_reset
  · rw [System.channelState_reset system firstConnection (by rfl)]
    simp
  · rw [System.channelState_reset system secondConnection (by rfl)]
    simp

private theorem run_transfer_coupling (state : system.State)
    (events : List NamedClockEvent) (pending : TransferPending state)
    (firstBound : (System.channelState state firstConnection).length ≤
      sourceToTransform.depth)
    (secondBound : (System.channelState state secondConnection).length ≤
      transformToChecker.depth) :
    (transformToChecker.runTrace (System.channelState state secondConnection)
      (system.channelEventsFrom noInputs secondConnection state events)).accepted =
    (sourceToTransform.runTrace (System.channelState state firstConnection)
      (system.channelEventsFrom noInputs firstConnection state events)).delivered.map
        transformValue := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [System.channelEventsFrom, Chan.runTrace, List.map_append]
      rw [transfer_step_coupling event state pending]
      congr 1
      change (transformToChecker.runTrace
          (system.connectionResult event state secondConnection).state
          (system.channelEventsFrom noInputs secondConnection
            (system.advance event (noInputs state.time) state) rest)).accepted =
        (sourceToTransform.runTrace
          (system.connectionResult event state firstConnection).state
          (system.channelEventsFrom noInputs firstConnection
            (system.advance event (noInputs state.time) state) rest)).delivered.map
              transformValue
      rw [← System.channelState_advance system event (noInputs state.time) state
          secondConnection (by rfl)]
      rw [← System.channelState_advance system event (noInputs state.time) state
          firstConnection (by rfl)]
      apply ih
      · exact transferPending_advance event state pending firstBound secondBound
      · rw [System.channelState_advance system event (noInputs state.time) state
            firstConnection (by rfl)]
        exact sourceToTransform.noOverflow _ _ firstBound
      · rw [System.channelState_advance system event (noInputs state.time) state
            secondConnection (by rfl)]
        exact transformToChecker.noOverflow _ _ secondBound

/-- Under every finite named-clock schedule, the transform accepts exactly
the pure transform of the words delivered by the first crossing. -/
theorem transform_trace_coupling (events : List NamedClockEvent) :
    acceptedOutputTrace events = (transformInputTrace events).map transformValue := by
  apply run_transfer_coupling system.reset events transferPending_reset
  · rw [System.channelState_reset system firstConnection (by rfl)]
    simp
  · rw [System.channelState_reset system secondConnection (by rfl)]
    simp

/-- The first crossing loses, duplicates, corrupts, and reorders no accepted
packet under any finite named-clock schedule. -/
theorem first_trace_conservation (events : List NamedClockEvent) :
    acceptedInputTrace events = transformInputTrace events ++
      ((by rfl : firstConnection.width = 32) ▸
        System.channelState (system.runEventsFrom noInputs system.reset events)
          firstConnection) := by
  simpa [acceptedInputTrace, transformInputTrace, firstEvents] using
    System.channelTraceConservation system noInputs firstConnection (by rfl)
      system.reset events

/-- The output crossing has the same schedule-independent FIFO trace law. -/
theorem second_trace_conservation (events : List NamedClockEvent) :
    acceptedOutputTrace events = deliveredOutputTrace events ++
      ((by rfl : secondConnection.width = 32) ▸
        System.channelState (system.runEventsFrom noInputs system.reset events)
          secondConnection) := by
  simpa [acceptedOutputTrace, deliveredOutputTrace, secondEvents] using
    System.channelTraceConservation system noInputs secondConnection (by rfl)
      system.reset events

/-- Schedule-independent end-to-end safety for the complete three-island
system. Every output delivered to the checker is an ordered prefix of the
pure transform of accepted source packets; `inFlight` is exactly the two FIFO
backlogs, with the output crossing first and the transformed input crossing
second. -/
theorem end_to_end_trace_safety (events : List NamedClockEvent) :
    ∃ inFlight : List (BitVec 32),
      (acceptedInputTrace events).map transformValue =
        deliveredOutputTrace events ++ inFlight := by
  let final := system.runEventsFrom noInputs system.reset events
  let firstQueue : List (BitVec 32) :=
    (by rfl : firstConnection.width = 32) ▸
      System.channelState final firstConnection
  let secondQueue : List (BitVec 32) :=
    (by rfl : secondConnection.width = 32) ▸
      System.channelState final secondConnection
  refine ⟨secondQueue ++ firstQueue.map transformValue, ?_⟩
  have first := congrArg (List.map transformValue) (first_trace_conservation events)
  have coupled := transform_trace_coupling events
  have second := second_trace_conservation events
  dsimp [final, firstQueue, secondQueue] at first second ⊢
  rw [List.map_append] at first
  rw [first, ← coupled, second]
  simp [List.append_assoc]

/-- The same result through Loom's small generic trace-contract surface. The
Gauntlet-specific proof above establishes the island contract; downstream
composition need only consume this schedule-free relation. -/
theorem end_to_end_contract (events : List NamedClockEvent) :
    TraceContract.mapPrefix transformValue
      (acceptedInputTrace events) (deliveredOutputTrace events) :=
  end_to_end_trace_safety events

end Machines.Multiclock.ClockGauntlet
