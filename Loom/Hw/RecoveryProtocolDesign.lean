-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.RecoveryProtocol
import Loom.Hw.CertifiedDesign
import Loom.Hw.Declarations

/-!
# Compiler-produced recovery endpoint controller

One instance runs in each channel clock domain.  The circuit is an ordinary
single-clock `Design`, so its executable semantics, optimized evaluator,
compiler correctness, and exact text binding are the existing Loom path.
Only request and acknowledgement levels cross between the two instances.

This module proves that a cycle of the generated controller is exactly
`RecoveryProtocol.Endpoint.step` with `tick = true`. The multiclock artifact
layer joins two instances to compiled FIFO controls and a generated top-level
reset coordinator; the remaining whole-wrapper composition boundary is stated
in `MULTICLOCK_BOUNDARY.md`.
-/

namespace Loom.Hw
namespace Chan.RecoveryProtocol.Design

open Chan.RecoveryProtocol

def recoverInput : Reg 1 := ⟨"recover"⟩
def rawPeerRequest : Reg 1 := ⟨"raw_peer_request"⟩
def rawPeerAcknowledge : Reg 1 := ⟨"raw_peer_acknowledge"⟩

def recoverInputSeen : Reg 1 := ⟨"recover_input_seen"⟩
def requestOut : Reg 1 := ⟨"request"⟩
def peerRequest0 : Reg 1 := ⟨"peer_request_0"⟩
def peerRequest1 : Reg 1 := ⟨"peer_request_1"⟩
def acknowledgeOut : Reg 1 := ⟨"acknowledge"⟩
def peerAcknowledge0 : Reg 1 := ⟨"peer_acknowledge_0"⟩
def peerAcknowledge1 : Reg 1 := ⟨"peer_acknowledge_1"⟩
def flushedOut : Reg 1 := ⟨"flushed"⟩

private def one : Expr 1 := .lit 1#1
private def zero : Expr 1 := .lit 0#1

def newRequest : Expr 1 :=
  .and recoverInput.rd (.not recoverInputSeen.rd)

def localFlush : Expr 1 :=
  .and requestOut.rd peerAcknowledge1.rd

/-- Assert the local FIFO reset on the transition into `flushed` and hold it
until the endpoint has completed the four-phase release. -/
def resetHeld : Expr 1 :=
  .or flushedOut.rd localFlush

def idle : Expr 1 :=
  .and (.not recoverInput.rd)
    (.and (.not requestOut.rd)
      (.and (.not peerRequest1.rd) (.not peerAcknowledge1.rd)))

def blocked : Expr 1 :=
  .or recoverInput.rd
    (.or requestOut.rd (.or peerRequest1.rd flushedOut.rd))

def nextRequest : Expr 1 :=
  .mux (.and flushedOut.rd (.not recoverInput.rd)) zero
    (.mux (.or newRequest peerRequest1.rd) one requestOut.rd)

def nextFlushed : Expr 1 :=
  .mux idle zero (.or flushedOut.rd localFlush)

def declarations : Declarations :=
  Declarations.empty
    |>.addInput recoverInput
    |>.addInput rawPeerRequest
    |>.addInput rawPeerAcknowledge
    |>.addReg recoverInputSeen
    |>.addReg requestOut 0 true
    |>.addReg peerRequest0
    |>.addReg peerRequest1
    |>.addReg acknowledgeOut 0 true
    |>.addReg peerAcknowledge0
    |>.addReg peerAcknowledge1
    |>.addReg flushedOut 0 true
    |>.addCombOutput "blocked" blocked
    |>.addCombOutput "local_flush" resetHeld

def endpoint : Loom.Hw.Design :=
  Loom.Hw.Design.ofDecls "channel_recovery_endpoint" declarations
    [⟨"advance_recovery_handshake",
      .seq (recoverInputSeen.set recoverInput.rd) <|
      .seq (requestOut.set nextRequest) <|
      .seq (peerRequest0.set rawPeerRequest.rd) <|
      .seq (peerRequest1.set peerRequest0.rd) <|
      .seq (acknowledgeOut.set peerRequest1.rd) <|
      .seq (peerAcknowledge0.set rawPeerAcknowledge.rd) <|
      .seq (peerAcknowledge1.set peerAcknowledge0.rd)
        (flushedOut.set nextFlushed)⟩]

def bit (value : Bool) : BitVec 1 := if value then 1#1 else 0#1
def bool (value : BitVec 1) : Bool := value != 0

def drive (recover peerRequest peerAcknowledge : Bool) : InEnv :=
  fun name width =>
    if h : width = 1 then
      if name = recoverInput.name then h.symm ▸ bit recover
      else if name = rawPeerRequest.name then h.symm ▸ bit peerRequest
      else if name = rawPeerAcknowledge.name then h.symm ▸ bit peerAcknowledge
      else 0#width
    else 0#width

private def zeroState : St where
  regs := fun _ width => 0#width
  mems := fun _ _ width => 0#width

/-- Canonical concrete register representation of the executable protocol
endpoint. Reachability starts here and `view_cycle` below closes it under
every input combination. -/
def encode (value : RecoveryProtocol.Endpoint) : St where
  regs := ((((((((zeroState.regs
    |>.set recoverInputSeen.name (bit value.recoverInputSeen))
    |>.set requestOut.name (bit value.request))
    |>.set peerRequest0.name (bit value.peerRequest0))
    |>.set peerRequest1.name (bit value.peerRequest1))
    |>.set acknowledgeOut.name (bit value.acknowledge))
    |>.set peerAcknowledge0.name (bit value.peerAcknowledge0))
    |>.set peerAcknowledge1.name (bit value.peerAcknowledge1))
    |>.set flushedOut.name (bit value.flushed))
  mems := zeroState.mems

def view (state : St) : RecoveryProtocol.Endpoint where
  recoverInputSeen := bool (recoverInputSeen.rd.eval state)
  request := bool (requestOut.rd.eval state)
  peerRequest0 := bool (peerRequest0.rd.eval state)
  peerRequest1 := bool (peerRequest1.rd.eval state)
  acknowledge := bool (acknowledgeOut.rd.eval state)
  peerAcknowledge0 := bool (peerAcknowledge0.rd.eval state)
  peerAcknowledge1 := bool (peerAcknowledge1.rd.eval state)
  flushed := bool (flushedOut.rd.eval state)

@[simp] theorem bool_bit (value : Bool) : bool (bit value) = value := by
  cases value <;> decide

@[simp] theorem bool_zero : bool 0#1 = false := by decide
@[simp] theorem bool_one : bool 1#1 = true := by decide

private theorem bitvec_one_cases (value : BitVec 1) :
    value = 0#1 ∨ value = 1#1 := by
  rcases value with ⟨value, bound⟩
  have : value = 0 ∨ value = 1 := by omega
  rcases this with rfl | rfl <;> simp

@[simp] private theorem bool_and (left right : BitVec 1) :
    bool (left &&& right) = (bool left && bool right) := by
  rcases bitvec_one_cases left with rfl | rfl <;>
    rcases bitvec_one_cases right with rfl | rfl <;> decide

@[simp] private theorem bool_or (left right : BitVec 1) :
    bool (left ||| right) = (bool left || bool right) := by
  rcases bitvec_one_cases left with rfl | rfl <;>
    rcases bitvec_one_cases right with rfl | rfl <;> decide

@[simp] private theorem bool_not (value : BitVec 1) :
    bool (~~~value) = !bool value := by
  rcases bitvec_one_cases value with rfl | rfl <;> decide

@[simp] private theorem bool_mux (condition yes no : BitVec 1) :
    bool (if condition = 1#1 then yes else no) =
      if bool condition then bool yes else bool no := by
  rcases bitvec_one_cases condition with rfl | rfl <;>
    rcases bitvec_one_cases yes with rfl | rfl <;>
      rcases bitvec_one_cases no with rfl | rfl <;> decide

/-- The generated controller resets to the protocol's idle endpoint. -/
theorem view_reset : view endpoint.reset = ({} : RecoveryProtocol.Endpoint) := by
  decide

/-- One compiler-source cycle is exactly the executable endpoint transition.
The per-System clock schedule supplies stuttering by simply not cycling an
unticked island, so only the `tick = true` case belongs here. -/
theorem view_encode (value : RecoveryProtocol.Endpoint) :
    view (encode value) = value := by
  ext <;> simp [view, encode, zeroState, RegEnv.set, Reg.rd, Expr.eval,
    recoverInputSeen, requestOut, peerRequest0, peerRequest1,
    acknowledgeOut, peerAcknowledge0, peerAcknowledge1, flushedOut]

/-- The generated `local_flush` output is the protocol's reset-hold level,
including both the edge that enters `flushed` and every cycle spent there. -/
theorem resetHeld_encode (state : RecoveryProtocol.Endpoint)
    (recover peerRequest peerAck : Bool) :
    bool (resetHeld.eval ((encode state).setInputs endpoint.inputs
      (drive recover peerRequest peerAck))) = state.resetHeld := by
  simp [resetHeld, localFlush, RecoveryProtocol.Endpoint.resetHeld,
    RecoveryProtocol.Endpoint.localFlush, encode, endpoint, declarations,
    drive, zeroState, St.setInputs, RegEnv.set, Reg.rd, Reg.input, Expr.eval,
    recoverInput, rawPeerRequest, rawPeerAcknowledge,
    recoverInputSeen, requestOut, peerRequest0, peerRequest1,
    acknowledgeOut, peerAcknowledge0, peerAcknowledge1, flushedOut]

/-- State-independent safety form used by structural composition: whenever
the generated endpoint's public `o_flushed` register is high, its compiled
reset-hold expression is high in that same state. -/
theorem resetHeld_of_flushed_any (state : St)
    (flushed : bool (flushedOut.rd.eval state) = true) :
    bool (resetHeld.eval state) = true := by
  change bool (flushedOut.rd.eval state |||
    (requestOut.rd.eval state &&& peerAcknowledge1.rd.eval state)) = true
  rw [bool_or, flushed]
  rfl

/-- Exact arbitrary-state bridge for the reset output consumed by the
structural FIFO wrapper. -/
theorem resetHeld_view_any (state : St) :
    bool (resetHeld.eval state) = (view state).resetHeld := by
  simp [resetHeld, localFlush, RecoveryProtocol.Endpoint.resetHeld,
    RecoveryProtocol.Endpoint.localFlush, view, Reg.rd, Expr.eval]

theorem view_cycle (state : RecoveryProtocol.Endpoint)
    (recover peerRequest peerAck : Bool) :
    view (endpoint.cycleOpen (drive recover peerRequest peerAck) (encode state)) =
      state.step true recover peerRequest peerAck := by
  ext <;>
    simp [view, endpoint, declarations, Loom.Hw.Design.cycleOpen,
      Loom.Hw.Design.cycle, Act.run, Reg.set, Reg.rd, Reg.input, RegEnv.set, St.setInputs,
      Expr.eval, drive, encode, zeroState,
      recoverInput, rawPeerRequest, rawPeerAcknowledge,
      recoverInputSeen, requestOut, peerRequest0, peerRequest1,
      acknowledgeOut, peerAcknowledge0, peerAcknowledge1, flushedOut,
      RecoveryProtocol.Endpoint.step, RecoveryProtocol.Endpoint.newRequest,
      RecoveryProtocol.Endpoint.localFlush,
      nextRequest, nextFlushed, newRequest, localFlush, resetHeld, idle, one, zero,
      Bool.or_assoc]

/-- Strong form used by induction over the actual compiler-source state:
input coordinates and unrelated state do not need a canonical encoding. -/
theorem view_cycle_any (state : St) (recover peerRequest peerAck : Bool) :
    view (endpoint.cycleOpen (drive recover peerRequest peerAck) state) =
      (view state).step true recover peerRequest peerAck := by
  ext <;>
    simp [view, endpoint, declarations, Loom.Hw.Design.cycleOpen,
      Loom.Hw.Design.cycle, Act.run, Reg.set, Reg.rd, Reg.input, RegEnv.set,
      St.setInputs, Expr.eval, drive,
      recoverInput, rawPeerRequest, rawPeerAcknowledge,
      recoverInputSeen, requestOut, peerRequest0, peerRequest1,
      acknowledgeOut, peerAcknowledge0, peerAcknowledge1, flushedOut,
      RecoveryProtocol.Endpoint.step, RecoveryProtocol.Endpoint.newRequest,
      RecoveryProtocol.Endpoint.localFlush,
      nextRequest, nextFlushed, newRequest, localFlush, resetHeld, idle, one, zero,
      Bool.or_assoc]

/-! ## Two compiled endpoint instances

This model is the compiler-source state of the two endpoint-controller
instances in a generated recovery wrapper.  Queue contents and `recovering`
are specification ghosts; source and sink are the actual ordinary `Design`
states.  The global commit carried by `Coordinated.Request` is derived by the
System coordinator and is not an RTL port on either endpoint. -/
namespace CompiledPair

variable {w : Nat}

structure State (width : Nat) where
  queue : Chan.State width := []
  source : St := endpoint.reset
  sink : St := endpoint.reset
  recovering : Bool := false

def abstract (state : State w) : RecoveryProtocol.State w where
  queue := state.queue
  source := view state.source
  sink := view state.sink
  recovering := state.recovering

def reset (width : Nat) : State width := {}

def sourceNext (state : State w)
    (request : RecoveryProtocol.Coordinated.Request w) : St :=
  if request.endpoint.sourceTick then
    endpoint.cycleOpen
      (drive request.endpoint.sourceRecover
        (view state.sink).request (view state.sink).acknowledge)
      state.source
  else state.source

def sinkNext (state : State w)
    (request : RecoveryProtocol.Coordinated.Request w) : St :=
  if request.endpoint.sinkTick then
    endpoint.cycleOpen
      (drive request.endpoint.sinkRecover
        (view state.source).request (view state.source).acknowledge)
      state.sink
  else state.sink

def step (c : Chan w) (state : State w)
    (request : RecoveryProtocol.Coordinated.Request w) :
    Chan.ConcreteRecoveryResult (State w) w :=
  let logical := RecoveryProtocol.Coordinated.step c (abstract state) request
  { state :=
      { queue := logical.state.queue
        source := sourceNext state request
        sink := sinkNext state request
        recovering := logical.state.recovering }
    accepted := logical.accepted
    delivered := logical.delivered
    recovered := logical.recovered }

/-- Physical-observation form used by the portable FIFO wrapper.  Endpoint
controllers take the same compiled transitions as `step`; the retained queue
advances only by the FIFO transfer that actually succeeded. -/
def stepObserved (c : Chan w) (state : State w)
    (request : RecoveryProtocol.Coordinated.Request w)
    (observed : Chan.Event w) :
    Chan.ConcreteRecoveryResult (State w) w :=
  let logical := RecoveryProtocol.Coordinated.stepObserved
    c (abstract state) request observed
  { state :=
      { queue := logical.state.queue
        source := sourceNext state request
        sink := sinkNext state request
        recovering := logical.state.recovering }
    accepted := logical.accepted
    delivered := logical.delivered
    recovered := logical.recovered }

@[simp] theorem abstract_reset : abstract (reset w) = RecoveryProtocol.reset w := by
  ext <;> simp [abstract, reset, RecoveryProtocol.reset, view_reset]

theorem view_sourceNext (state : State w)
    (request : RecoveryProtocol.Coordinated.Request w) :
    view (sourceNext state request) =
      RecoveryProtocol.nextSource (abstract state) request.endpoint := by
  cases tick : request.endpoint.sourceTick with
  | false =>
      simp [sourceNext, tick, RecoveryProtocol.nextSource,
        RecoveryProtocol.Endpoint.step, abstract]
  | true =>
      simp only [sourceNext, tick, if_true]
      rw [view_cycle_any]
      simp [RecoveryProtocol.nextSource, tick, abstract]

theorem view_sinkNext (state : State w)
    (request : RecoveryProtocol.Coordinated.Request w) :
    view (sinkNext state request) =
      RecoveryProtocol.nextSink (abstract state) request.endpoint := by
  cases tick : request.endpoint.sinkTick with
  | false =>
      simp [sinkNext, tick, RecoveryProtocol.nextSink,
        RecoveryProtocol.Endpoint.step, abstract]
  | true =>
      simp only [sinkNext, tick, if_true]
      rw [view_cycle_any]
      simp [RecoveryProtocol.nextSink, tick, abstract]

/-- The two actual compiler-source endpoint states take exactly the endpoint
transition used by the globally coordinated recovery refinement. -/
theorem abstract_step (c : Chan w) (state : State w)
    (request : RecoveryProtocol.Coordinated.Request w) :
    abstract (step c state request).state =
      (RecoveryProtocol.Coordinated.step c (abstract state) request).state := by
  apply RecoveryProtocol.State.ext
  · rfl
  · exact view_sourceNext state request
  · exact view_sinkNext state request
  · rfl

/-- The compiled endpoint pair also follows the conservative physical-event
model exactly; stale synchronized pointers may delay a transfer without
creating a second endpoint semantics. -/
theorem abstract_stepObserved (c : Chan w) (state : State w)
    (request : RecoveryProtocol.Coordinated.Request w)
    (observed : Chan.Event w) :
    abstract (stepObserved c state request observed).state =
      (RecoveryProtocol.Coordinated.stepObserved
        c (abstract state) request observed).state := by
  apply RecoveryProtocol.State.ext
  · rfl
  · exact view_sourceNext state request
  · exact view_sinkNext state request
  · rfl

theorem stepObserved_event (c : Chan w) (state : State w)
    (request : RecoveryProtocol.Coordinated.Request w)
    (observed : Chan.Event w) :
    (stepObserved c state request observed).event =
      (RecoveryProtocol.Coordinated.stepObserved
        c (abstract state) request observed).event := rfl

/-- In particular, the compiled pair and the coordinated abstract protocol
classify the same transfer/flush event on every step. -/
theorem step_event (c : Chan w) (state : State w)
    (request : RecoveryProtocol.Coordinated.Request w) :
    (step c state request).event =
      (RecoveryProtocol.Coordinated.step c (abstract state) request).event := rfl

/-- At a globally committed event, the actual pre-edge compiled endpoint
states drive both FIFO-half reset inputs high. -/
theorem commit_resets_both (state : State w)
    (request : RecoveryProtocol.Coordinated.Request w)
    (complete : RecoveryProtocol.Coordinated.commits (abstract state) request = true) :
    bool (resetHeld.eval state.source) = true ∧
      bool (resetHeld.eval state.sink) = true := by
  have held := RecoveryProtocol.Coordinated.commits_bothResetHeld
    (abstract state) request complete
  simpa [resetHeld_view_any] using held

end CompiledPair

/-- Executable gates used by the application realization builder. -/
def compilerReady : Bool :=
  Compile.designWFCheck endpoint && endpoint.fastWFB

def certify (ready : compilerReady = true) : CertifiedDesign endpoint := by
  have checks := Bool.and_eq_true_iff.mp ready
  exact CertifiedDesign.ofChecks checks.1 checks.2

example : compilerReady = true := by decide

end Chan.RecoveryProtocol.Design
end Loom.Hw
