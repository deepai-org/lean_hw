-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ChanRefinement

/-!
# Certified one-entry toggle mailbox

This is Loom's small stock CDC implementation for a depth-one channel.  The
source latches a payload and flips `sourcePhase`; the destination may observe
that phase on a later tick, and delivery flips `ackPhase`.  The acknowledgement
may likewise reach the source later.  `publish` and `acknowledge` are explicit
adversarial synchronizer outcomes: they may delay progress arbitrarily, while
the proof below holds for every choice.

The model is a reference implementation, not the meaning of `Chan`.  A user
may select it, the Gray FIFO, or a separately certified implementation.
-/

namespace Loom.Hw.Cdc.ToggleChan

open Loom.Hw

variable {w : Nat}

structure Request (width : Nat) where
  sourceTick : Bool := false
  sinkTick : Bool := false
  push : Option (BitVec width) := none
  pop : Bool := false
  publish : Bool := false
  acknowledge : Bool := false
  deriving DecidableEq, Repr

structure State (width : Nat) where
  payload : BitVec width
  pending : Bool
  sourceBusy : Bool
  visible : Bool
  sourcePhase : Bool
  sinkPhase : Bool
  ackPhase : Bool
  sourceAckPhase : Bool

def reset (width : Nat) : State width :=
  ⟨0, false, false, false, false, false, false, false⟩

def accepted (state : State w) (request : Request w) : Option (BitVec w) :=
  if request.sourceTick && !state.sourceBusy then request.push else none

def delivered (state : State w) (request : Request w) : Option (BitVec w) :=
  if request.sinkTick && request.pop && state.visible && state.pending then
    some state.payload
  else none

def step (state : State w) (request : Request w) : Chan.ConcreteResult (State w) w :=
  let take := accepted state request
  let give := delivered state request
  let didTake := take.isSome
  let didGive := give.isSome
  { state :=
      { payload := take.getD state.payload
        pending := if didGive then false else state.pending || didTake
        sourceBusy := if didTake then true
          else if request.sourceTick && request.acknowledge && !state.pending then false
          else state.sourceBusy
        visible := if didGive then false
          else state.visible ||
            (request.sinkTick && request.publish && state.pending)
        sourcePhase := if didTake then !state.sourcePhase else state.sourcePhase
        sinkPhase := if request.sinkTick && request.publish then
            state.sourcePhase else state.sinkPhase
        ackPhase := if didGive then !state.ackPhase else state.ackPhase
        sourceAckPhase := if request.sourceTick && request.acknowledge then
            state.ackPhase else state.sourceAckPhase }
    accepted := take
    delivered := give }

/-- The abstract queue is the one unconsumed latched payload.  `sourceBusy`
may remain set after consumption until the acknowledgement crosses back. -/
structure Rep (c : Chan w) (queue : Chan.State w) (state : State w) : Prop where
  depthOne : c.depth = 1
  queueEq : queue = if state.pending then [state.payload] else []
  pendingBusy : state.pending = true → state.sourceBusy = true
  visiblePending : state.visible = true → state.pending = true

theorem rep_reset (c : Chan w) (depthOne : c.depth = 1) :
    Rep c [] (reset w) := by
  constructor <;> simp [reset, depthOne]

/-- Every concrete mailbox event is one abstract FIFO event.  Synchronizer
delay appears only as a conservative event with no successful transfer. -/
theorem step_refines (c : Chan w) (queue : Chan.State w) (state : State w)
    (request : Request w) (rep : Rep c queue state) :
    let physical := step state request
    let abstract := c.step queue physical.event
    Rep c abstract.state physical.state ∧
      abstract.accepted = physical.accepted.isSome ∧
      abstract.delivered = physical.delivered := by
  rcases rep with ⟨depthOne, queueEq, pendingBusy, visiblePending⟩
  subst queue
  cases pendingEq : state.pending <;>
    cases busyEq : state.sourceBusy <;>
    cases visibleEq : state.visible <;>
    cases sourceTickEq : request.sourceTick <;>
    cases sinkTickEq : request.sinkTick <;>
    cases pushEq : request.push <;>
    cases popEq : request.pop <;>
    cases publishEq : request.publish <;>
    cases acknowledgeEq : request.acknowledge <;>
    cases c.policy <;>
    simp [step, accepted, delivered, Chan.ConcreteResult.event, Chan.step,
      depthOne, pendingEq, busyEq, visibleEq, sourceTickEq, sinkTickEq,
      pushEq, popEq, publishEq, acknowledgeEq] at pendingBusy visiblePending ⊢
  all_goals constructor <;> simp [depthOne]

def refinement (c : Chan w) (depthOne : c.depth = 1) : Chan.Refinement c where
  ConcreteState := State w
  Request := Request w
  reset := reset w
  step := step
  Rep := Rep c
  reset_refines := rep_reset c depthOne
  step_refines := by
    intro queue state request rep
    exact step_refines c queue state request rep

end Loom.Hw.Cdc.ToggleChan
