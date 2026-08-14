-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ChanRefinement

/-!
# Certified synchronous channel realization

This packages the actual generated FIFO `Design` behind the implementation-
neutral `Chan.Refinement` interface.  The package is optional physical
evidence; it is not a field of the abstract `Chan` handle.
-/

namespace Loom.Hw
namespace Chan

variable {w : Nat}

def syncAccepted (c : Chan w) (state : St) (event : Event w) : Option (BitVec w) :=
  let next := c.adapter.cycleOpen (c.drive event.push event.pop) state
  if (Expr.reg 1 c.acceptedName).eval next = 1#1 then event.push else none

def syncDelivered (c : Chan w) (state : St) (event : Event w) : Option (BitVec w) :=
  let next := c.adapter.cycleOpen (c.drive event.push event.pop) state
  if (Expr.reg 1 c.deliveredName).eval next = 1#1 then
    some (c.adapterPayload.eval state)
  else none

def syncConcreteStep (c : Chan w) (state : St) (event : Event w) :
    ConcreteResult St w :=
  { state := c.adapter.cycleOpen (c.drive event.push event.pop) state
    accepted := c.syncAccepted state event
    delivered := c.syncDelivered state event }

theorem syncAccepted_eq (c : Chan w) (queue : State w) (state : St)
    (event : Event w) (rep : AdapterRep c queue state) :
    c.syncAccepted state event =
      if (c.step queue event).accepted then event.push else none := by
  unfold syncAccepted
  dsimp only
  have transfer := c.adapter_transfer_refines_of_rep queue event state rep
  rw [transfer.1]
  cases accepted : (c.step queue event).accepted <;> simp [boolBit]

theorem syncDelivered_eq (c : Chan w) (queue : State w) (state : St)
    (event : Event w) (rep : AdapterRep c queue state) :
    c.syncDelivered state event = (c.step queue event).delivered := by
  unfold syncDelivered
  dsimp only
  have transfer := c.adapter_transfer_refines_of_rep queue event state rep
  rw [transfer.2]
  cases delivered : (c.step queue event).delivered with
  | none => simp [boolBit]
  | some value =>
      have nonempty : !queue.isEmpty := by
        cases queue with
        | nil => simp [step] at delivered
        | cons head tail => simp
      have payload := rep.toView.payload nonempty
      have head := c.fifoOrder queue event value delivered
      simp [boolBit, payload, head]

theorem syncConcreteStep_event (c : Chan w) (queue : State w) (state : St)
    (event : Event w) (rep : AdapterRep c queue state) :
    (c.syncConcreteStep state event).event = c.successfulEvent queue event := by
  apply congrArg₂ EventData.mk
  · simp [syncConcreteStep, c.syncAccepted_eq queue state event rep]
  · simp [syncConcreteStep, c.syncDelivered_eq queue state event rep]

/-- The stock generated FIFO is a certified implementation of the abstract
channel for every positive depth and either explicit co-tick policy. -/
def syncRefinement (c : Chan w) (positiveDepth : 0 < c.depth) : Refinement c where
  ConcreteState := St
  Request := Event w
  reset := c.adapter.reset
  step := c.syncConcreteStep
  Rep := AdapterRep c
  reset_refines := c.adapterRep_reset positiveDepth
  step_refines := by
    intro queue state event rep
    let physical := c.syncConcreteStep state event
    have eventEq : physical.event = c.successfulEvent queue event :=
      c.syncConcreteStep_event queue state event rep
    have normalized : c.step queue physical.event = c.step queue event := by
      rw [eventEq, c.step_successfulEvent queue event]
    change AdapterRep c (c.step queue physical.event).state physical.state ∧
      (c.step queue physical.event).accepted = physical.accepted.isSome ∧
      (c.step queue physical.event).delivered = physical.delivered
    rw [normalized]
    constructor
    · simpa [physical, syncConcreteStep] using rep.step event
    constructor
    · change (c.step queue event).accepted = (c.syncAccepted state event).isSome
      rw [c.syncAccepted_eq queue state event rep]
      cases accepted : (c.step queue event).accepted
      · simp
      · cases pushed : event.push with
        | none => simp [step, pushed] at accepted
        | some value => simp
    · change (c.step queue event).delivered = c.syncDelivered state event
      exact (c.syncDelivered_eq queue state event rep).symm

end Chan
end Loom.Hw
