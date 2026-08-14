-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SoCFabricGauntlet.Proofs

/-!
# Conditional progress contracts for the SoC Fabric Gauntlet

Safety in `Proofs` has no fairness premise.  This module states liveness over
application-defined cumulative service indices.  A target instantiation must
separately justify that clocks keep ticking and that ready/consume service is
offered; no clock ratio is smuggled into the generic theorem.
-/

namespace Machines.Multiclock.SoCFabricGauntlet

open Loom.Hw

structure ProgressTraces where
  clientAccepted : TraceContract.CountTrace
  fabricVisible : TraceContract.CountTrace
  fabricGranted : TraceContract.CountTrace
  targetCommitted : TraceContract.CountTrace
  responseRouted : TraceContract.CountTrace
  clientDelivered : TraceContract.CountTrace
  auditDelivered : TraceContract.CountTrace

/-- Explicit adjacent-stage service assumptions.  On hardware, the index is a
campaign service round and these fields are discharged only when the required
domain clocks, target readiness, response acceptance, and audit consumption
continue. -/
structure ProgressPremises (trace : ProgressTraces) where
  requestClockAndSink : TraceContract.deliveredWithin 1
    trace.clientAccepted trace.fabricVisible
  arbitration : TraceContract.deliveredWithin 2
    trace.fabricVisible trace.fabricGranted
  targetClockAndCapacity : TraceContract.deliveredWithin 1
    trace.fabricGranted trace.targetCommitted
  responseClockAndRoute : TraceContract.deliveredWithin 1
    trace.targetCommitted trace.responseRouted
  clientClockAndAcceptance : TraceContract.deliveredWithin 1
    trace.responseRouted trace.clientDelivered
  auditClockAndConsumption : TraceContract.deliveredWithin 1
    trace.targetCommitted trace.auditDelivered

/-- Every accepted transaction is returned within the sum of the five named
service bounds.  This is conditional progress, not an unconditional clock
claim. -/
theorem accepted_eventually_delivered (trace : ProgressTraces)
    (premises : ProgressPremises trace) :
    TraceContract.deliveredWithin 6 trace.clientAccepted trace.clientDelivered := by
  have first := TraceContract.deliveredWithin_comp
    premises.requestClockAndSink premises.arbitration
  have second := TraceContract.deliveredWithin_comp first
    premises.targetClockAndCapacity
  have third := TraceContract.deliveredWithin_comp second
    premises.responseClockAndRoute
  exact TraceContract.deliveredWithin_comp third
    premises.clientClockAndAcceptance

theorem committed_eventually_audited (trace : ProgressTraces)
    (premises : ProgressPremises trace) :
    TraceContract.deliveredWithin 1 trace.targetCommitted trace.auditDelivered :=
  premises.auditClockAndConsumption

/-- If issuing has stopped at `stop`, the composed bound gives a concrete
service index by which the delivered count has caught up with every request
accepted at that cut. -/
theorem drains_after_stop (trace : ProgressTraces)
    (premises : ProgressPremises trace) (stop : Nat) :
    trace.clientAccepted stop ≤ trace.clientDelivered (stop + 6) :=
  accepted_eventually_delivered trace premises stop

inductive ClientId
  | cpu
  | dma
  deriving DecidableEq, Repr

/-- Pure policy used by the hardware arbiter when it is idle and the target
can accept.  `priorityCpu = true` means CPU wins a tie. -/
def chooseGrant (priorityCpu cpuValid dmaValid : Bool) : Option ClientId :=
  if cpuValid && dmaValid then
    if priorityCpu then some .cpu else some .dma
  else if cpuValid then some .cpu
  else if dmaValid then some .dma
  else none

def priorityAfter : Option ClientId → Bool → Bool
  | some .cpu, _ => false
  | some .dma, _ => true
  | none, prior => prior

theorem chooseGrant_at_most_one (priorityCpu cpuValid dmaValid : Bool) :
    (chooseGrant priorityCpu cpuValid dmaValid).isSome = true →
      chooseGrant priorityCpu cpuValid dmaValid = some .cpu ∨
      chooseGrant priorityCpu cpuValid dmaValid = some .dma := by
  cases priorityCpu <;> cases cpuValid <;> cases dmaValid <;>
    simp [chooseGrant]

theorem roundRobin_tie_alternates (priorityCpu : Bool) :
    let first := chooseGrant priorityCpu true true
    let next := priorityAfter first priorityCpu
    chooseGrant next true true ≠ first := by
  cases priorityCpu <;> decide

/-- Under continuous contention and two available grant opportunities, both
clients are served once.  Thus a requester waits through at most one competing
grant; clock and target availability remain explicit in `ProgressPremises`. -/
theorem roundRobin_two_grant_bound (priorityCpu : Bool) :
    let first := chooseGrant priorityCpu true true
    let second := chooseGrant (priorityAfter first priorityCpu) true true
    (first = some .cpu ∧ second = some .dma) ∨
      (first = some .dma ∧ second = some .cpu) := by
  cases priorityCpu <;> decide

def clientIdOfFabricClient : FabricClient → ClientId
  | .cpu => .cpu
  | .dma => .dma

def literalFabricChoice (state : St) : Option ClientId :=
  (fabricGrantChoice state).map clientIdOfFabricClient

private theorem bitvec1_and_eq_one_progress (left right : BitVec 1) :
    left &&& right = 1#1 ↔ left = 1#1 ∧ right = 1#1 := by
  have leftCases : left = 0#1 ∨ left = 1#1 := by bv_omega
  have rightCases : right = 0#1 ∨ right = 1#1 := by bv_omega
  rcases leftCases with rfl | rfl <;> rcases rightCases with rfl | rfl <;>
    decide

/-- The abstract two-client policy used by the progress proof is the literal
fabric arbiter whenever an arbitration opportunity exists.  Clock service and
target capacity remain explicit premises; this theorem discharges the policy
part rather than assuming a second, unrelated arbiter. -/
theorem literalFabricChoice_eq_chooseGrant (state : St)
    (notHeld : state.regs "hold_arbitration" 1 = 0#1)
    (idle : state.regs "outstanding" 1 = 0#1)
    (targetReady : targetRequest.bits.canEnq.eval state = 1#1) :
    literalFabricChoice state =
      chooseGrant (state.regs "round_robin" 1 == 0#1)
        (cpuRequest.bits.canDeq.eval state == 1#1)
        (dmaRequest.bits.canDeq.eval state == 1#1) := by
  unfold literalFabricChoice fabricGrantChoice chooseGrant
  have gate : (Expr.and (.not (.reg 1 "hold_arbitration"))
      (.not (.reg 1 "outstanding"))).eval state = 1#1 := by
    simp [Expr.eval, notHeld, idle]
  rw [if_pos gate, if_pos targetReady]
  by_cases cpuReady : cpuRequest.bits.canDeq.eval state = 1#1 <;>
  by_cases dmaReady : dmaRequest.bits.canDeq.eval state = 1#1 <;>
  by_cases priority : state.regs "round_robin" 1 = 0#1 <;>
    simp [cpuReady, dmaReady, priority, Expr.eval,
      bitvec1_and_eq_one_progress,
      clientIdOfFabricClient]

/-- Consequently the literal arbiter's choice under continuous contention is
the alternating policy whose two-opportunity bound is proved above. -/
theorem literal_roundRobin_two_opportunity_bound (state : St)
    (notHeld : state.regs "hold_arbitration" 1 = 0#1)
    (idle : state.regs "outstanding" 1 = 0#1)
    (targetReady : targetRequest.bits.canEnq.eval state = 1#1)
    (cpuReady : cpuRequest.bits.canDeq.eval state = 1#1)
    (dmaReady : dmaRequest.bits.canDeq.eval state = 1#1) :
    let priorityCpu := state.regs "round_robin" 1 == 0#1
    let first := literalFabricChoice state
    let second := chooseGrant (priorityAfter first priorityCpu) true true
    (first = some .cpu ∧ second = some .dma) ∨
      (first = some .dma ∧ second = some .cpu) := by
  rw [literalFabricChoice_eq_chooseGrant state notHeld idle targetReady]
  simpa [cpuReady, dmaReady] using
    roundRobin_two_grant_bound (state.regs "round_robin" 1 == 0#1)

end Machines.Multiclock.SoCFabricGauntlet
