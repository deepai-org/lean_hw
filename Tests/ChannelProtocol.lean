-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Substrate.TwoClock

namespace Tests.ChannelProtocol

open Loom.Hw
open Machines.Substrate.TwoClock

/-! The generated proof handle closes lookup details once. -/

example : system.Invariant
    (System.atChannel connection fun values => values.length ≤ queue.depth) :=
  prettySystem.qConnection.capacity

example : system.Invariant (System.PresentationCoherent system connection) :=
  prettySystem.qConnection.safety

/-! A pending conservative pop reserves the physical queue head instead of
counting it a second time. -/

example : Chan.unreservedQueue [7#8, 9#8] true = [9#8] := by decide

example :
    (Chan.registeredOwnership [7#8, 9#8] false 0#8 true).inventory = [9#8] := by
  decide

/-- A source-only event may append behind a head already reserved by the
unticked destination; the reserved head is not reintroduced into inventory. -/
example :
    Chan.unreservedQueue [1#8] true ++
        queue.acceptedValues [1#8] { push := some 2#8, pop := false } =
      Chan.applicationConsumed [1#8] false ++
        Chan.unreservedQueue
          (queue.step [1#8] { push := some 2#8, pop := false }).state true :=
  queue.scheduledSink_conservation [1#8] (some 2#8) true false false
    (by decide) (by simp) (by simp)

/-- A destination consume and source append on one aligned event transfer the
old head out and leave the new tail owned exactly once. -/
example :
    Chan.unreservedQueue [1#8] false ++
        queue.acceptedValues [1#8] { push := some 2#8, pop := false } =
      Chan.applicationConsumed [1#8] true ++
        Chan.unreservedQueue
          (queue.step [1#8] { push := some 2#8, pop := false }).state true :=
  queue.scheduledSink_conservation [1#8] (some 2#8) false true true
    (by simp) (by simp) (by simp)

/-! The generic endpoint certificates are about the exact generated Designs,
not only their abstract helper functions.  The idle body is the smallest
closed witness and keeps the proof independent of application behavior. -/

private def idleBody : Design where
  name := "idle_endpoint_body"
  regs := []
  mems := []
  rules := []
  outputs := []

private def idleSourceCertificate :
    Chan.SourceEndpointCertificate queue idleBody where
  assume := fun state input =>
    Chan.bitAsserted (input queue.sourceAcceptedName 1) = true →
      (queue.sourceView state).valid = true
  replacement := fun _ _ => none
  refines := by
    intro input state assumption
    have ackCases : input queue.sourceAcceptedName 1 = 0#1 ∨
        input queue.sourceAcceptedName 1 = 1#1 := by bv_omega
    rcases ackCases with ack | ack
    · have ack' : input "__loom_chan_q_src_accepted" 1 = 0#1 := by
        simpa [queue, Chan.sourceAcceptedName, Chan.stem] using ack
      simp [Chan.sourceView, Chan.bitAsserted, Chan.withSource,
        Design.cycleOpen, Design.cycle, idleBody, Chan.sourceStep,
        St.setInputs, Act.run, Expr.eval, RegEnv.set, ack',
        Chan.sourceAccepted, Chan.sourceValidName, Chan.sourcePayloadName,
        Chan.sourceReadyName, Chan.sourceAcceptedName, Chan.stem, queue]
    · have valid := assumption (by simp [Chan.bitAsserted, ack])
      have ack' : input "__loom_chan_q_src_accepted" 1 = 1#1 := by
        simpa [queue, Chan.sourceAcceptedName, Chan.stem] using ack
      have valid' : state.regs "__loom_chan_q_src_valid" 1 = 1#1 := by
        simpa [Chan.sourceView, Chan.bitAsserted, queue,
          Chan.sourceValidName, Chan.stem] using valid
      simp [Chan.sourceView, Chan.bitAsserted, Chan.withSource,
        Design.cycleOpen, Design.cycle, idleBody, Chan.sourceStep,
        St.setInputs, Act.run, Expr.eval, RegEnv.set, ack', valid',
        Chan.sourceAccepted, Chan.sourceValidName, Chan.sourcePayloadName,
        Chan.sourceReadyName, Chan.sourceAcceptedName, Chan.stem, queue]
  acceptedLegal := by
    intro input state assumption accepted
    apply assumption
  replacementLegal := by simp

private def idleSinkCertificate :
    Chan.SinkEndpointCertificate queue idleBody where
  assume := fun _ _ => True
  «consume» := fun _ _ => false
  refines := by
    intro input state _
    unfold Chan.sinkPopPending Chan.bitAsserted Chan.withSink Design.cycleOpen
      Design.cycle idleBody
    simp [St.setInputs, Act.run, Expr.eval, RegEnv.set, queue]
  payloadPreserved := by
    intro input state _
    unfold Chan.withSink Design.cycleOpen Design.cycle idleBody
    simp [St.setInputs, Act.run, RegEnv.set, Chan.sinkPayloadName,
      Chan.sinkPopName, Chan.stem, queue]
  consumeLegal := by simp

example (input : InEnv) (state : St)
    (accepted : idleSourceCertificate.assume state input) :
    let driven := state.setInputs (queue.withSource idleBody).inputs input
    let ack := Chan.bitAsserted (driven.regs queue.sourceAcceptedName 1)
    queue.sourceView ((queue.withSource idleBody).cycleOpen input state) =
      Chan.sourceStep (queue.sourceView state).valid
        (queue.sourceView state).payload ack none :=
  queue.withSource_refines idleBody idleSourceCertificate input state accepted

example (input : InEnv) (state : St) :
    queue.sinkPopPending ((queue.withSink idleBody).cycleOpen input state) = false :=
  queue.withSink_refines idleBody idleSinkCertificate input state trivial

private def ledgerBefore : Chan.Ownership 8 where
  queued := [1#8]
  staged := [2#8]

private def ledgerMiddle : Chan.Ownership 8 where
  queued := [2#8]
  staged := [3#8]

private def ledgerAfter : Chan.Ownership 8 where
  queued := [3#8]

private theorem firstStep :
    Chan.OwnershipStep ledgerBefore [3#8] [1#8] ledgerMiddle := by
  unfold Chan.OwnershipStep Chan.Ownership.inventory ledgerBefore ledgerMiddle
  decide

private theorem secondStep :
    Chan.OwnershipStep ledgerMiddle [] [2#8] ledgerAfter := by
  unfold Chan.OwnershipStep Chan.Ownership.inventory ledgerMiddle ledgerAfter
  decide

example : Chan.OwnershipStep ledgerBefore [3#8] [1#8, 2#8] ledgerAfter :=
  firstStep.comp secondStep

/-! Bounded service composes in a named service unit. -/

private def countTrace : TraceContract.CountTrace := fun time => time

private def identityService : TraceContract.BoundedService where
  unit := "destination ticks"
  accepted := countTrace
  delivered := countTrace
  bound := 0
  deliveredMonotone := fun _ _ le => le
  guarantee := by intro time; simp [countTrace]

private def twiceService := identityService.comp identityService rfl rfl

example : twiceService.bound = 0 := rfl
example : twiceService.unit = "destination ticks" := rfl

private def emptyInterface : System.InterfaceProof system Nat Nat where
  safety := fun _ => True
  safetyInvariant := by
    unfold System.Invariant Loom.TSys.Invariant
    intros
    trivial
  contract := TraceContract.id
  observeInput := fun _ _ _ => []
  observeOutput := fun _ _ _ => []
  holds := by intros; rfl

private def composedInterface : System.InterfaceProof system Nat Nat :=
  emptyInterface.comp emptyInterface (by intros; rfl)

example : composedInterface.contract [] [] := ⟨[], rfl, rfl⟩

/-! The ordinary executor theorem is exposed at the Application boundary. -/

example (events : SchedulePrefix) :
    (application.run events).semantic = system.runPrefix events :=
  application.run_semantic_eq events

example (events : SchedulePrefix) :
    (application.runCompact events).Agrees (system.runPrefix events) :=
  application.runCompact_agrees events

end Tests.ChannelProtocol
