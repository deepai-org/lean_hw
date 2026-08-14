-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SoCFabricGauntlet.Execution

/-! Certified schedule replay campaigns for the SoC Fabric Gauntlet. -/

namespace Tools.SoCFabricGauntletCampaign

open Loom.Hw
open Machines.Multiclock.SoCFabricGauntlet
open Machines.Multiclock.SoCFabricGauntlet.Execution

def event (mask : Nat) : NamedClockEvent :=
  ⟨([("cpu_fabric_clk", 1), ("dma_clk", 2), ("mem_clk", 4),
      ("mon_clk", 8)].filterMap fun (name, bit) =>
      if mask &&& bit != 0 then some name else none)⟩

def repeatPattern : Nat → List Nat → List NamedClockEvent
  | 0, _ => []
  | count + 1, pattern => pattern.map event ++ repeatPattern count pattern

def balancedSchedule : List NamedClockEvent :=
  repeatPattern 1000 [1, 2, 4, 8, 3, 4, 9, 2, 5, 8, 6, 1]

def dmaFasterSchedule : List NamedClockEvent :=
  repeatPattern 1200 [2, 2, 2, 2, 1, 2, 4, 2, 8, 3, 2, 4, 6, 9]

def cpuResponseStallSchedule : List NamedClockEvent :=
  repeatPattern 1200 [1, 2, 4, 8, 3, 5, 6, 9, 10, 12]

def servicePauseSchedule : List NamedClockEvent :=
  repeatPattern 80 [1, 2, 4, 8, 3] ++
  repeatPattern 180 [1, 2, 8, 3, 9, 2] ++
  repeatPattern 1000 [1, 2, 4, 8, 3, 5, 6, 9]

def monitorPauseSchedule : List NamedClockEvent :=
  repeatPattern 80 [1, 2, 4, 8, 3] ++
  repeatPattern 180 [1, 2, 4, 3, 5, 6] ++
  repeatPattern 1000 [1, 2, 4, 8, 3, 5, 6, 9]

def coincidentSchedule : List NamedClockEvent :=
  repeatPattern 1000 [15, 1, 2, 4, 8, 3, 5, 9, 6, 10, 12, 7]

def cpuResponsePauseInputs : ExternalInputs :=
  fun time island name width =>
    if island = "cpu" && name = "hold_response" && time ≥ 200 && time < 1800 then
      BitVec.ofNat width 1
    else noInputs time island name width

structure CampaignResult where
  name : String
  passed : Bool
  observed : Metrics
  deriving Repr

structure ResetResult where
  stage : String
  reachedAt : Option Nat
  cleanRestart : Bool
  passed : Bool
  deriving Repr

structure Cut where
  state : FastState
  remaining : List NamedClockEvent

structure NegativeResult where
  corruption : String
  detected : Bool
  observed : Metrics
  deriving Repr

def campaign (name : String) (schedule : List NamedClockEvent)
    (inputs : ExternalInputs) (coverage : Metrics → Bool) : CampaignResult :=
  let observed := metrics (run inputs reset schedule)
  { name, observed, passed := complete observed && coverage observed }

def campaignWithMidpoint (name : String) (schedule : List NamedClockEvent)
    (midpoint : Nat) (inputs : ExternalInputs)
    (coverage : FastState → Metrics → Bool) : CampaignResult :=
  let middle := run inputs reset (schedule.take midpoint)
  let observed := metrics (run inputs reset schedule)
  { name, observed, passed := complete observed && coverage middle observed }

def tickCount (clock : String) (schedule : List NamedClockEvent) : Nat :=
  (schedule.filter (·.fires clock)).length

def findStage (predicate : StageFlags → Bool) (inputs : ExternalInputs) :
    Nat → FastState → List NamedClockEvent → Option (Nat × FastState)
  | _, _, [] => none
  | index, state, next :: rest =>
      if predicate (stageFlags state) then some (index, state)
      else findStage predicate inputs (index + 1) (advance inputs next state) rest

def cutAt (predicate : FastState → Bool) (inputs : ExternalInputs) :
    FastState → List NamedClockEvent → Option Cut
  | _, [] => none
  | state, events@(next :: rest) =>
      if predicate state then some ⟨state, events⟩
      else cutAt predicate inputs (advance inputs next state) rest

def corruptHead {width : Nat} (mask : BitVec width) :
    List (BitVec width) → List (BitVec width)
  | [] => []
  | value :: rest => (value ^^^ mask) :: rest

def negativeResult (name : String) (predicate : FastState → Bool)
    (corrupt : FastState → FastState) (oracle : Metrics → Bool) : NegativeResult :=
  match cutAt predicate noInputs reset balancedSchedule with
  | none => ⟨name, false, metrics reset⟩
  | some cut =>
      let observed := metrics (run noInputs (corrupt cut.state) cut.remaining)
      ⟨name, !complete observed && oracle observed, observed⟩

def negativeResults : List NegativeResult :=
  [ negativeResult "request-client-bit"
      (fun state => !state.cpuRequest.isEmpty)
      (fun state => { state with
        cpuRequest := corruptHead (BitVec.ofNat 50 (1 <<< 49)) state.cpuRequest })
      (fun m => m.cpuError != 0),
    negativeResult "request-tag-bit"
      (fun state => !state.cpuRequest.isEmpty)
      (fun state => { state with
        cpuRequest := corruptHead (BitVec.ofNat 50 (1 <<< 45)) state.cpuRequest })
      (fun m => m.cpuError != 0),
    negativeResult "request-mask-bit"
      (fun state => state.cpuRequest.head?.any (fun request =>
        request.toNat &&& (1 <<< 44) != 0))
      (fun state => { state with
        cpuRequest := corruptHead (BitVec.ofNat 50 1) state.cpuRequest })
      (fun m => m.cpuDigest != 0 || m.dmaDigest != 0 || m.auditDigest != 0),
    negativeResult "response-data-bit"
      (fun state => !state.cpuResponse.isEmpty)
      (fun state => { state with
        cpuResponse := corruptHead (BitVec.ofNat 38 2) state.cpuResponse })
      (fun m => m.cpuDigest != 0) ]

def resetResult (name : String) (predicate : StageFlags → Bool)
    (schedule : List NamedClockEvent := monitorPauseSchedule)
    (inputs : ExternalInputs := noInputs) : ResetResult :=
  let reached := findStage predicate inputs 0 reset schedule
  let restarted := match reached with
    | some (_, loaded) => metrics (run noInputs (coordinatedReset loaded) balancedSchedule)
    | none => metrics (run noInputs reset balancedSchedule)
  { stage := name
    reachedAt := reached.map (·.1)
    cleanRestart := complete restarted
    passed := reached.isSome && complete restarted }

def resetResults : List ResetResult :=
  [ resetResult "empty" (·.empty) balancedSchedule,
    resetResult "client-held" (·.clientHeld) balancedSchedule,
    resetResult "request-fifo" (·.requestFifo) balancedSchedule,
    resetResult "arbiter-selected" (·.arbiterSelected) balancedSchedule,
    resetResult "target-fifo" (·.targetFifo) balancedSchedule,
    resetResult "committed-response-pending" (·.committedResponsePending)
      balancedSchedule,
    resetResult "response-fifo" (·.responseFifo) cpuResponseStallSchedule
      cpuResponsePauseInputs,
    resetResult "full-backpressured-audit" (·.fullBackpressured)
      monitorPauseSchedule,
    resetResult "traffic-both-directions" (·.trafficBothDirections)
      cpuResponseStallSchedule cpuResponsePauseInputs ]

def results : List CampaignResult :=
  [ campaign "balanced" balancedSchedule noInputs
      (fun m => m.contentionTicks > 0 && m.cpuGrants == m.dmaGrants),
    campaign "dma-faster" dmaFasterSchedule noInputs
      (fun _ => tickCount "dma_clk" dmaFasterSchedule >
        tickCount "cpu_fabric_clk" dmaFasterSchedule),
    campaignWithMidpoint "cpu-response-stall" cpuResponseStallSchedule 1500
      cpuResponsePauseInputs (fun middle _ =>
        middle.cpuResponse.length > 0 && (metrics middle).dmaResponses > 0),
    campaignWithMidpoint "service-pause" servicePauseSchedule 1400 noInputs
      (fun middle _ => middle.targetRequest.length > 0),
    campaignWithMidpoint "monitor-pause" monitorPauseSchedule 1400 noInputs
      (fun middle m => middle.audit.length == audit.bits.depth && m.auditStalls > 0),
    campaign "coincident-edges" coincidentSchedule noInputs
      (fun m => m.contentionTicks > 0),
    campaign "arbitration-pressure" balancedSchedule noInputs
      (fun m => m.contentionTicks > 0 && m.cpuGrants == m.dmaGrants),
    campaign "masked-write-sweep" balancedSchedule noInputs
      (fun m => m.monitorError == 0 &&
        m.auditDigest == (m.cpuDigest ^^^ m.dmaDigest)) ]

def runMain : IO UInt32 := do
  let observed := results
  let resets := resetResults
  let negatives := negativeResults
  for result in observed do
    IO.println s!"campaign={result.name} passed={result.passed} metrics={repr result.observed}"
  for result in resets do
    IO.println s!"reset-stage={result.stage} reached_at={result.reachedAt} clean_restart={result.cleanRestart} passed={result.passed}"
  for result in negatives do
    IO.println s!"negative={result.corruption} detected={result.detected} metrics={repr result.observed}"
  if observed.all (·.passed) && resets.all (·.passed) &&
      negatives.all (·.detected) then
    IO.println "SOC_FABRIC_CERTIFIED_CAMPAIGNS_OK"
    pure 0
  else
    IO.eprintln "SOC_FABRIC_CERTIFIED_CAMPAIGNS_FAILED"
    pure 1

end Tools.SoCFabricGauntletCampaign
