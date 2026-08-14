-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SoCFabricGauntlet.Recovery
import Machines.Multiclock.SoCFabricGauntlet.Execution

/-!
# Loss-explicit recovery campaign for the SoC Fabric Gauntlet

The executable campaign retains the canonical Gauntlet's exact pre-adapted
island trees and changes only the logical reset policy.  Its ordered connection
keys are checked against the pretty-authored recovery realization in
`Recovery.lean`.
-/

namespace Machines.Multiclock.SoCFabricGauntlet.RecoveryCampaign

open Loom.Hw
open Machines.Multiclock.SoCFabricGauntlet
open Machines.Multiclock.SoCFabricGauntlet.Recovery

def logicalSystem : System :=
  builder.withIndependentReset.certify (by decide)

example : logicalSystem.connections.map (·.key) =
    recoveryFabric.connections.map (·.key) := by decide
example : logicalSystem.resetPolicy = .independentFlush := by decide

def event (mask : Nat) : NamedClockEvent :=
  ⟨([("cpu_fabric_clk", 1), ("dma_clk", 2), ("mem_clk", 4),
      ("mon_clk", 8)].filterMap fun (name, bit) =>
      if mask &&& bit != 0 then some name else none)⟩

def repeatPattern : Nat → List Nat → List NamedClockEvent
  | 0, _ => []
  | count + 1, pattern => pattern.map event ++ repeatPattern count pattern

def trafficSchedule : List NamedClockEvent :=
  repeatPattern 1000 [1, 2, 4, 8, 3, 4, 9, 2, 5, 8, 6, 1]

def ordinaryEvent (tick : NamedClockEvent) : System.RecoveryEvent := { tick }

def ordinaryPrefix (count : Nat) : System.RecoverySchedulePrefix :=
  (trafficSchedule.take count |>.map ordinaryEvent).toArray

def stateAfter (count : Nat) : logicalSystem.State :=
  logicalSystem.runRecoveryPrefix (ordinaryPrefix count) Execution.noInputs

def occupancies (state : logicalSystem.State) : List Nat :=
  logicalSystem.connections.map fun connection =>
    (logicalSystem.channelState state connection).length

def regNat (state : logicalSystem.State) (island name : String)
    (width : Nat) : Nat :=
  (state.island island).regs name width |>.toNat

/-! ## Reachable under-load cut and loss ledger

Event 27 was found by executable schedule search, not by constructing an
arbitrary queue state.  At this cut one request, one response, and one audit
record occupy three distinct crossings.  `Execution.run_represents` ties the
compact state to the authoritative ordinary `System` execution.
-/

def recoveryCut : Nat := 27

def loadedFast : Execution.FastState :=
  Execution.run Execution.noInputs Execution.reset
    (trafficSchedule.take recoveryCut)

theorem loadedFast_reachable :
    Execution.Represents loadedFast
      (SoCFabricGauntlet.system.runEventsFrom Execution.noInputs
        SoCFabricGauntlet.system.reset (trafficSchedule.take recoveryCut)) :=
  Execution.reset_run_represents Execution.noInputs
    (trafficSchedule.take recoveryCut)

def loaded : logicalSystem.State :=
  let state := Execution.view loadedFast
  { island := state.island, channel := state.channel, time := state.time }

def fabricRecovery : System.RecoveryEvent where
  tick := ⟨[]⟩
  resetIslands := ["fabric"]

def lossLedger (event : System.RecoveryEvent) (state : logicalSystem.State) :
    List (String × Nat) :=
  logicalSystem.connections.map fun connection =>
    (connection.chan.name,
      if event.affects connection then
        (logicalSystem.channelState state connection).length
      else 0)

def recovered : logicalSystem.State :=
  logicalSystem.advanceRecovery fabricRecovery (Execution.noInputs loaded.time) loaded

set_option maxRecDepth 10000 in
example : (Execution.metrics loadedFast).channelOccupancy =
    [1, 0, 0, 0, 0, 1, 1] := by decide

set_option maxRecDepth 10000 in
example : lossLedger fabricRecovery loaded =
    [("cpu_request", 1), ("cpu_response", 0),
     ("dma_request", 0), ("dma_response", 0),
     ("target_request", 0), ("target_response", 1),
     ("audit", 0)] := by decide

set_option maxRecDepth 10000 in
example : occupancies recovered = [0, 0, 0, 0, 0, 0, 1] := by
  decide

example : logicalSystem.recoveryEventOk fabricRecovery = true := by
  decide

/-! The physical completion gate for `fabric` covers both endpoint halves of
all six incident routes.  Recovery is reported only when the request remains
asserted and every one of those twelve endpoint acknowledgements is present.
-/

def fabricIsland : SystemIsland :=
  ⟨"fabric", "cpu_fabric_clk", SoCFabricGauntlet.fabric⟩

def allEndpointDone : System.RecoveryEndpointKey → Bool := fun _ => true

def oneEndpointMissing : System.RecoveryEndpointKey → Bool := fun endpoint =>
  endpoint != ⟨cpuRequestConnection.key, .source⟩

example : (logicalSystem.recoveryEndpointsFor fabricIsland).length = 12 := by
  decide

example : logicalSystem.recoveryComplete fabricIsland true allEndpointDone = true := by
  decide

example : logicalSystem.recoveryComplete fabricIsland true oneEndpointMissing = false := by
  decide

/-! Independent recovery deliberately does not provide application replay.
The explicit restart below begins a fresh application epoch using the supported
common reset, after the single-island loss event has completed.  The standard
campaign then proves renewed forward progress and full transaction completion.
-/

def restartedFast : Execution.FastState :=
  Execution.run Execution.noInputs Execution.reset trafficSchedule

end Machines.Multiclock.SoCFabricGauntlet.RecoveryCampaign
