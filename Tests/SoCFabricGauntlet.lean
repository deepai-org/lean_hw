-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SoCFabricGauntlet
import Tools.SoCFabricGauntletCampaign

namespace Tests.SoCFabricGauntlet

open Loom.Hw
open Machines.Multiclock.SoCFabricGauntlet

def sampleRequest : Request :=
  ⟨1#1, 0xA#4, 1#1, 0x5C#8, 0x12345678#32, 0xD#4⟩
def sampleResponse : Response := ⟨0#1, 7#4, 0x89abcdef#32, 0#1⟩
def sampleCommit : CommitRecord := ⟨1#1, 3#4, 0x42#8, 1#1, 0xfeedface#32⟩

example : HwPacked.unpack (HwPacked.pack sampleRequest) = sampleRequest := by rfl
example : HwPacked.unpack (HwPacked.pack sampleResponse) = sampleResponse := by rfl
example : HwPacked.unpack (HwPacked.pack sampleCommit) = sampleCommit := by rfl

example : HwPacked.width Request = 50 := by decide
example : HwPacked.width Response = 38 := by decide
example : HwPacked.width CommitRecord = 46 := by decide
example : Request.clientField.lo = 49 := rfl
example : Request.maskField.lo = 0 := rfl
example : Response.dataField.lo = 1 := rfl
example : CommitRecord.resultField.lo = 0 := rfl

example : system.connections.length = 7 := by decide
example : system.islands.map (fun island => (island.name, island.clock)) =
    [("cpu", "cpu_fabric_clk"), ("dma", "dma_clk"),
      ("fabric", "cpu_fabric_clk"), ("service", "mem_clk"),
      ("monitor", "mon_clk")] := by decide
example : certifiedArtifact.emissionCheck.isOk := by native_decide
example : certifiedArtifact.renderedVerilog.contains "input wire [49:0] src_payload" := by
  native_decide
example : certifiedArtifact.renderedVerilog.contains "input wire [37:0] src_payload" := by
  native_decide
example : certifiedArtifact.renderedVerilog.contains "loom_compiled_sync_fifo_cpu_request" := by
  native_decide
example : certifiedArtifact.renderedVerilog.contains "loom_compiled_async_fifo_dma_request" := by
  native_decide

/-- All long campaigns use the compact runner related to the public System by
`Execution.reset_run_represents`; the computed campaign gates must all close. -/
example : Tools.SoCFabricGauntletCampaign.results.all (·.passed) := by
  native_decide
example : Tools.SoCFabricGauntletCampaign.resetResults.all (·.passed) := by
  native_decide
example : Tools.SoCFabricGauntletCampaign.negativeResults.all (·.detected) := by
  native_decide

private def physicalBindings : List System.BoundImplementation :=
  certifiedArtifact.bindings.map System.CertifiedChannelBinding.toPhysical

private def reorderedPhysicalBindings : List System.BoundImplementation :=
  match physicalBindings with
  | first :: second :: rest => second :: first :: rest
  | bindings => bindings

/-- Missing, duplicated, and reordered route inventories fail closed. -/
example : !(System.realize system []).isOk := by native_decide
example : !(System.realize system (physicalBindings.dropLast)).isOk := by native_decide
example : !(System.realize system
    (cpuRequestBinding.toPhysical :: physicalBindings)).isOk := by native_decide
example : !(System.realize system
    reorderedPhysicalBindings).isOk := by native_decide

/-- Omitting a response route specifically (rather than merely shortening the
inventory at its tail) is rejected by exact ordered realization coverage. -/
example : !(System.realize system
    [cpuRequestBinding.toPhysical, cpuResponseBinding.toPhysical,
      dmaRequestBinding.toPhysical,
      targetRequestBinding.toPhysical, targetResponseBinding.toPhysical,
      auditBinding.toPhysical]).isOk := by native_decide

private def duplicateCpuSend : Design :=
  { cpu with rules := cpu.rules ++
      [⟨"negative_second_send",
        cpuRequest.bits.enq (.lit (HwPacked.pack sampleRequest))⟩] }

private def duplicateCpuSendBuilder : SystemBuilder :=
  System.empty
    |>.island "cpu" duplicateCpuSend (clock := "cpu_fabric_clk")
    |>.island "dma" dma (clock := "dma_clk")
    |>.island "fabric" fabric (clock := "cpu_fabric_clk")
    |>.island "service" service (clock := "mem_clk")
    |>.island "monitor" monitor (clock := "mon_clk")
    |>.connect cpuRequest.bits (source := "cpu") (sink := "fabric")
    |>.connect cpuResponse.bits (source := "fabric") (sink := "cpu")
    |>.connect dmaRequest.bits (source := "dma") (sink := "fabric")
    |>.connect dmaResponse.bits (source := "fabric") (sink := "dma")
    |>.connect targetRequest.bits (source := "fabric") (sink := "service")
    |>.connect targetResponse.bits (source := "service") (sink := "fabric")
    |>.connect audit.bits (source := "service") (sink := "monitor")
    |>.withClockRel .asynchronous

/-- A second possible send to the same endpoint in one CPU tick fails the
System structural gate before realization or simulation. -/
example : !(duplicateCpuSendBuilder.assemble.isOk) := by native_decide

private def unconstrainedDmaRequest : System.BoundImplementation :=
  System.BoundImplementation.custom dmaRequestConnection
    "negative.unconstrained_dma_request" .any dmaRequestBinding.refinement
    (fun _ => "negative_unconstrained_dma_request")
    (fun _ => "module negative_unconstrained_dma_request; endmodule")
    (fun _ => [])

private def wrongClockDmaRequest : System.BoundImplementation :=
  System.BoundImplementation.custom dmaRequestConnection
    "negative.same_clock_dma_request" .same dmaRequestBinding.refinement
    (fun _ => "negative_same_clock_dma_request")
    (fun _ => "module negative_same_clock_dma_request; endmodule")
    (fun _ => [])

/-- A distinct-clock route cannot silently lose intent or claim aligned clocks. -/
example : !(System.realize system
    [cpuRequestBinding.toPhysical, cpuResponseBinding.toPhysical,
      unconstrainedDmaRequest, dmaResponseBinding.toPhysical,
      targetRequestBinding.toPhysical, targetResponseBinding.toPhysical,
      auditBinding.toPhysical]).isOk := by native_decide
example : !(System.realize system
    [cpuRequestBinding.toPhysical, cpuResponseBinding.toPhysical,
      wrongClockDmaRequest, dmaResponseBinding.toPhysical,
      targetRequestBinding.toPhysical, targetResponseBinding.toPhysical,
      auditBinding.toPhysical]).isOk := by native_decide

/-- Dynamic packed-field consumers fail on a width/offset overrun. -/
example : match PackedField.checked (α := Request) "wrong_width" 49 4 with
    | .error _ => true
    | .ok _ => false := by
  have overrun : ¬49 + 4 ≤ HwPacked.width Request := by decide
  simp [PackedField.checked, overrun]

/-- Swapping client and tag bits is observably different from the canonical
generated packer and is rejected by an exact-value comparison. -/
example : HwPacked.pack sampleRequest !=
    ((HwPacked.pack sampleRequest).setWidth 50 ^^^
      (BitVec.ofNat 50 ((1 <<< 49) ||| (1 <<< 45)))) := by
  native_decide

private def rogueTelemetry : Design :=
  { cpuBody with
    name := "rogue_telemetry_dependency"
    inputs := [⟨"__loom_chan_telemetry_dst_valid", 1⟩] }

private def rogueTelemetryBuilder : SystemBuilder :=
  System.empty.island "rogue" rogueTelemetry (clock := "rogue_clk")

/-- Generated-looking telemetry dependencies outside a declared channel are
rejected during checked System assembly. -/
example : !(rogueTelemetryBuilder.assemble.isOk) := by native_decide

end Tests.SoCFabricGauntlet
