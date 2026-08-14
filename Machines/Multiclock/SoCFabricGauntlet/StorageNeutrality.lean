-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SoCFabricGauntlet.Artifact
import Evidence.Targets.AsyncQueueStorage
import Loom.Hw.Multiclock

/-!
# Storage-realization neutrality pressure test

This module instantiates the same canonical `System` through the registered
target-storage path using the synchronous read behavior of an inferred Xilinx
7-series block RAM.  The leaf presentation is explicit, so it cannot be wired
through the zero-stage first-word-fall-through wrapper.

The retained wide artifact reproduces inference and the silicon failure. It
is deliberately *not* accepted by the openXC7/Zynq-7000 target-selection
policy below and must not be presented as a qualified target implementation.
-/

namespace Machines.Multiclock.SoCFabricGauntlet.StorageNeutrality

open Loom.Hw
open Loom.Hw.Cdc.AsyncQueueStorage
open Machines.Multiclock.SoCFabricGauntlet

private def bramBinding (p : Parameters) (stem : String) : Binding p where
  name := "evidence.xilinx7.inferred-block-ram." ++ stem
  configuration := p.configuration .readFirst 1
  agreesWidth := rfl
  agreesDepth := rfl
  agreesReadLatency := rfl
  basis := .assumed
    "Xilinx 7-series inferred true dual-port block RAM satisfies the synchronous storage contract"

private def renderBramModule (name : String)
    (interface : PhysicalLeafInterface) (configuration : Configuration) : String :=
  String.intercalate "\n" [
    s!"module {name}(",
    "  input wire write_clk, input wire read_clk, input wire rst,",
    "  input wire write_enable, input wire read_enable,",
    s!"  input wire [{interface.addressWidth - 1}:0] write_address, read_address,",
    s!"  input wire [{interface.width - 1}:0] write_data,",
    s!"  output reg [{interface.width - 1}:0] read_sample",
    ");",
    s!"  // XILINX7_BLOCK_RAM width={interface.width} depth={interface.depth}",
    s!"  // contract_read_latency={configuration.readLatency}",
    s!"  (* ram_style = \"block\" *) reg [{interface.width - 1}:0] words [0:{interface.depth - 1}];",
    "  always @(posedge write_clk) begin",
    "    if (write_enable) words[write_address] <= write_data;",
    "  end",
    "  always @(posedge read_clk) begin",
    "    if (read_enable) read_sample <= words[read_address];",
    "  end",
    "endmodule"]

def bramLeaf (p : Parameters) (stem : String) : PhysicalLeaf p where
  binding := bramBinding p stem
  readPresentation := .registered
  moduleName := "loom_xilinx7_block_ram_" ++ stem
  renderModule := renderBramModule

private def leafFor (binding : System.CertifiedPortableBinding)
    (stem : String) :=
  bramLeaf
    (System.CertifiedPortable.storageShape binding.connection
      binding.depthAtLeastTwo).parameters stem

private def registeredBinding (binding : System.CertifiedPortableBinding)
    (stem : String) : System.CertifiedRegisteredStorageBinding where
  base := binding
  leaf := leafFor binding stem
  registered := rfl

def targetOverlay : System.CertifiedBindingOverlay certifiedArtifact.bindings where
  replacements := [
    .registeredStorage (registeredBinding dmaRequestBinding "dma_request"),
    .registeredStorage (registeredBinding dmaResponseBinding "dma_response"),
    .registeredStorage (registeredBinding targetRequestBinding "target_request"),
    .registeredStorage (registeredBinding targetResponseBinding "target_response"),
    .registeredStorage (registeredBinding auditBinding "audit")]
  distinct := by decide
  covered := by decide

/-- Sparse target overlay: the two same-clock bindings remain untouched and
ordered coverage is inherited from the canonical artifact. -/
def bramArtifact : System.CertifiedRealizedSystem system certified :=
  certifiedArtifact.withOverlay targetOverlay (by decide) (by decide)

/-- Registered-BRAM target realization of the exact canonical System. -/
def bramTarget : System.RealizedSystem :=
  bramArtifact.realized

private def profileErrorFor (binding : System.CertifiedPortableBinding) : Option String :=
  let parameters := (System.CertifiedPortable.storageShape binding.connection
    binding.depthAtLeastTwo).parameters
  match Loom.Evidence.Targets.AsyncQueueStorage.openXc7Zynq7000IndependentClockPolicy.check
      parameters with
  | .ok _ => none
  | .error message => some s!"channel {binding.connection.chan.name}: {message}"

/-- Every target-refined channel in this SoC is wider than the conservative
openXC7 limit. This list is consumed by the emission tool before it writes an
artifact unless the caller explicitly requests known-bad evidence
reproduction. -/
def openXc7TargetPolicyFailures : List String :=
  [dmaRequestBinding, dmaResponseBinding, targetRequestBinding,
    targetResponseBinding, auditBinding].filterMap profileErrorFor

example : bramTarget.system = certifiedArtifact.realized.system := rfl
example : bramTarget.bindings.map (·.key) =
    certifiedArtifact.realized.bindings.map (·.key) := by decide
example : bramTarget.artifacts.externalAssumptions.length = 5 := by decide
example : openXc7TargetPolicyFailures.length = 5 := by native_decide
example : openXc7TargetPolicyFailures.any (·.contains "width 46") = true := by
  native_decide
example : (System.renderExternalAssumptions
    bramTarget.artifacts.externalAssumptions).contains
      "not Loom theorems and are not discharged by successful RTL generation or target-cell inference" := by
  native_decide

/-! The selected artifact now reports and implements the registered stage. -/

example : System.registeredTargetStorageTiming.storageReadStages = 1 := rfl
example : (leafFor targetRequestBinding "target_request").binding.configuration.readLatency = 1 :=
  rfl

end Machines.Multiclock.SoCFabricGauntlet.StorageNeutrality
