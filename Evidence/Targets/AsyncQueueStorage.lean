-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.AsyncQueueStorage

/-!
# Optional physical storage bindings for asynchronous queues

These are evidence-layer declarations, not Loom semantics and not defaults.
They demonstrate that the technology-neutral `AsyncQueueStorage` contract can
be bound to the repository's available Zynq-7000 evidence target or to an
arbitrary ASIC memory macro. A different FPGA family, foundry, compiler, or
custom memory supplies another value of the same generic binding type.

Each physical binding contains exactly one named external assumption. Width,
depth, and total synchronous-read latency are proof-equal to the contract
instance; write mode and output-register settings are serialized in the same
configuration named by that assumption.
-/

namespace Loom.Evidence.Targets.AsyncQueueStorage

open Loom.Hw.Cdc.AsyncQueueStorage

/-! ## Fail-closed target selection

The generic `PhysicalLeaf` boundary deliberately permits any target integration
that names its residual assumption. A concrete target flow needs a stricter,
executable selection policy: known-bad or unqualified configurations must be
rejected before they are presented as usable target implementations. These
records live in `Evidence`, not in channel semantics.
-/

/-- Claims that target evidence may establish. They are intentionally
distinct: success at an earlier stage never promotes a later stage. -/
inductive TargetClaimStage where
  | rtlSimulation
  | primitiveInference
  | routedImplementation
  | siliconExecution
  deriving DecidableEq, Repr

inductive TargetEvidenceOutcome where
  | pass
  | fail
  deriving DecidableEq, Repr

/-- One narrowly scoped external observation. `configuration` is prose on
purpose: target packages may need device-, tool-, primitive-, width-, depth-,
or clock-specific qualifiers that do not belong in Loom's semantic types. -/
structure TargetStorageEvidence where
  stage : TargetClaimStage
  outcome : TargetEvidenceOutcome
  configuration : String
  reference : String
  deriving DecidableEq, Repr

/-- Executable policy used by a target adapter before selecting an assumed
storage leaf. `accepts` is a conservative permission to attempt the target
flow, not a proof that the external storage assumption is true. -/
structure TargetStoragePolicy where
  name : String
  deviceFamily : String
  toolchain : String
  clockRelationship : String
  accepts : Parameters → Bool
  rejection : Parameters → String
  evidence : List TargetStorageEvidence

namespace TargetStoragePolicy

def Supports (policy : TargetStoragePolicy) (p : Parameters) : Prop :=
  policy.accepts p = true

instance (policy : TargetStoragePolicy) (p : Parameters) :
    Decidable (policy.Supports p) := by
  unfold Supports
  infer_instance

/-- Executable fail-closed boundary for scripts and artifact selectors. -/
def check (policy : TargetStoragePolicy) (p : Parameters) : Except String Unit :=
  if policy.accepts p then .ok () else .error (policy.rejection p)

end TargetStoragePolicy

private def dualClockProbeReference :=
  "fpga/substrate0/evidence/dual-clock-bram-probe/RESULT.md"

/-- Conservative policy justified by the 2026-08-14 ZC702 probe. Widths above
36 are rejected because openXC7 0.8.2 lowers them through the observed-bad
72-bit RAMB36E1 mode. Acceptance at or below 36 only avoids that known-bad
mode; the selected leaf still carries its external storage-contract
assumption. -/
def openXc7Zynq7000IndependentClockPolicy : TargetStoragePolicy where
  name := "openxc7-zynq7000-independent-clock-storage"
  deviceFamily := "AMD/Xilinx Zynq-7000"
  toolchain := "openXC7 0.8.2"
  clockRelationship := "independent write/read clocks"
  accepts := fun p => decide (p.width ≤ 36)
  rejection := fun p =>
    s!"target profile openXC7 0.8.2 / Zynq-7000 rejects independent-clock " ++
    s!"inferred storage width {p.width}: widths above 36 select an unqualified " ++
    "72-bit RAMB36E1 lowering; use portable register storage or separately qualified banking"
  evidence := [
    ⟨.rtlSimulation, .pass, "46-bit dual-clock probe, 4,096 transfers",
      dualClockProbeReference⟩,
    ⟨.primitiveInference, .pass, "46-bit probe inferred as 72-bit-mode RAMB36E1",
      dualClockProbeReference⟩,
    ⟨.routedImplementation, .pass, "46-bit probe routed on xc7z020clg484-1",
      dualClockProbeReference⟩,
    ⟨.siliconExecution, .fail, "46-bit 72-mode leaf; payload bit 44 inverted",
      dualClockProbeReference⟩,
    ⟨.siliconExecution, .pass, "32-bit independently inferred RAM bank",
      dualClockProbeReference⟩,
    ⟨.siliconExecution, .pass, "14-bit independently inferred RAM bank",
      dualClockProbeReference⟩]

/-- Profile-gated binding constructor. The proof is a target-selection gate,
not a proof of the physical leaf contract; the latter remains the exact named
external assumption in `BindingBasis.assumed`. -/
def openXc7Zynq7000InferredBinding (p : Parameters)
    (_supported : openXc7Zynq7000IndependentClockPolicy.Supports p)
    (writeMode : WriteMode := .readFirst) (outputRegisters : Nat := 1) : Binding p where
  name := "evidence.openxc7.zynq7000.inferred-independent-clock-ram"
  configuration := p.configuration writeMode outputRegisters
  agreesWidth := rfl
  agreesDepth := rfl
  agreesReadLatency := rfl
  basis := .assumed (
    s!"openXC7 0.8.2 Zynq-7000 inferred independent-clock RAM " ++
    s!"satisfies AsyncQueueStorage(width={p.width},depth={p.depth}," ++
    s!"readLatency={p.readLatency}); profile acceptance avoids known-bad modes " ++
    "but does not discharge this assumption")

inductive RambE1Kind where
  | ramb18e1
  | ramb36e1
  deriving DecidableEq, Repr

def RambE1Kind.name : RambE1Kind → String
  | .ramb18e1 => "RAMB18E1"
  | .ramb36e1 => "RAMB36E1"

/-- Optional Xilinx 7-series binding used only when a board/evidence flow
explicitly selects it. The named assumption is the complete residual digital
leaf contract, not a claim that Loom proves vendor primitive semantics. -/
def rambE1 (p : Parameters) (kind : RambE1Kind)
    (writeMode : WriteMode := .readFirst) (outputRegisters : Nat := 1) : Binding p where
  name := "evidence.xilinx7." ++ kind.name
  configuration := p.configuration writeMode outputRegisters
  agreesWidth := rfl
  agreesDepth := rfl
  agreesReadLatency := rfl
  basis := .assumed (
    s!"{kind.name} configured as one-write/one-read independent-clock RAM " ++
    s!"satisfies AsyncQueueStorage(width={p.width},depth={p.depth}," ++
    s!"readLatency={p.readLatency})")

/-- Technology-parameterized ASIC binding. `macroName` is data supplied by a
PDK/compiler integration; generic Loom has no preferred foundry or SRAM
generator. -/
def asicSram (p : Parameters) (macroName : String)
    (writeMode : WriteMode := .readFirst) (outputRegisters : Nat := 0) : Binding p where
  name := "evidence.asic." ++ macroName
  configuration := p.configuration writeMode outputRegisters
  agreesWidth := rfl
  agreesDepth := rfl
  agreesReadLatency := rfl
  basis := .assumed (
    s!"{macroName} configured as one-write/one-read independent-clock SRAM " ++
    s!"satisfies AsyncQueueStorage(width={p.width},depth={p.depth}," ++
    s!"readLatency={p.readLatency})")

/-! ## Reference extension-boundary leaf

This is intentionally a mock target rather than a vendor or foundry
integration. It demonstrates once that selecting a target-refined leaf changes
the rendered RTL and that the renderer receives the exact checked
width/depth/latency configuration. The named assumption is visible and is not
promoted into Loom's certified portable path. -/

def mockBinding (p : Parameters) : Binding p where
  name := "evidence.mock.dual-clock-memory"
  configuration := p.configuration .readFirst 0
  agreesWidth := rfl
  agreesDepth := rfl
  agreesReadLatency := rfl
  basis := .assumed
    "mock dual-clock memory satisfies the selected AsyncQueueStorage contract"

private def renderMockModule (name : String) (interface : PhysicalLeafInterface)
    (configuration : Configuration) : String :=
  String.intercalate "\n" [
    s!"module {name}(",
    "  input wire write_clk, input wire read_clk, input wire rst,",
    "  input wire write_enable, input wire read_enable,",
    s!"  input wire [{interface.addressWidth - 1}:0] write_address, read_address,",
    s!"  input wire [{interface.width - 1}:0] write_data,",
    s!"  output wire [{interface.width - 1}:0] read_sample",
    ");",
    s!"  // MOCK_TARGET_STORAGE width={interface.width} depth={interface.depth}",
    s!"  // address_width={interface.addressWidth} response_latency={interface.readLatency}",
    s!"  // read_latency={configuration.readLatency} write_mode={repr configuration.writeMode}",
    s!"  reg [{interface.width - 1}:0] words [0:{interface.depth - 1}];",
    "  always @(posedge write_clk) begin",
    "    if (write_enable) words[write_address] <= write_data;",
    "  end",
    "  assign read_sample = words[read_address];",
    "endmodule"]

def mockLeaf (p : Parameters) : PhysicalLeaf p where
  binding := mockBinding p
  readPresentation := .firstWordFallThrough
  moduleName := "loom_mock_target_async_storage"
  renderModule := renderMockModule

end Loom.Evidence.Targets.AsyncQueueStorage
