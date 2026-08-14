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

/-- Exact device identity used by a qualification record. An empty `part`
means the evidence is deliberately family-wide; a concrete part number must
otherwise match literally. -/
structure TargetDevice where
  vendor : String
  family : String
  part : String
  deriving DecidableEq, Repr

/-- Exact tool identity. Version is never a comment: changing it changes the
qualification key and therefore invalidates selection. -/
structure TargetTool where
  name : String
  version : String
  deriving DecidableEq, Repr

inductive TargetClockRelationship where
  | sameClock
  | related
  | independent
  deriving DecidableEq, Repr

/-- How the implementation flow obtains the physical storage. -/
inductive TargetPrimitiveMode where
  | inferred (flow mode : String)
  | explicitPrimitive (name mode : String)
  | macro (name configuration : String)
  deriving DecidableEq, Repr

/-- Complete machine-comparable scope of one storage qualification claim.
`Configuration` contributes width, depth, read latency, write mode, and output
register count; presentation and clock relationship close the remaining
digital-contract dimensions. -/
structure StorageQualificationKey where
  device : TargetDevice
  tool : TargetTool
  primitiveMode : TargetPrimitiveMode
  configuration : Configuration
  presentation : ReadPresentation
  clockRelationship : TargetClockRelationship
  deriving DecidableEq, Repr

/-- One narrowly scoped external observation. The key is exact and
machine-readable; `detail` explains the observed result but never participates
in selection. -/
structure TargetStorageEvidence where
  key : StorageQualificationKey
  stage : TargetClaimStage
  outcome : TargetEvidenceOutcome
  artifactSha256 : String
  reference : String
  detail : String
  deriving DecidableEq, Repr

/-- Executable policy used by a target adapter before selecting an assumed
storage leaf. `accepts` is a conservative permission to attempt the target
flow, not a proof that the external storage assumption is true. -/
structure TargetStoragePolicy where
  name : String
  accepts : StorageQualificationKey → Bool
  rejection : StorageQualificationKey → String
  evidence : List TargetStorageEvidence

namespace TargetStoragePolicy

def Supports (policy : TargetStoragePolicy) (key : StorageQualificationKey) : Prop :=
  policy.accepts key = true

instance (policy : TargetStoragePolicy) (key : StorageQualificationKey) :
    Decidable (policy.Supports key) := by
  unfold Supports
  infer_instance

/-- Executable fail-closed boundary for scripts and artifact selectors. -/
def check (policy : TargetStoragePolicy) (key : StorageQualificationKey) :
    Except String Unit :=
  if policy.accepts key then .ok () else .error (policy.rejection key)

def evidenceFor (policy : TargetStoragePolicy) (key : StorageQualificationKey) :
    List TargetStorageEvidence :=
  policy.evidence.filter (·.key == key)

end TargetStoragePolicy

private def dualClockProbeReference :=
  "fpga/substrate0/evidence/dual-clock-bram-probe/RESULT.md"

def openXc7Zynq7000Device : TargetDevice :=
  { vendor := "AMD/Xilinx", family := "Zynq-7000", part := "xc7z020clg484-1" }

def openXc7Tool : TargetTool :=
  { name := "openXC7", version := "0.8.2" }

def openXc7InferredRamMode : TargetPrimitiveMode :=
  .inferred "yosys synth_xilinx" "RAMB18E1/RAMB36E1 automatic width mode"

def openXc7Zynq7000Key (p : Parameters) : StorageQualificationKey :=
  { device := openXc7Zynq7000Device
    tool := openXc7Tool
    primitiveMode := openXc7InferredRamMode
    configuration := p.configuration .readFirst 1
    presentation := .registered
    clockRelationship := .independent }

private def openXc7ProbeKey (width : Nat) : StorageQualificationKey :=
  { device := openXc7Zynq7000Device
    tool := openXc7Tool
    primitiveMode := openXc7InferredRamMode
    configuration :=
      { width, depth := 4, readLatency := 1
        writeMode := .readFirst, outputRegisters := 1 }
    presentation := .registered
    clockRelationship := .independent }

private def probeSourceSha256 :=
  "3195af3c6a4bbe78dd5e17fc2688f3b5a0b077394afdb0cb95aac343ffd7587e"

private def probeBitstreamSha256 :=
  "12d7cd75b7aa2060dc921af658ac2d8278f23de8a13f0c34d8267b5c9ba75afc"

/-- Conservative policy justified by the 2026-08-14 ZC702 probe. Widths above
36 are rejected because openXC7 0.8.2 lowers them through the observed-bad
72-bit RAMB36E1 mode. Acceptance at or below 36 only avoids that known-bad
mode; the selected leaf still carries its external storage-contract
assumption. -/
def openXc7Zynq7000IndependentClockPolicy : TargetStoragePolicy where
  name := "openxc7-zynq7000-independent-clock-storage"
  accepts := fun key =>
    key.device == openXc7Zynq7000Device &&
    key.tool == openXc7Tool &&
    key.primitiveMode == openXc7InferredRamMode &&
    key.presentation == .registered &&
    key.clockRelationship == .independent &&
    key.configuration.readLatency == 1 &&
    key.configuration.writeMode == .readFirst &&
    key.configuration.outputRegisters == 1 &&
    decide (key.configuration.width ≤ 36)
  rejection := fun key =>
    s!"target profile openXC7 0.8.2 / Zynq-7000 rejects independent-clock " ++
    s!"inferred storage width {key.configuration.width}: the exact device, tool version, " ++
    "primitive mode, configuration, registered presentation, and independent-clock " ++
    "relationship must match; widths above 36 select an unqualified 72-bit RAMB36E1 lowering"
  evidence := [
    ⟨openXc7ProbeKey 46, .rtlSimulation, .pass, probeSourceSha256,
      dualClockProbeReference, "4,096 transfers"⟩,
    ⟨openXc7ProbeKey 46, .primitiveInference, .pass, probeSourceSha256,
      dualClockProbeReference, "inferred as 72-bit-mode RAMB36E1"⟩,
    ⟨openXc7ProbeKey 46, .routedImplementation, .pass, probeBitstreamSha256,
      dualClockProbeReference, "routed on xc7z020clg484-1"⟩,
    ⟨openXc7ProbeKey 46, .siliconExecution, .fail, probeBitstreamSha256,
      dualClockProbeReference, "72-mode leaf inverted payload bit 44"⟩,
    ⟨openXc7ProbeKey 32, .siliconExecution, .pass, probeBitstreamSha256,
      dualClockProbeReference, "independently inferred lower RAM bank"⟩,
    ⟨openXc7ProbeKey 14, .siliconExecution, .pass, probeBitstreamSha256,
      dualClockProbeReference, "independently inferred upper RAM bank"⟩]

/-- Profile-gated binding constructor. The proof is a target-selection gate,
not a proof of the physical leaf contract; the latter remains the exact named
external assumption in `BindingBasis.assumed`. -/
def openXc7Zynq7000InferredBinding (p : Parameters)
    (_supported : openXc7Zynq7000IndependentClockPolicy.Supports
      (openXc7Zynq7000Key p)) : Binding p where
  name := "evidence.openxc7.zynq7000.inferred-independent-clock-ram"
  configuration := p.configuration .readFirst 1
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
