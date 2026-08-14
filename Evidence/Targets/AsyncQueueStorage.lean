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
  moduleName := "loom_mock_target_async_storage"
  renderModule := renderMockModule

end Loom.Evidence.Targets.AsyncQueueStorage
