-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.SystemRealize
import Loom.Hw.CertifiedSystem
import Loom.Hw.AsyncFifoDesign
import Loom.Hw.PortableAsyncQueueStorage
import Loom.Hw.ChanSync
import Loom.Hw.RecoveryProtocolDesign
import Loom.Hw.RecoveryDatapathDesign
import Loom.Hw.SystemRecovery

/-!
# Certified structural artifacts for multi-clock Systems

This is the closed, technology-neutral release path. A depth-two channel is
made from four ordinary certified Designs: its write/read controllers and the
write/read halves of the portable register-bank storage witness. The only RTL
written here is generated structural instantiation and wiring; every stateful
or combinational behavioral expression comes from `Compile.compile`.

Physical RAM bindings remain a separate extension point behind
`AsyncQueueStorage`. This file selects the unconditional compiled register
bank, so it introduces no physical storage assumption.
-/

namespace Loom.Hw.System

open Loom.Hw

/-- Structural/service timing reported for the compiled same-clock FIFO. The
queue commits on a clock edge, but delivery remains elastic because the sink
may decline to consume. -/
def compiledSyncTiming : ChannelTiming where
  sourceOfferStages := 1
  sinkConsumeStages := 1
  forwardSynchronizerStages := 0
  reverseSynchronizerStages := 0
  storageReadStages := 0
  sourceIssueInterval := .conditional 1 .sourceTicks [.sourceReadyEveryTick]
  sinkIssueInterval := .conditional 2 .sinkTicks
    [.sinkPayloadAvailableEveryTick, .sinkConsumesWhenAvailable]
  delivery := .scheduleDependent [.sinkConsumesWhenAvailable]

/-- Timing reported for the portable Gray FIFO. Two synchronizer stages are
real structural facts; the proved adversarial sampler has no bounded-staleness
premise, so the service field intentionally contains no finite number. -/
def compiledPortableTiming : ChannelTiming where
  sourceOfferStages := 1
  sinkConsumeStages := 1
  forwardSynchronizerStages := 2
  reverseSynchronizerStages := 2
  storageReadStages := 0
  sourceIssueInterval := .conditional 1 .sourceTicks
    [.sourceReadyEveryTick]
  sinkIssueInterval := .conditional 2 .sinkTicks
    [.sinkPayloadAvailableEveryTick, .sinkConsumesWhenAvailable]
  delivery := .scheduleDependent
    [.sinkContinuesTicking, .sinkConsumesWhenAvailable,
      .sinkEventuallyObservesSource]

/-- Independent recovery adds no hidden optimistic deadline. Its four-phase
protocol completes only while both domains make progress, remote levels are
eventually observed, and the level request is held to acknowledgement. -/
def compiledRecoveryPortableTiming : ChannelTiming where
  sourceOfferStages := 1
  sinkConsumeStages := 1
  forwardSynchronizerStages := 2
  reverseSynchronizerStages := 2
  storageReadStages := 0
  sourceIssueInterval := .conditional 1 .sourceTicks
    [.sourceReadyEveryTick]
  sinkIssueInterval := .conditional 2 .sinkTicks
    [.sinkPayloadAvailableEveryTick, .sinkConsumesWhenAvailable]
  delivery := .scheduleDependent
    [.sinkContinuesTicking, .sinkConsumesWhenAvailable,
      .sinkEventuallyObservesSource]
  recovery := .scheduleDependent
    [.sourceContinuesTicking, .sinkContinuesTicking,
      .sourceEventuallyObservesSink, .sinkEventuallyObservesSource,
      .recoveryRequestHeld]

namespace CertifiedDepthTwo

def fifoParameters (width : Nat) : Cdc.AsyncFifoDesign.Parameters where
  width := width
  depth := 2
  depthAtLeastTwo := by decide
  powerOfTwo := by decide

def storageParameters (width : Nat) : Cdc.AsyncQueueStorage.Parameters :=
  Cdc.AsyncQueueStorage.DepthTwo.parameters width

end CertifiedDepthTwo

/-- One abstract connection together with certificates for every behavioral
module in Loom's portable depth-two realization. `depthEq` is explicit: this
constructor cannot silently truncate or reinterpret another channel shape. -/
structure CertifiedDepthTwoBinding where
  connection : SystemConnection
  depthEq : connection.chan.depth = 2
  controls : Cdc.AsyncFifoDesign.Controls
    (CertifiedDepthTwo.fifoParameters connection.width)
  storage : Cdc.AsyncQueueStorage.CertifiedRegisterBankDesigns
    (CertifiedDepthTwo.storageParameters connection.width)

def CertifiedDepthTwoBinding.key (binding : CertifiedDepthTwoBinding) :
    ConnectionKey := binding.connection.key

private def depthTwoStorage {width : Nat} (channel : Chan width)
    (depthEq : channel.depth = 2) (positive : 0 < channel.depth) :
    Cdc.AsyncQueueStorage.Implementation
      (Cdc.AsyncFifo.storageParameters channel positive) := by
  rcases channel with ⟨name, depth, policy⟩
  simp only at depthEq
  subst depth
  exact Cdc.AsyncQueueStorage.DepthTwo.implementation width

/-- The exact technology-neutral refinement proved for the same control
Designs and compiled storage implementation carried by the binding. -/
def CertifiedDepthTwoBinding.refinement (binding : CertifiedDepthTwoBinding) :
    Chan.Refinement binding.connection.chan := by
  let p := CertifiedDepthTwo.fifoParameters binding.connection.width
  have depth : binding.connection.chan.depth = p.depth := by
    simpa [p, CertifiedDepthTwo.fifoParameters] using binding.depthEq
  have positive : 0 < binding.connection.chan.depth := by
    rw [binding.depthEq]
    decide
  exact Cdc.AsyncFifoDesign.Compiled.refinement p binding.connection.chan
    depth positive
    (depthTwoStorage binding.connection.chan binding.depthEq positive)

private def widthDecl (width : Nat) : String :=
  if width = 1 then "" else s!"[{width - 1}:0] "

private def fifoObject (info : CrossingInfo) (instanceName signal : String) :
    PhysicalObject :=
  { path := ["u_" ++ info.channel, instanceName, signal] }

/-- Complete technology-neutral implementation intent for the stock Gray
FIFO controller. It names exact generated objects; a backend may lower these
requirements to XDC, SDC, Quartus assignments, ASIC synchronizer-cell mapping,
or an explicit unsupported result without changing the System or channel. -/
def portablePhysicalIntent (info : CrossingInfo)
    (pointerWidth : Nat) : List TimingConstraint :=
  match info.sourceClock, info.sinkClock with
  | some source, some sink =>
      if source = sink then [] else
        let writeGray := fifoObject info "u_source_control" "write_gray"
        let writeSync0 := fifoObject info "u_sink_control" "write_gray_sync0"
        let writeSync1 := fifoObject info "u_sink_control" "write_gray_sync1"
        let readGray := fifoObject info "u_sink_control" "read_gray"
        let readSync0 := fifoObject info "u_source_control" "read_gray_sync0"
        let readSync1 := fifoObject info "u_source_control" "read_gray_sync1"
        [ .asynchronousClocks source sink,
          .synchronizerChain sink [writeSync0, writeSync1],
          .coherentBus source sink writeGray writeSync0 pointerWidth
            { reference := .fasterOf source sink }
            { reference := .fasterOf source sink },
          .synchronizerChain source [readSync0, readSync1],
          .coherentBus sink source readGray readSync0 pointerWidth
            { reference := .fasterOf source sink }
            { reference := .fasterOf source sink } ]
  | _, _ => []

private def wrapperName (binding : CertifiedDepthTwoBinding) : String :=
  "loom_compiled_async_fifo_" ++ binding.connection.chan.name

/-- All behavioral modules in the channel artifact. Their text is projected
from `CertifiedDesign`; none is supplied as an independent string. -/
def CertifiedDepthTwoBinding.componentModules
    (binding : CertifiedDepthTwoBinding) : List (String × String) :=
  [ (binding.controls.source.compiled.name,
      binding.controls.source.renderedVerilog),
    (binding.controls.sink.compiled.name,
      binding.controls.sink.renderedVerilog),
    (binding.storage.writer.compiled.name,
      binding.storage.writer.renderedVerilog),
    (binding.storage.reader.compiled.name,
      binding.storage.reader.renderedVerilog) ]

/-- Generated structural wrapper for the four proved modules. The signal
names are the typed declarations in `AsyncFifoDesign` and
`AsyncQueueStorageDesign`; the wrapper contains no `always`, state, Gray
logic, flag comparison, or storage behavior. -/
def CertifiedDepthTwoBinding.wrapperText
    (binding : CertifiedDepthTwoBinding) : String :=
  let width := binding.connection.width
  let pointerWidth := Cdc.AsyncFifoDesign.pointerWidth
    (CertifiedDepthTwo.fifoParameters width)
  let addressWidth := Cdc.AsyncFifoDesign.addressWidth
    (CertifiedDepthTwo.fifoParameters width)
  let sourceModule := binding.controls.source.compiled.name
  let sinkModule := binding.controls.sink.compiled.name
  let writerModule := binding.storage.writer.compiled.name
  let readerModule := binding.storage.reader.compiled.name
  String.intercalate "\n" [
    s!"module {wrapperName binding}(",
    "  input wire src_clk, input wire dst_clk, input wire rst,",
    s!"  input wire src_valid, input wire {widthDecl width}src_payload,",
    "  output wire src_ready,",
    "  output wire dst_valid,",
    s!"  output wire {widthDecl width}dst_payload, input wire dst_pop",
    ");",
    s!"wire {widthDecl pointerWidth}write_binary, write_gray, read_gray_sync0, read_gray_sync1;",
    s!"wire {widthDecl pointerWidth}read_binary, read_gray, write_gray_sync0, write_gray_sync1;",
    "wire write_take, read_take, sink_valid;",
    s!"wire {widthDecl addressWidth}write_address, read_address;",
    s!"wire {widthDecl width}write_data, slot_0, slot_1, read_data_0, read_sample;",
    "wire read_valid_0;",
    s!"{sourceModule} u_source_control (",
    "  .clk(src_clk), .rst(rst), .source_valid(src_valid), .source_payload(src_payload),",
    "  .raw_read_gray(read_gray), .o_write_binary(write_binary), .o_write_gray(write_gray),",
    "  .o_read_gray_sync0(read_gray_sync0), .o_read_gray_sync1(read_gray_sync1),",
    "  .source_ready(src_ready), .write_take(write_take),",
    "  .write_address(write_address), .write_data(write_data));",
    s!"{sinkModule} u_sink_control (",
    "  .clk(dst_clk), .rst(rst), .sink_pop(dst_pop), .raw_write_gray(write_gray),",
    "  .o_read_binary(read_binary), .o_read_gray(read_gray),",
    "  .o_write_gray_sync0(write_gray_sync0), .o_write_gray_sync1(write_gray_sync1),",
    "  .sink_valid(sink_valid), .read_take(read_take), .read_address(read_address));",
    s!"{writerModule} u_storage_writer (",
    "  .clk(src_clk), .rst(rst), .write_enable(write_take),",
    "  .write_address(write_address), .write_data(write_data),",
    "  .o_slot_0(slot_0), .o_slot_1(slot_1));",
    s!"{readerModule} u_storage_reader (",
    "  .clk(dst_clk), .rst(rst), .slot_0(slot_0), .slot_1(slot_1),",
    "  .read_enable(read_take), .read_address(read_address),",
    "  .o_read_data_0(read_data_0), .o_read_valid_0(read_valid_0),",
    "  .read_sample(read_sample));",
    "assign dst_valid = sink_valid;",
    "assign dst_payload = read_sample;",
    "endmodule" ]

private def CertifiedDepthTwoBinding.crossingInfo
    (binding : CertifiedDepthTwoBinding) (sys : System) : CrossingInfo :=
  { channel := binding.connection.chan.name
    width := binding.connection.width
    depth := binding.connection.chan.depth
    policy := binding.connection.chan.policy
    source := binding.connection.source
    sourceClock := (sys.findIsland? binding.connection.source).map (·.clock)
    sink := binding.connection.sink
    sinkClock := (sys.findIsland? binding.connection.sink).map (·.clock) }

def CertifiedDepthTwoBinding.toPhysical
    (binding : CertifiedDepthTwoBinding) : BoundImplementation :=
  BoundImplementation.custom binding.connection "loom.compiled.depth_two"
    .any binding.refinement
    (fun _ => wrapperName binding)
    (fun _ => binding.wrapperText)
    (fun info => portablePhysicalIntent info
      (Cdc.AsyncFifoDesign.pointerWidth
        (CertifiedDepthTwo.fifoParameters binding.connection.width)))
    compiledPortableTiming

/-! ## General portable power-of-two binding -/

namespace CertifiedPortable

def positiveDepth (connection : SystemConnection)
    (depthAtLeastTwo : 2 ≤ connection.chan.depth) : 0 < connection.chan.depth :=
  lt_of_lt_of_le (by decide) depthAtLeastTwo

def fifoParameters (connection : SystemConnection)
    (depthAtLeastTwo : 2 ≤ connection.chan.depth)
    (powerOfTwo : 2 ^ Nat.log2 connection.chan.depth = connection.chan.depth) :
    Cdc.AsyncFifoDesign.Parameters where
  width := connection.width
  depth := connection.chan.depth
  depthAtLeastTwo := depthAtLeastTwo
  powerOfTwo := powerOfTwo

def storageShape (connection : SystemConnection)
    (depthAtLeastTwo : 2 ≤ connection.chan.depth) :
    Cdc.AsyncQueueStorage.Portable.Shape where
  width := connection.width
  depth := connection.chan.depth
  positive := positiveDepth connection depthAtLeastTwo

end CertifiedPortable

/-- One certified, technology-neutral register-bank FIFO of arbitrary
power-of-two depth. The depth and payload width are the abstract channel's
values, not separate renderer configuration. -/
structure CertifiedPortableBinding where
  connection : SystemConnection
  depthAtLeastTwo : 2 ≤ connection.chan.depth
  powerOfTwo : 2 ^ Nat.log2 connection.chan.depth = connection.chan.depth
  controls : Cdc.AsyncFifoDesign.Controls
    (CertifiedPortable.fifoParameters connection depthAtLeastTwo powerOfTwo)
  storage : Cdc.AsyncQueueStorage.Portable.CertifiedDesigns
    (CertifiedPortable.storageShape connection depthAtLeastTwo)

def CertifiedPortableBinding.key (binding : CertifiedPortableBinding) :
    ConnectionKey := binding.connection.key

def CertifiedPortableBinding.refinement (binding : CertifiedPortableBinding) :
    Chan.Refinement binding.connection.chan := by
  let fifo := CertifiedPortable.fifoParameters binding.connection
    binding.depthAtLeastTwo binding.powerOfTwo
  have positive := CertifiedPortable.positiveDepth binding.connection
    binding.depthAtLeastTwo
  let shape := CertifiedPortable.storageShape binding.connection
    binding.depthAtLeastTwo
  exact Cdc.AsyncFifoDesign.Compiled.refinement fifo binding.connection.chan
    rfl positive (Cdc.AsyncQueueStorage.Portable.implementation shape)

private def portableWrapperName (binding : CertifiedPortableBinding) : String :=
  "loom_compiled_async_fifo_" ++ binding.connection.chan.name

def CertifiedPortableBinding.componentModules
    (binding : CertifiedPortableBinding) : List (String × String) :=
  [ (binding.controls.source.compiled.name,
      binding.controls.source.renderedVerilog),
    (binding.controls.sink.compiled.name,
      binding.controls.sink.renderedVerilog),
    (binding.storage.writer.compiled.name,
      binding.storage.writer.renderedVerilog),
    (binding.storage.reader.compiled.name,
      binding.storage.reader.renderedVerilog) ]

def CertifiedPortableBinding.wrapperText
    (binding : CertifiedPortableBinding) : String :=
  let connection := binding.connection
  let shape := CertifiedPortable.storageShape connection binding.depthAtLeastTwo
  let fifo := CertifiedPortable.fifoParameters connection binding.depthAtLeastTwo binding.powerOfTwo
  let width := connection.width
  let pointerWidth := Cdc.AsyncFifoDesign.pointerWidth fifo
  let addressWidth := Cdc.AsyncFifoDesign.addressWidth fifo
  let slots := List.range connection.chan.depth
  let slotWires := slots.map fun index => s!"slot_{index}"
  let writerSlots := slots.map fun index =>
    s!"  .o_{Cdc.AsyncQueueStorage.Portable.slotName index}(slot_{index}),"
  let readerSlots := slots.map fun index =>
    s!"  .{Cdc.AsyncQueueStorage.Portable.slotName index}(slot_{index}),"
  let sourceModule := binding.controls.source.compiled.name
  let sinkModule := binding.controls.sink.compiled.name
  let writerModule := binding.storage.writer.compiled.name
  let readerModule := binding.storage.reader.compiled.name
  String.intercalate "\n" <|
    [ s!"module {portableWrapperName binding}(",
      "  input wire src_clk, input wire dst_clk, input wire rst,",
      s!"  input wire src_valid, input wire {widthDecl width}src_payload,",
      "  output wire src_ready,",
      "  output wire dst_valid,",
      s!"  output wire {widthDecl width}dst_payload, input wire dst_pop",
      ");",
      s!"wire {widthDecl pointerWidth}write_binary, write_gray, read_gray_sync0, read_gray_sync1;",
      s!"wire {widthDecl pointerWidth}read_binary, read_gray, write_gray_sync0, write_gray_sync1;",
      "wire write_take, read_take, sink_valid;",
      s!"wire {widthDecl addressWidth}write_address, read_address;",
      s!"wire {widthDecl width}write_data, read_sample;" ] ++
    (if slotWires.isEmpty then [] else
      [s!"wire {widthDecl width}{String.intercalate ", " slotWires};"]) ++
    [ s!"{sourceModule} u_source_control (",
      "  .clk(src_clk), .rst(rst), .source_valid(src_valid), .source_payload(src_payload),",
      "  .raw_read_gray(read_gray), .o_write_binary(write_binary), .o_write_gray(write_gray),",
      "  .o_read_gray_sync0(read_gray_sync0), .o_read_gray_sync1(read_gray_sync1),",
      "  .source_ready(src_ready), .write_take(write_take),",
      "  .write_address(write_address), .write_data(write_data));",
      s!"{sinkModule} u_sink_control (",
      "  .clk(dst_clk), .rst(rst), .sink_pop(dst_pop), .raw_write_gray(write_gray),",
      "  .o_read_binary(read_binary), .o_read_gray(read_gray),",
      "  .o_write_gray_sync0(write_gray_sync0), .o_write_gray_sync1(write_gray_sync1),",
      "  .sink_valid(sink_valid), .read_take(read_take), .read_address(read_address));",
      s!"{writerModule} u_storage_writer (",
      "  .clk(src_clk), .rst(rst)," ] ++ writerSlots ++
    [ "  ." ++ (Cdc.AsyncQueueStorage.Portable.writeEnable shape).name ++ "(write_take),",
      "  ." ++ (Cdc.AsyncQueueStorage.Portable.writeAddress shape).name ++ "(write_address),",
      "  ." ++ (Cdc.AsyncQueueStorage.Portable.writeData shape).name ++ "(write_data));",
      s!"{readerModule} u_storage_reader (",
      "  .clk(dst_clk), .rst(rst)," ] ++ readerSlots ++
    [ "  ." ++ (Cdc.AsyncQueueStorage.Portable.readEnable shape).name ++ "(read_take),",
      "  ." ++ (Cdc.AsyncQueueStorage.Portable.readAddress shape).name ++ "(read_address),",
      "  .read_sample(read_sample));",
      "assign dst_valid = sink_valid;",
      "assign dst_payload = read_sample;",
      "endmodule" ]

/-! ### Expert target-storage substitution seam

The ordinary certified route above remains fully portable. A target evidence
profile may replace only its storage leaf while retaining the same compiled
FIFO controls and abstract refinement. The replacement renderer receives the
exact storage interface/configuration contract; its named assumption remains
outside Loom's theorem boundary. -/

private def targetStorageWrapperName (binding : CertifiedPortableBinding) : String :=
  portableWrapperName binding ++ "_target_storage"

private def registeredTargetStorageWrapperName
    (binding : CertifiedPortableBinding) : String :=
  portableWrapperName binding ++ "_registered_target_storage"

/-- Target wrappers are opaque per-binding artifact units.  Scope shared
shape-derived control module names by channel so two equal-width/depth leaves
cannot emit duplicate Verilog declarations when assembled in one System. -/
private def targetControlModuleName (base : String)
    (binding : CertifiedPortableBinding) : String :=
  base ++ "_" ++ binding.connection.chan.name

private def renameRenderedModule (text oldName newName : String) : String :=
  text.replace ("module " ++ oldName ++ "(") ("module " ++ newName ++ "(")

def CertifiedPortableBinding.wrapperTextWithStorageLeaf
    (binding : CertifiedPortableBinding)
    (leaf : Cdc.AsyncQueueStorage.PhysicalLeaf
      (CertifiedPortable.storageShape binding.connection
        binding.depthAtLeastTwo).parameters) : String :=
  let connection := binding.connection
  let fifo := CertifiedPortable.fifoParameters connection binding.depthAtLeastTwo binding.powerOfTwo
  let width := connection.width
  let pointerWidth := Cdc.AsyncFifoDesign.pointerWidth fifo
  let addressWidth := Cdc.AsyncFifoDesign.addressWidth fifo
  let sourceModule := targetControlModuleName binding.controls.source.compiled.name binding
  let sinkModule := targetControlModuleName binding.controls.sink.compiled.name binding
  String.intercalate "\n" [
    s!"module {targetStorageWrapperName binding}(",
    "  input wire src_clk, input wire dst_clk, input wire rst,",
    s!"  input wire src_valid, input wire {widthDecl width}src_payload,",
    "  output wire src_ready,",
    "  output wire dst_valid,",
    s!"  output wire {widthDecl width}dst_payload, input wire dst_pop",
    ");",
    s!"wire {widthDecl pointerWidth}write_binary, write_gray, read_gray_sync0, read_gray_sync1;",
    s!"wire {widthDecl pointerWidth}read_binary, read_gray, write_gray_sync0, write_gray_sync1;",
    "wire write_take, read_take, sink_valid;",
    s!"wire {widthDecl addressWidth}write_address, read_address;",
    s!"wire {widthDecl width}write_data, read_sample;",
    s!"{sourceModule} u_source_control (",
    "  .clk(src_clk), .rst(rst), .source_valid(src_valid), .source_payload(src_payload),",
    "  .raw_read_gray(read_gray), .o_write_binary(write_binary), .o_write_gray(write_gray),",
    "  .o_read_gray_sync0(read_gray_sync0), .o_read_gray_sync1(read_gray_sync1),",
    "  .source_ready(src_ready), .write_take(write_take),",
    "  .write_address(write_address), .write_data(write_data));",
    s!"{sinkModule} u_sink_control (",
    "  .clk(dst_clk), .rst(rst), .sink_pop(dst_pop), .raw_write_gray(write_gray),",
    "  .o_read_binary(read_binary), .o_read_gray(read_gray),",
    "  .o_write_gray_sync0(write_gray_sync0), .o_write_gray_sync1(write_gray_sync1),",
    "  .sink_valid(sink_valid), .read_take(read_take), .read_address(read_address));",
    s!"{leaf.moduleName} u_target_storage (",
    "  .write_clk(src_clk), .read_clk(dst_clk), .rst(rst),",
    "  .write_enable(write_take), .read_enable(read_take),",
    "  .write_address(write_address), .read_address(read_address),",
    "  .write_data(write_data), .read_sample(read_sample));",
    "assign dst_valid = sink_valid;",
    "assign dst_payload = read_sample;",
    "endmodule" ]

/-- Latency-aware wrapper for a registered synchronous-read leaf.  A one-word
presentation buffer launches a read only after the synchronized FIFO reports a
head word, exposes the returned sample on the following cycle, and advances the
FIFO pointer only when that buffered word is consumed.  Clearing the buffer on
every pop intentionally permits a bubble; it avoids speculative reads across
an empty transition and keeps the wrapper correct for arbitrary clock ratios. -/
def CertifiedPortableBinding.wrapperTextWithRegisteredStorageLeaf
    (binding : CertifiedPortableBinding)
    (leaf : Cdc.AsyncQueueStorage.PhysicalLeaf
      (CertifiedPortable.storageShape binding.connection
        binding.depthAtLeastTwo).parameters) : String :=
  let connection := binding.connection
  let fifo := CertifiedPortable.fifoParameters connection binding.depthAtLeastTwo binding.powerOfTwo
  let width := connection.width
  let pointerWidth := Cdc.AsyncFifoDesign.pointerWidth fifo
  let addressWidth := Cdc.AsyncFifoDesign.addressWidth fifo
  let sourceModule := targetControlModuleName binding.controls.source.compiled.name binding
  let sinkModule := targetControlModuleName binding.controls.sink.compiled.name binding
  String.intercalate "\n" [
    s!"module {registeredTargetStorageWrapperName binding}(",
    "  input wire src_clk, input wire dst_clk, input wire rst,",
    s!"  input wire src_valid, input wire {widthDecl width}src_payload,",
    "  output wire src_ready,",
    "  output wire dst_valid,",
    s!"  output wire {widthDecl width}dst_payload, input wire dst_pop",
    ");",
    s!"wire {widthDecl pointerWidth}write_binary, write_gray, read_gray_sync0, read_gray_sync1;",
    s!"wire {widthDecl pointerWidth}read_binary, read_gray, write_gray_sync0, write_gray_sync1;",
    "wire write_take, fifo_read_take, fifo_sink_valid, fifo_pop, read_launch;",
    s!"wire {widthDecl addressWidth}write_address, read_address;",
    s!"wire {widthDecl width}write_data, read_sample;",
    "reg payload_ready;",
    s!"{sourceModule} u_source_control (",
    "  .clk(src_clk), .rst(rst), .source_valid(src_valid), .source_payload(src_payload),",
    "  .raw_read_gray(read_gray), .o_write_binary(write_binary), .o_write_gray(write_gray),",
    "  .o_read_gray_sync0(read_gray_sync0), .o_read_gray_sync1(read_gray_sync1),",
    "  .source_ready(src_ready), .write_take(write_take),",
    "  .write_address(write_address), .write_data(write_data));",
    s!"{sinkModule} u_sink_control (",
    "  .clk(dst_clk), .rst(rst), .sink_pop(fifo_pop), .raw_write_gray(write_gray),",
    "  .o_read_binary(read_binary), .o_read_gray(read_gray),",
    "  .o_write_gray_sync0(write_gray_sync0), .o_write_gray_sync1(write_gray_sync1),",
    "  .sink_valid(fifo_sink_valid), .read_take(fifo_read_take), .read_address(read_address));",
    "assign read_launch = fifo_sink_valid && !payload_ready;",
    "assign fifo_pop = payload_ready && dst_pop;",
    "always @(posedge dst_clk) begin",
    "  if (rst) payload_ready <= 1'b0;",
    "  else if (fifo_pop) payload_ready <= 1'b0;",
    "  else if (read_launch) payload_ready <= 1'b1;",
    "end",
    s!"{leaf.moduleName} u_target_storage (",
    "  .write_clk(src_clk), .read_clk(dst_clk), .rst(rst),",
    "  .write_enable(write_take), .read_enable(read_launch),",
    "  .write_address(write_address), .read_address(read_address),",
    "  .write_data(write_data), .read_sample(read_sample));",
    "assign dst_valid = fifo_sink_valid && payload_ready;",
    "assign dst_payload = read_sample;",
    "endmodule" ]

/-- Evidence-layer physical binding whose exact RTL replaces the portable
storage modules with `leaf`. The semantic refinement remains the same
technology-neutral channel theorem; correspondence of the external leaf text
is precisely its visible `BindingBasis.assumed` obligation. -/
def CertifiedPortableBinding.toPhysicalWithStorageLeaf
    (binding : CertifiedPortableBinding)
    (leaf : Cdc.AsyncQueueStorage.PhysicalLeaf
      (CertifiedPortable.storageShape binding.connection
        binding.depthAtLeastTwo).parameters)
    (_fwft : leaf.readPresentation = .firstWordFallThrough) : BoundImplementation :=
  BoundImplementation.custom binding.connection
    ("target-storage:" ++ leaf.binding.name) .any binding.refinement
    (fun _ => targetStorageWrapperName binding)
    (fun _ => String.intercalate "\n\n" [
      renameRenderedModule binding.controls.source.renderedVerilog
        binding.controls.source.compiled.name
        (targetControlModuleName binding.controls.source.compiled.name binding),
      renameRenderedModule binding.controls.sink.renderedVerilog
        binding.controls.sink.compiled.name
        (targetControlModuleName binding.controls.sink.compiled.name binding),
      leaf.moduleText,
      binding.wrapperTextWithStorageLeaf leaf])
    (fun info => portablePhysicalIntent info
      (Cdc.AsyncFifoDesign.pointerWidth
        (CertifiedPortable.fifoParameters binding.connection
          binding.depthAtLeastTwo binding.powerOfTwo)))
    compiledPortableTiming
    (externalAssumptions := leaf.binding.externalAssumption.toList)

/-- Timing for the conservative registered-leaf presentation wrapper.  The
leaf contributes one real storage stage; clearing the presentation buffer on
each pop limits sustained consumption to one word per three sink ticks through
the ordinary registered endpoint. -/
def registeredTargetStorageTiming : ChannelTiming where
  sourceOfferStages := 1
  sinkConsumeStages := 1
  forwardSynchronizerStages := 2
  reverseSynchronizerStages := 2
  storageReadStages := 1
  sourceIssueInterval := .conditional 1 .sourceTicks
    [.sourceReadyEveryTick]
  sinkIssueInterval := .conditional 3 .sinkTicks
    [.sinkPayloadAvailableEveryTick, .sinkConsumesWhenAvailable]
  delivery := .scheduleDependent
    [.sinkContinuesTicking, .sinkConsumesWhenAvailable,
      .sinkEventuallyObservesSource]

/-- Evidence-layer substitution for a registered synchronous-read leaf.  The
presentation proof keeps this path disjoint from the FWFT wrapper. -/
def CertifiedPortableBinding.toPhysicalWithRegisteredStorageLeaf
    (binding : CertifiedPortableBinding)
    (leaf : Cdc.AsyncQueueStorage.PhysicalLeaf
      (CertifiedPortable.storageShape binding.connection
        binding.depthAtLeastTwo).parameters)
    (_registered : leaf.readPresentation = .registered) : BoundImplementation :=
  BoundImplementation.custom binding.connection
    ("target-storage-registered:" ++ leaf.binding.name) .any binding.refinement
    (fun _ => registeredTargetStorageWrapperName binding)
    (fun _ => String.intercalate "\n\n" [
      renameRenderedModule binding.controls.source.renderedVerilog
        binding.controls.source.compiled.name
        (targetControlModuleName binding.controls.source.compiled.name binding),
      renameRenderedModule binding.controls.sink.renderedVerilog
        binding.controls.sink.compiled.name
        (targetControlModuleName binding.controls.sink.compiled.name binding),
      leaf.moduleText,
      binding.wrapperTextWithRegisteredStorageLeaf leaf])
    (fun info => portablePhysicalIntent info
      (Cdc.AsyncFifoDesign.pointerWidth
        (CertifiedPortable.fifoParameters binding.connection
          binding.depthAtLeastTwo binding.powerOfTwo)))
    registeredTargetStorageTiming
    (externalAssumptions := leaf.binding.externalAssumption.toList)

/-- Closed certified-artifact package for a registered target leaf.  The
semantic refinement remains the proved portable FIFO; the exact target RTL and
its one named external storage assumption are retained in `leaf`. -/
structure CertifiedRegisteredStorageBinding where
  base : CertifiedPortableBinding
  leaf : Cdc.AsyncQueueStorage.PhysicalLeaf
    (CertifiedPortable.storageShape base.connection
      base.depthAtLeastTwo).parameters
  registered : leaf.readPresentation = .registered

namespace CertifiedRegisteredStorageBinding

def connection (binding : CertifiedRegisteredStorageBinding) : SystemConnection :=
  binding.base.connection

def refinement (binding : CertifiedRegisteredStorageBinding) :
    Chan.Refinement binding.connection.chan :=
  binding.base.refinement

def toPhysical (binding : CertifiedRegisteredStorageBinding) : BoundImplementation :=
  binding.base.toPhysicalWithRegisteredStorageLeaf binding.leaf binding.registered

/-- Target module text already contains channel-scoped compiled controls, the
exact leaf, and its wrapper, so the certified renderer must not append a second
copy through the shared component list. -/
def componentModules (_binding : CertifiedRegisteredStorageBinding) :
    List (String × String) := []

def emissionCheck (binding : CertifiedRegisteredStorageBinding) : Except String Unit := do
  (Cdc.AsyncFifoDesign.sourceControl
    (CertifiedPortable.fifoParameters binding.connection
      binding.base.depthAtLeastTwo binding.base.powerOfTwo)).emitCheck
  (Cdc.AsyncFifoDesign.sinkControl
    (CertifiedPortable.fifoParameters binding.connection
      binding.base.depthAtLeastTwo binding.base.powerOfTwo)).emitCheck

end CertifiedRegisteredStorageBinding

def CertifiedPortableBinding.toPhysical
    (binding : CertifiedPortableBinding) : BoundImplementation :=
  BoundImplementation.custom binding.connection "loom.compiled.portable_fifo"
    .any binding.refinement
    (fun _ => portableWrapperName binding)
    (fun _ => binding.wrapperText)
    (fun info => portablePhysicalIntent info
      (Cdc.AsyncFifoDesign.pointerWidth
        (CertifiedPortable.fifoParameters binding.connection
          binding.depthAtLeastTwo binding.powerOfTwo)))
    compiledPortableTiming

/-! ## Compiler-produced graceful-recovery wrapper -/

/-- The closed portable FIFO plus two instances of the proved recovery
endpoint and width-specific compiler-produced datapath guards.  The recovery
refinement is additional to the ordinary FIFO refinement: transfer-only
clients retain the latter, while reset-aware composition consumes the former. -/
structure CertifiedRecoveryPortableBinding where
  base : CertifiedPortableBinding
  endpoint : CertifiedDesign Chan.RecoveryProtocol.Design.endpoint
  datapath : Chan.RecoveryDatapath.Certified
    { width := base.connection.width }

def CertifiedRecoveryPortableBinding.connection
    (binding : CertifiedRecoveryPortableBinding) : SystemConnection :=
  binding.base.connection

def CertifiedRecoveryPortableBinding.key
    (binding : CertifiedRecoveryPortableBinding) : ConnectionKey :=
  binding.connection.key

def CertifiedRecoveryPortableBinding.refinement
    (binding : CertifiedRecoveryPortableBinding) :
    Chan.Refinement binding.connection.chan :=
  binding.base.refinement

def CertifiedRecoveryPortableBinding.recoveryRefinement
    (binding : CertifiedRecoveryPortableBinding) :
    Chan.RecoveryRefinement binding.connection.chan :=
  Chan.RecoveryProtocol.Coordinated.observedRefinement binding.connection.chan

/-- Recovery-phase relation between the retained logical epoch and the
ordinary compiled FIFO/storage implementation. Outside recovery it requires
the existing full FIFO refinement. During recovery the physical FIFO may have
reset earlier than the island-global logical commit, so its old contents are
deliberately hidden behind the protocol ghost rather than falsely related to
the retained queue. -/
structure CertifiedRecoveryPortableBinding.EpochRep
    (binding : CertifiedRecoveryPortableBinding)
    (logical : Chan.RecoveryProtocol.State binding.connection.width)
    (physical : binding.refinement.ConcreteState) : Prop where
  stable : logical.recovering = false →
    binding.refinement.Rep logical.queue physical

/-- The ordinary compiled FIFO reset is the non-vacuous empty witness for the
recovery relation. -/
theorem CertifiedRecoveryPortableBinding.epochRep_reset
    (binding : CertifiedRecoveryPortableBinding) :
    binding.EpochRep (Chan.RecoveryProtocol.reset binding.connection.width)
      binding.refinement.reset := by
  constructor
  intro _
  exact binding.refinement.reset_refines

/-- Once the global coordinator commits and both physical halves take their
asserted reset edges, the canonical compiled FIFO reset state re-establishes
the strong empty-queue relation. The separate compiled-pair theorem proves
that a commit drives both reset inputs; the remaining aggregate wrapper proof
must show its structural component state is this reset state. -/
theorem CertifiedRecoveryPortableBinding.epochRep_of_globalCommit_reset
    (binding : CertifiedRecoveryPortableBinding)
    (logical : Chan.RecoveryProtocol.State binding.connection.width)
    (request : Chan.RecoveryProtocol.Coordinated.Request
      binding.connection.width)
    (complete : Chan.RecoveryProtocol.Coordinated.commits logical request = true) :
    binding.EpochRep
      (Chan.RecoveryProtocol.Coordinated.step
        binding.connection.chan logical request).state
      binding.refinement.reset := by
  constructor
  intro _
  have queueEmpty :
      (Chan.RecoveryProtocol.Coordinated.step
        binding.connection.chan logical request).state.queue = [] := by
    simp [Chan.RecoveryProtocol.Coordinated.step, complete]
  rw [queueEmpty]
  exact binding.refinement.reset_refines

theorem CertifiedRecoveryPortableBinding.epochRep_of_globalCommit_resetObserved
    (binding : CertifiedRecoveryPortableBinding)
    (logical : Chan.RecoveryProtocol.State binding.connection.width)
    (request : Chan.RecoveryProtocol.Coordinated.Request
      binding.connection.width)
    (observed : Chan.Event binding.connection.width)
    (complete : Chan.RecoveryProtocol.Coordinated.commits logical request = true) :
    binding.EpochRep
      (Chan.RecoveryProtocol.Coordinated.stepObserved
        binding.connection.chan logical request observed).state
      binding.refinement.reset := by
  constructor
  intro _
  have queueEmpty :
      (Chan.RecoveryProtocol.Coordinated.stepObserved
        binding.connection.chan logical request observed).state.queue = [] := by
    simp [Chan.RecoveryProtocol.Coordinated.stepObserved, complete]
  rw [queueEmpty]
  exact binding.refinement.reset_refines

/-- Proof-level base-FIFO transition used by the recovery wrapper relation.
The global commit resets the whole base state; otherwise the existing ordinary
refinement takes one request. -/
def CertifiedRecoveryPortableBinding.advanceBase
    (binding : CertifiedRecoveryPortableBinding)
    (logical : Chan.RecoveryProtocol.State binding.connection.width)
    (request : Chan.RecoveryProtocol.Coordinated.Request
      binding.connection.width)
    (physical : binding.refinement.ConcreteState)
    (baseRequest : binding.refinement.Request) :
    binding.refinement.ConcreteState :=
  if Chan.RecoveryProtocol.Coordinated.commits logical request then
    binding.refinement.reset
  else
    (binding.refinement.step physical baseRequest).state

/-- Inductive recovery-epoch step. While an epoch is pending the physical
FIFO is intentionally abstracted away. A global commit re-establishes reset;
an ordinary non-recovery step reuses the existing FIFO refinement, requiring
only the event equality supplied by the compiled guard/control wiring. -/
theorem CertifiedRecoveryPortableBinding.epochRep_advance
    (binding : CertifiedRecoveryPortableBinding)
    (logical : Chan.RecoveryProtocol.State binding.connection.width)
    (request : Chan.RecoveryProtocol.Coordinated.Request
      binding.connection.width)
    (physical : binding.refinement.ConcreteState)
    (baseRequest : binding.refinement.Request)
    (represented : binding.EpochRep logical physical) :
    binding.EpochRep
      (Chan.RecoveryProtocol.Coordinated.stepObserved
        binding.connection.chan logical request
        (binding.refinement.step physical baseRequest).event).state
      (binding.advanceBase logical request physical baseRequest) := by
  cases completeEq : Chan.RecoveryProtocol.Coordinated.commits logical request with
  | true =>
      simpa [CertifiedRecoveryPortableBinding.advanceBase, completeEq] using
        binding.epochRep_of_globalCommit_resetObserved logical request
          (binding.refinement.step physical baseRequest).event completeEq
  | false =>
      constructor
      intro nextStable
      have currentStable : logical.recovering = false := by
        simp [Chan.RecoveryProtocol.Coordinated.stepObserved, completeEq] at nextStable
        exact nextStable.1
      have oldRep := represented.stable currentStable
      have refined := binding.refinement.step_refines baseRequest oldRep
      dsimp only at refined
      have queueEq :
          (Chan.RecoveryProtocol.Coordinated.stepObserved
            binding.connection.chan logical request
            (binding.refinement.step physical baseRequest).event).state.queue =
            (binding.connection.chan.step logical.queue
              (binding.refinement.step physical baseRequest).event).state := by
        simp only [Chan.RecoveryProtocol.Coordinated.stepObserved, completeEq,
          Bool.false_eq_true, if_false]
      simp only [CertifiedRecoveryPortableBinding.advanceBase, completeEq,
        Bool.false_eq_true, if_false]
      rw [queueEq]
      exact refined.1

/-! ## Aggregate recovery-wrapper semantics

This is the state carried by one stock recovery channel after structural
wiring has selected its compiled endpoint pair and ordinary portable FIFO.
The endpoint-pair queue is a specification ghost; `base` is the actual
compiled FIFO/storage refinement state. -/

structure CertifiedRecoveryPortableBinding.WrapperState
    (binding : CertifiedRecoveryPortableBinding) where
  endpoints : Chan.RecoveryProtocol.Design.CompiledPair.State
    binding.connection.width :=
      Chan.RecoveryProtocol.Design.CompiledPair.reset binding.connection.width
  base : binding.refinement.ConcreteState := binding.refinement.reset

structure CertifiedRecoveryPortableBinding.WrapperRep
    (binding : CertifiedRecoveryPortableBinding)
    (queue : Chan.State binding.connection.width)
    (state : binding.WrapperState) : Prop where
  protocol : Chan.RecoveryProtocol.Rep queue
    (Chan.RecoveryProtocol.Design.CompiledPair.abstract state.endpoints)
  epoch : binding.EpochRep
    (Chan.RecoveryProtocol.Design.CompiledPair.abstract state.endpoints)
    state.base

def CertifiedRecoveryPortableBinding.wrapperReset
    (binding : CertifiedRecoveryPortableBinding) : binding.WrapperState := {}

structure CertifiedRecoveryPortableBinding.WrapperRequest
    (binding : CertifiedRecoveryPortableBinding) where
  control : Chan.RecoveryProtocol.Coordinated.Request
    binding.connection.width := {}
  fifo : binding.refinement.Request

/-- One behavioral wrapper transition. The FIFO's certified refinement
reports the successful physical transfer; that observation drives the
retained logical epoch and the two compiled endpoint-controller states. -/
def CertifiedRecoveryPortableBinding.wrapperStep
    (binding : CertifiedRecoveryPortableBinding)
    (state : binding.WrapperState) (request : binding.WrapperRequest) :
    Chan.ConcreteRecoveryResult binding.WrapperState binding.connection.width :=
  let physical := binding.refinement.step state.base request.fifo
  let logical := Chan.RecoveryProtocol.Design.CompiledPair.stepObserved
    binding.connection.chan state.endpoints request.control physical.event
  { state :=
      { endpoints := logical.state
        base := binding.advanceBase
          (Chan.RecoveryProtocol.Design.CompiledPair.abstract state.endpoints)
          request.control state.base request.fifo }
    accepted := logical.accepted
    delivered := logical.delivered
    recovered := logical.recovered }

theorem CertifiedRecoveryPortableBinding.wrapperReset_refines
    (binding : CertifiedRecoveryPortableBinding) :
    binding.WrapperRep [] binding.wrapperReset := by
  constructor
  · exact Chan.RecoveryProtocol.rep_reset
  · simpa [CertifiedRecoveryPortableBinding.wrapperReset] using
      binding.epochRep_reset

/-- The compiled endpoints, conservative FIFO observation, and retained epoch
form one inductive loss-explicit channel refinement for every stock portable
binding. This is the behavioral whole-wrapper relation; structural emission
facts connect its reset edge to the exact generated components below. -/
theorem CertifiedRecoveryPortableBinding.wrapperStep_refines
    (binding : CertifiedRecoveryPortableBinding)
    (queue : Chan.State binding.connection.width)
    (state : binding.WrapperState) (request : binding.WrapperRequest)
    (represented : binding.WrapperRep queue state) :
    let physical := binding.wrapperStep state request
    let abstract := binding.connection.chan.recoveryStep queue physical.event
    binding.WrapperRep abstract.state physical.state ∧
      abstract.accepted = physical.accepted ∧
      abstract.delivered = physical.delivered := by
  dsimp only
  let observed := (binding.refinement.step state.base request.fifo).event
  let coordinated := Chan.RecoveryProtocol.Coordinated.stepObserved
    binding.connection.chan
    (Chan.RecoveryProtocol.Design.CompiledPair.abstract state.endpoints)
    request.control observed
  have refined := Chan.RecoveryProtocol.Coordinated.stepObserved_refines
    binding.connection.chan
    (Chan.RecoveryProtocol.Design.CompiledPair.abstract state.endpoints)
    request.control observed
  have endpointsEq :=
    Chan.RecoveryProtocol.Design.CompiledPair.abstract_stepObserved
      binding.connection.chan state.endpoints request.control observed
  have epoch := binding.epochRep_advance
    (Chan.RecoveryProtocol.Design.CompiledPair.abstract state.endpoints)
    request.control state.base request.fifo represented.epoch
  rw [← represented.protocol] at refined
  refine ⟨⟨?_, ?_⟩, refined.2⟩
  · simpa [CertifiedRecoveryPortableBinding.wrapperStep, observed,
      coordinated] using refined.1
  · simpa [CertifiedRecoveryPortableBinding.wrapperStep, observed,
      coordinated, endpointsEq] using epoch

/-- The stock wrapper is itself a reusable recovery refinement; application
authors never construct this bundle. -/
def CertifiedRecoveryPortableBinding.wrapperRefinement
    (binding : CertifiedRecoveryPortableBinding) :
    Chan.RecoveryRefinement binding.connection.chan where
  ConcreteState := binding.WrapperState
  Request := binding.WrapperRequest
  reset := binding.wrapperReset
  step := binding.wrapperStep
  Rep := binding.WrapperRep
  reset_refines := binding.wrapperReset_refines
  step_refines := fun request represented =>
    binding.wrapperStep_refines _ _ request represented

/-- Each exact compiled behavioral component in the portable FIFO takes an
asserted synchronous reset edge to its source-level reset state. Together
with `compiledPair_commit_drives_fifoResets`, this covers the behavioral
components selected by the generated recovery wrapper; only their aggregate
state packaging across the structural wires remains. -/
theorem CertifiedRecoveryPortableBinding.compiledBaseResetEdges
    (binding : CertifiedRecoveryPortableBinding)
    (sourceInput sinkInput writerInput readerInput : InEnv)
    (sourceState sinkState writerState readerState : St) :
    let fifo := CertifiedPortable.fifoParameters binding.connection
      binding.base.depthAtLeastTwo binding.base.powerOfTwo
    let shape := CertifiedPortable.storageShape binding.connection
      binding.base.depthAtLeastTwo
    Compile.forgetSt
        (binding.base.controls.source.compiled.cycleOpenWithReset true
          sourceInput (Compile.convSt sourceState)) =
        (Cdc.AsyncFifoDesign.sourceControl fifo).reset ∧
      Compile.forgetSt
        (binding.base.controls.sink.compiled.cycleOpenWithReset true
          sinkInput (Compile.convSt sinkState)) =
        (Cdc.AsyncFifoDesign.sinkControl fifo).reset ∧
      Compile.forgetSt
        (binding.base.storage.writer.compiled.cycleOpenWithReset true
          writerInput (Compile.convSt writerState)) =
        (Cdc.AsyncQueueStorage.Portable.writerDesign shape).reset ∧
      Compile.forgetSt
        (binding.base.storage.reader.compiled.cycleOpenWithReset true
          readerInput (Compile.convSt readerState)) =
        (Cdc.AsyncQueueStorage.Portable.readerDesign shape).reset := by
  dsimp only
  constructor
  · simpa [Design.cycleOpenWithReset] using
      binding.base.controls.source.compiledCycleOpenWithReset_eq
        true sourceInput sourceState
  constructor
  · simpa [Design.cycleOpenWithReset] using
      binding.base.controls.sink.compiledCycleOpenWithReset_eq
        true sinkInput sinkState
  constructor
  · simpa [Design.cycleOpenWithReset] using
      binding.base.storage.writer.compiledCycleOpenWithReset_eq
        true writerInput writerState
  · simpa [Design.cycleOpenWithReset] using
      binding.base.storage.reader.compiledCycleOpenWithReset_eq
        true readerInput readerState

/-- The ordinary refinement's canonical reset packages the same two compiled
control reset states used by the structural wrapper. -/
theorem CertifiedRecoveryPortableBinding.baseReset_controls
    (binding : CertifiedRecoveryPortableBinding) :
    let fifo := CertifiedPortable.fifoParameters binding.connection
      binding.base.depthAtLeastTwo binding.base.powerOfTwo
    binding.refinement.reset.source =
        (Cdc.AsyncFifoDesign.sourceControl fifo).reset ∧
      binding.refinement.reset.sink =
        (Cdc.AsyncFifoDesign.sinkControl fifo).reset := by
  constructor <;> rfl

/-- The selected portable storage's read-domain component is packaged from
the same certified reader reset state. -/
theorem CertifiedRecoveryPortableBinding.baseReset_reader
    (binding : CertifiedRecoveryPortableBinding) :
    let shape := CertifiedPortable.storageShape binding.connection
      binding.base.depthAtLeastTwo
    binding.refinement.reset.composed.storage.reader =
      (Cdc.AsyncQueueStorage.Portable.readerDesign shape).reset := by
  rfl

/-- The selected portable storage's write-domain component is likewise the
compiled writer's all-zero reset state. -/
theorem CertifiedRecoveryPortableBinding.baseReset_writer
    (binding : CertifiedRecoveryPortableBinding) :
    let shape := CertifiedPortable.storageShape binding.connection
      binding.base.depthAtLeastTwo
    binding.refinement.reset.composed.storage.writer =
      (Cdc.AsyncQueueStorage.Portable.writerDesign shape).reset := by
  dsimp only
  change ((Cdc.AsyncQueueStorage.Portable.implementation
      (CertifiedPortable.storageShape binding.connection
        binding.base.depthAtLeastTwo)).reset (fun _ => 0)).writer = _
  exact Cdc.AsyncQueueStorage.Portable.implementation_reset_writer_zero _

/-- Repackage the four emitted behavioral component states into the concrete
state type of the already proved ordinary FIFO refinement. The FIFO and
reference-storage fields are proof ghosts and retain their canonical reset
values; every physically stateful field is supplied explicitly. -/
def CertifiedRecoveryPortableBinding.assembleBaseState
    (binding : CertifiedRecoveryPortableBinding)
    (source sink writer reader : St) : binding.refinement.ConcreteState :=
  { binding.refinement.reset with
    source := source
    sink := sink
    composed :=
      { binding.refinement.reset.composed with
        storage := { writer := writer, reader := reader } } }

/-- If all four compiled components take their asserted reset edge, their
aggregate concrete state is exactly the canonical empty FIFO state—not merely
componentwise similar to it. -/
theorem CertifiedRecoveryPortableBinding.assembleBaseState_of_resets
    (binding : CertifiedRecoveryPortableBinding)
    (source sink writer reader : St)
    (sourceReset : source = binding.refinement.reset.source)
    (sinkReset : sink = binding.refinement.reset.sink)
    (writerReset : writer =
      binding.refinement.reset.composed.storage.writer)
    (readerReset : reader =
      binding.refinement.reset.composed.storage.reader) :
    binding.assembleBaseState source sink writer reader =
      binding.refinement.reset := by
  subst source
  subst sink
  subst writer
  subst reader
  rfl

/-- The exact post-edge aggregate obtained from the four compiled modules
when their structurally connected reset inputs are asserted. -/
def CertifiedRecoveryPortableBinding.compiledResetEdgeBaseState
    (binding : CertifiedRecoveryPortableBinding)
    (sourceInput sinkInput writerInput readerInput : InEnv)
    (sourceState sinkState writerState readerState : St) :
    binding.refinement.ConcreteState :=
  binding.assembleBaseState
    (Compile.forgetSt
      (binding.base.controls.source.compiled.cycleOpenWithReset true
        sourceInput (Compile.convSt sourceState)))
    (Compile.forgetSt
      (binding.base.controls.sink.compiled.cycleOpenWithReset true
        sinkInput (Compile.convSt sinkState)))
    (Compile.forgetSt
      (binding.base.storage.writer.compiled.cycleOpenWithReset true
        writerInput (Compile.convSt writerState)))
    (Compile.forgetSt
      (binding.base.storage.reader.compiled.cycleOpenWithReset true
        readerInput (Compile.convSt readerState)))

/-- Closing theorem for the behavioral component reset edge: the exact four
compiled transitions package to the existing refinement's canonical reset. -/
theorem CertifiedRecoveryPortableBinding.compiledResetEdgeBaseState_eq
    (binding : CertifiedRecoveryPortableBinding)
    (sourceInput sinkInput writerInput readerInput : InEnv)
    (sourceState sinkState writerState readerState : St) :
    binding.compiledResetEdgeBaseState sourceInput sinkInput writerInput readerInput
      sourceState sinkState writerState readerState =
        binding.refinement.reset := by
  have edges := binding.compiledBaseResetEdges sourceInput sinkInput
    writerInput readerInput sourceState sinkState writerState readerState
  have controls := binding.baseReset_controls
  have writer := binding.baseReset_writer
  have reader := binding.baseReset_reader
  apply binding.assembleBaseState_of_resets
  · exact edges.1.trans controls.1.symm
  · exact edges.2.1.trans controls.2.symm
  · exact edges.2.2.1.trans writer.symm
  · exact edges.2.2.2.trans reader.symm

private def recoveryPortableWrapperName
    (binding : CertifiedRecoveryPortableBinding) : String :=
  "loom_compiled_recovery_async_fifo_" ++ binding.connection.chan.name

def CertifiedRecoveryPortableBinding.componentModules
    (binding : CertifiedRecoveryPortableBinding) : List (String × String) :=
  binding.base.componentModules ++
    [(binding.endpoint.compiled.name, binding.endpoint.renderedVerilog),
     (binding.datapath.source.compiled.name,
       binding.datapath.source.renderedVerilog),
     (binding.datapath.sink.compiled.name,
       binding.datapath.sink.renderedVerilog)]

/-- Structural join only. Every Boolean expression—including masks and local
FIFO reset generation—lives in one of the compiler-produced component
modules above. -/
def CertifiedRecoveryPortableBinding.wrapperText
    (binding : CertifiedRecoveryPortableBinding) : String :=
  let connection := binding.connection
  let shape := CertifiedPortable.storageShape connection
    binding.base.depthAtLeastTwo
  let fifo := CertifiedPortable.fifoParameters connection
    binding.base.depthAtLeastTwo binding.base.powerOfTwo
  let width := connection.width
  let pointerWidth := Cdc.AsyncFifoDesign.pointerWidth fifo
  let addressWidth := Cdc.AsyncFifoDesign.addressWidth fifo
  let slots := List.range connection.chan.depth
  let slotWires := slots.map fun index => s!"slot_{index}"
  let writerSlots := slots.map fun index =>
    s!"  .o_{Cdc.AsyncQueueStorage.Portable.slotName index}(slot_{index}),"
  let readerSlots := slots.map fun index =>
    s!"  .{Cdc.AsyncQueueStorage.Portable.slotName index}(slot_{index}),"
  let sourceModule := binding.base.controls.source.compiled.name
  let sinkModule := binding.base.controls.sink.compiled.name
  let writerModule := binding.base.storage.writer.compiled.name
  let readerModule := binding.base.storage.reader.compiled.name
  let endpointModule := binding.endpoint.compiled.name
  let sourceGuardModule := binding.datapath.source.compiled.name
  let sinkGuardModule := binding.datapath.sink.compiled.name
  String.intercalate "\n" <|
    [s!"module {recoveryPortableWrapperName binding}(",
     "  input wire src_clk, input wire dst_clk, input wire rst,",
     "  input wire src_recover, input wire dst_recover,",
     "  output wire src_recovered, output wire dst_recovered,",
     s!"  input wire src_valid, input wire {widthDecl width}src_payload,",
     "  output wire src_ready, output wire src_accepted,",
     "  output wire dst_valid,",
     s!"  output wire {widthDecl width}dst_payload, input wire dst_pop",
     ");",
     "wire source_request, source_acknowledge, source_blocked, source_flush;",
     "wire sink_request, sink_acknowledge, sink_blocked, sink_flush;",
     "wire source_fifo_reset, sink_fifo_reset;",
     "wire fifo_src_valid, fifo_src_ready, fifo_dst_valid, fifo_dst_pop;",
     s!"wire {widthDecl width}fifo_src_payload;",
     s!"wire {widthDecl pointerWidth}write_binary, write_gray, read_gray_sync0, read_gray_sync1;",
     s!"wire {widthDecl pointerWidth}read_binary, read_gray, write_gray_sync0, write_gray_sync1;",
     "wire write_take, read_take;",
     s!"wire {widthDecl addressWidth}write_address, read_address;",
     s!"wire {widthDecl width}write_data, read_sample;"] ++
    (if slotWires.isEmpty then [] else
      [s!"wire {widthDecl width}{String.intercalate ", " slotWires};"]) ++
    [s!"{endpointModule} u_source_recovery (",
     "  .clk(src_clk), .rst(rst), .recover(src_recover),",
     "  .raw_peer_request(sink_request), .raw_peer_acknowledge(sink_acknowledge),",
     "  .o_request(source_request), .o_acknowledge(source_acknowledge),",
     "  .o_flushed(src_recovered), .blocked(source_blocked), .local_flush(source_flush));",
     s!"{endpointModule} u_sink_recovery (",
     "  .clk(dst_clk), .rst(rst), .recover(dst_recover),",
     "  .raw_peer_request(source_request), .raw_peer_acknowledge(source_acknowledge),",
     "  .o_request(sink_request), .o_acknowledge(sink_acknowledge),",
     "  .o_flushed(dst_recovered), .blocked(sink_blocked), .local_flush(sink_flush));",
     s!"{sourceGuardModule} u_source_guard (",
     "  .clk(src_clk), .rst(rst), .source_valid(src_valid), .source_payload(src_payload),",
     "  .fifo_ready(fifo_src_ready), .recovery_blocked(source_blocked),",
     "  .recovery_flush(source_flush), .global_reset(rst),",
     "  .fifo_valid(fifo_src_valid), .fifo_payload(fifo_src_payload),",
     "  .source_ready(src_ready), .source_accepted(src_accepted),",
     "  .fifo_reset(source_fifo_reset));",
     s!"{sinkGuardModule} u_sink_guard (",
     "  .clk(dst_clk), .rst(rst), .fifo_valid(fifo_dst_valid), .fifo_payload(read_sample),",
     "  .sink_pop(dst_pop), .recovery_blocked(sink_blocked),",
     "  .recovery_flush(sink_flush), .global_reset(rst),",
     "  .fifo_pop(fifo_dst_pop), .sink_valid(dst_valid),",
     "  .sink_payload(dst_payload), .fifo_reset(sink_fifo_reset));",
     s!"{sourceModule} u_source_control (",
     "  .clk(src_clk), .rst(source_fifo_reset),",
     "  .source_valid(fifo_src_valid), .source_payload(fifo_src_payload),",
     "  .raw_read_gray(read_gray), .o_write_binary(write_binary), .o_write_gray(write_gray),",
     "  .o_read_gray_sync0(read_gray_sync0), .o_read_gray_sync1(read_gray_sync1),",
     "  .source_ready(fifo_src_ready), .write_take(write_take),",
     "  .write_address(write_address), .write_data(write_data));",
     s!"{sinkModule} u_sink_control (",
     "  .clk(dst_clk), .rst(sink_fifo_reset), .sink_pop(fifo_dst_pop),",
     "  .raw_write_gray(write_gray), .o_read_binary(read_binary), .o_read_gray(read_gray),",
     "  .o_write_gray_sync0(write_gray_sync0), .o_write_gray_sync1(write_gray_sync1),",
     "  .sink_valid(fifo_dst_valid), .read_take(read_take), .read_address(read_address));",
     s!"{writerModule} u_storage_writer (",
     "  .clk(src_clk), .rst(source_fifo_reset),"] ++ writerSlots ++
    ["  ." ++ (Cdc.AsyncQueueStorage.Portable.writeEnable shape).name ++ "(write_take),",
     "  ." ++ (Cdc.AsyncQueueStorage.Portable.writeAddress shape).name ++ "(write_address),",
     "  ." ++ (Cdc.AsyncQueueStorage.Portable.writeData shape).name ++ "(write_data));",
     s!"{readerModule} u_storage_reader (",
     "  .clk(dst_clk), .rst(sink_fifo_reset),"] ++ readerSlots ++
    ["  ." ++ (Cdc.AsyncQueueStorage.Portable.readEnable shape).name ++ "(read_take),",
     "  ." ++ (Cdc.AsyncQueueStorage.Portable.readAddress shape).name ++ "(read_address),",
     "  .read_sample(read_sample));",
     "endmodule"]

def CertifiedRecoveryPortableBinding.instanceText
    (binding : CertifiedRecoveryPortableBinding) (info : CrossingInfo) : String :=
  let sourceClock := info.sourceClock.getD "missing_source_clock"
  let sinkClock := info.sinkClock.getD "missing_sink_clock"
  let stem := "__loom_chan_" ++ info.channel ++ "_"
  let sourceValid := BoundImplementation.islandOutput info.source
    (stem ++ "src_valid")
  let sourcePayload := BoundImplementation.islandOutput info.source
    (stem ++ "src_payload")
  let sourceReady := BoundImplementation.islandSignal info.source
    (stem ++ "src_ready")
  let sinkValid := BoundImplementation.islandSignal info.sink
    (stem ++ "dst_valid")
  let sinkPayload := BoundImplementation.islandSignal info.sink
    (stem ++ "dst_payload")
  let sinkPop := BoundImplementation.islandOutput info.sink
    (stem ++ "dst_pop")
  let sourceRecover := BoundImplementation.islandSignal info.source "recover"
  let sinkRecover := BoundImplementation.islandSignal info.sink "recover"
  let sourceDone := s!"__loom_recovery_{info.channel}_src_done"
  let sinkDone := s!"__loom_recovery_{info.channel}_dst_done"
  s!"{recoveryPortableWrapperName binding} u_{info.channel} (\n" ++
    s!"  .src_clk({sourceClock}), .dst_clk({sinkClock}), .rst(rst),\n" ++
    s!"  .src_recover({sourceRecover}), .dst_recover({sinkRecover}),\n" ++
    s!"  .src_recovered({sourceDone}), .dst_recovered({sinkDone}),\n" ++
    s!"  .src_valid({sourceValid}), .src_payload({sourcePayload}), .src_ready({sourceReady}),\n" ++
    s!"  .src_accepted({BoundImplementation.islandSignal info.source (stem ++ "src_accepted")}),\n" ++
    s!"  .dst_valid({sinkValid}), .dst_payload({sinkPayload}), .dst_pop({sinkPop}));\n"

def CertifiedRecoveryPortableBinding.toPhysical
    (binding : CertifiedRecoveryPortableBinding) : BoundImplementation :=
  BoundImplementation.customInstance binding.connection
    "loom.compiled.recovery_portable_fifo" .any binding.refinement
    (fun _ => recoveryPortableWrapperName binding)
    (fun _ => binding.wrapperText)
    binding.instanceText
    (fun info => portablePhysicalIntent info
      (Cdc.AsyncFifoDesign.pointerWidth
        (CertifiedPortable.fifoParameters binding.connection
          binding.base.depthAtLeastTwo binding.base.powerOfTwo)))
    compiledRecoveryPortableTiming

/-! ## Compiled same-clock binding -/

/-- The stock synchronous FIFO compiled from the same `Chan.adapter` whose
refinement is proved in `ChanSync`. It supports every positive depth and both
co-tick policies, but its physical clock rule requires aligned endpoints. -/
structure CertifiedSyncBinding where
  connection : SystemConnection
  positiveDepth : 0 < connection.chan.depth
  adapter : CertifiedDesign connection.chan.physicalAdapter

def CertifiedSyncBinding.key (binding : CertifiedSyncBinding) : ConnectionKey :=
  binding.connection.key

def CertifiedSyncBinding.refinement (binding : CertifiedSyncBinding) :
    Chan.Refinement binding.connection.chan :=
  binding.connection.chan.syncRefinement binding.positiveDepth

private def syncWrapperName (binding : CertifiedSyncBinding) : String :=
  "loom_compiled_sync_fifo_" ++ binding.connection.chan.name

def CertifiedSyncBinding.componentModules
    (binding : CertifiedSyncBinding) : List (String × String) :=
  [(binding.adapter.compiled.name, binding.adapter.renderedVerilog)]

/-- Purely structural wrapper from the System endpoint convention to the
ordinary compiled FIFO ports. `dst_clk` is retained in the common wrapper
interface; `.same` clock checking proves both endpoint names resolve to the
same clock before this artifact can be constructed. -/
def CertifiedSyncBinding.wrapperText (binding : CertifiedSyncBinding) : String :=
  let connection := binding.connection
  let channel := connection.chan
  let width := connection.width
  String.intercalate "\n" [
    s!"module {syncWrapperName binding}(",
    "  input wire src_clk, input wire dst_clk, input wire rst,",
    s!"  input wire src_valid, input wire {widthDecl width}src_payload,",
    "  output wire src_ready,",
    "  output wire dst_valid,",
    s!"  output wire {widthDecl width}dst_payload, input wire dst_pop",
    ");",
    s!"{binding.adapter.compiled.name} u_sync_fifo (",
    "  .clk(src_clk), .rst(rst),",
    s!"  .{channel.pushName}(src_valid),",
    s!"  .{channel.pushPayloadName}(src_payload),",
    s!"  .{channel.popName}(dst_pop),",
    "  .source_ready(src_ready), .sink_valid(dst_valid),",
    "  .sink_payload(dst_payload));",
    "endmodule" ]

def CertifiedSyncBinding.toPhysical
    (binding : CertifiedSyncBinding) : BoundImplementation :=
  BoundImplementation.custom binding.connection "loom.compiled.sync_fifo"
    .same binding.refinement
    (fun _ => syncWrapperName binding)
    (fun _ => binding.wrapperText)
    (fun _ => []) compiledSyncTiming

/-- Closed compiler-produced realization choices supported by the ordinary
application facade. The sum is deliberately small: a synchronous FIFO for
aligned islands and a portable Gray FIFO for unrelated clocks. -/
inductive CertifiedChannelBinding where
  | synchronous (binding : CertifiedSyncBinding)
  | portable (binding : CertifiedPortableBinding)
  | registeredStorage (binding : CertifiedRegisteredStorageBinding)
  | recoveryPortable (binding : CertifiedRecoveryPortableBinding)

namespace CertifiedChannelBinding

def connection : CertifiedChannelBinding → SystemConnection
  | .synchronous binding => binding.connection
  | .portable binding => binding.connection
  | .registeredStorage binding => binding.connection
  | .recoveryPortable binding => binding.connection

def key (binding : CertifiedChannelBinding) : ConnectionKey :=
  binding.connection.key

def refinement (binding : CertifiedChannelBinding) :
    Chan.Refinement binding.connection.chan := by
  cases binding with
  | synchronous binding => exact binding.refinement
  | portable binding => exact binding.refinement
  | registeredStorage binding => exact binding.refinement
  | recoveryPortable binding => exact binding.refinement

def recoveryRefinement? (binding : CertifiedChannelBinding) :
    Option (Chan.RecoveryRefinement binding.connection.chan) :=
  match binding with
  | .synchronous _ => none
  | .portable _ => none
  | .registeredStorage _ => none
  | .recoveryPortable recovery => some recovery.recoveryRefinement

def recoveryCapable : CertifiedChannelBinding → Bool
  | .recoveryPortable _ => true
  | _ => false

def componentModules : CertifiedChannelBinding → List (String × String)
  | .synchronous binding => binding.componentModules
  | .portable binding => binding.componentModules
  | .registeredStorage binding => binding.componentModules
  | .recoveryPortable binding => binding.componentModules

def toPhysical : CertifiedChannelBinding → BoundImplementation
  | .synchronous binding => binding.toPhysical
  | .portable binding => binding.toPhysical
  | .registeredStorage binding => binding.toPhysical
  | .recoveryPortable binding => binding.toPhysical

@[simp] theorem toPhysical_connection (binding : CertifiedChannelBinding) :
    binding.toPhysical.connection = binding.connection := by
  cases binding <;> rfl

@[simp] theorem toPhysical_key (binding : CertifiedChannelBinding) :
    binding.toPhysical.key = binding.key := by
  simp [BoundImplementation.key, key]

def emissionCheck : CertifiedChannelBinding → Except String Unit
  | .synchronous binding => binding.connection.chan.physicalAdapter.emitCheck
  | .portable binding => do
      (Cdc.AsyncFifoDesign.sourceControl
        (CertifiedPortable.fifoParameters binding.connection
          binding.depthAtLeastTwo binding.powerOfTwo)).emitCheck
      (Cdc.AsyncFifoDesign.sinkControl
        (CertifiedPortable.fifoParameters binding.connection
          binding.depthAtLeastTwo binding.powerOfTwo)).emitCheck
      (Cdc.AsyncQueueStorage.Portable.writerDesign
        (CertifiedPortable.storageShape binding.connection
          binding.depthAtLeastTwo)).emitCheck
      (Cdc.AsyncQueueStorage.Portable.readerDesign
        (CertifiedPortable.storageShape binding.connection
          binding.depthAtLeastTwo)).emitCheck
  | .registeredStorage binding => binding.emissionCheck
  | .recoveryPortable binding => do
      (Cdc.AsyncFifoDesign.sourceControl
        (CertifiedPortable.fifoParameters binding.connection
          binding.base.depthAtLeastTwo binding.base.powerOfTwo)).emitCheck
      (Cdc.AsyncFifoDesign.sinkControl
        (CertifiedPortable.fifoParameters binding.connection
          binding.base.depthAtLeastTwo binding.base.powerOfTwo)).emitCheck
      (Cdc.AsyncQueueStorage.Portable.writerDesign
        (CertifiedPortable.storageShape binding.connection
          binding.base.depthAtLeastTwo)).emitCheck
      (Cdc.AsyncQueueStorage.Portable.readerDesign
        (CertifiedPortable.storageShape binding.connection
          binding.base.depthAtLeastTwo)).emitCheck
      Chan.RecoveryProtocol.Design.endpoint.emitCheck
      (Chan.RecoveryDatapath.sourceDesign
        { width := binding.connection.width }).emitCheck
      (Chan.RecoveryDatapath.sinkDesign
        { width := binding.connection.width }).emitCheck

end CertifiedChannelBinding

/-- A CertifiedSystem with exactly one compiler-produced binding per declared
connection. The same ordered coverage equation constructs the ordinary
physical artifact plan and proves that no channel disappears. -/
def resetBindingsCheck (system : System)
    (bindings : List CertifiedChannelBinding) : Bool :=
  match system.resetPolicy with
  | .coordinated => !bindings.any CertifiedChannelBinding.recoveryCapable
  | .independentFlush => bindings.all CertifiedChannelBinding.recoveryCapable

structure CertifiedRealizedSystem (system : System)
    (certified : CertifiedSystem system) where
  bindings : List CertifiedChannelBinding
  coverage : bindings.map CertifiedChannelBinding.key =
    system.connections.map SystemConnection.key
  clockRules : (bindings.map CertifiedChannelBinding.toPhysical).all
    (clockRuleOk system) = true
  /-- Reset capability is part of certification rather than merely an IO-time
  check. An invalid policy/binding mixture cannot be packaged for release. -/
  resetCompatibility : resetBindingsCheck system bindings = true

namespace CertifiedRealizedSystem

def realized {system : System} {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified) : RealizedSystem :=
  realizeChecked system (artifact.bindings.map (·.toPhysical))
    (by
      rw [List.map_map]
      calc
        artifact.bindings.map
            (BoundImplementation.key ∘ CertifiedChannelBinding.toPhysical) =
            artifact.bindings.map CertifiedChannelBinding.key := by
              apply List.map_congr_left
              intro binding _
              exact CertifiedChannelBinding.toPhysical_key binding
        _ = system.connections.map SystemConnection.key := artifact.coverage)
    artifact.clockRules

private def insertModule (modules : List (String × String))
    (candidate : String × String) : List (String × String) :=
  if modules.any (fun module => module.1 = candidate.1) then modules
  else modules ++ [candidate]

private def uniqueModules (modules : List (String × String)) :
    List (String × String) := modules.foldl insertModule []

/-- Exact generated System Verilog. Island modules and all behavioral channel
modules are proved compiler projections; wrappers and the top are structural
renderers over the checked connection inventory. -/
def renderedVerilog {system : System} {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified) : String :=
  let physical := artifact.realized.artifacts
  let components := uniqueModules
    (artifact.bindings.flatMap (·.componentModules))
  String.intercalate "\n\n" <|
    physical.islandModules.map (·.2) ++
    components.map (·.2) ++
    physical.instances.map (·.moduleText) ++
    [physical.topModule.render]

def renderedUTF8 {system : System} {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified) : ByteArray :=
  artifact.renderedVerilog.toUTF8

/-- Byte-exact release binding: there is no alternate System renderer or
handwritten CDC body in the statement. -/
theorem renderedUTF8_eq {system : System} {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified) :
    artifact.renderedUTF8 = artifact.renderedVerilog.toUTF8 := rfl

/-- Fail-closed gate for the compiler-only path. Besides the ordinary System
assembly checks, every generated behavioral Design must pass the ordinary
emission gate and no two module names may denote different exact texts. -/
def emissionCheck {system : System} {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified) : Except String Unit := do
  match system.resetPolicy with
  | .coordinated =>
      if artifact.bindings.any CertifiedChannelBinding.recoveryCapable then
        throw "System.emitCertified: recovery bindings require independentFlush policy"
  | .independentFlush =>
      if !artifact.bindings.all CertifiedChannelBinding.recoveryCapable then
        throw "System.emitCertified: every independentFlush channel requires a recovery refinement"
  artifact.realized.emissionCheck
  for binding in artifact.bindings do
    binding.emissionCheck
  let physical := artifact.realized.artifacts
  let modules := physical.islandModules ++
    artifact.bindings.flatMap (·.componentModules) ++
    physical.instances.map fun entry => (entry.moduleName, entry.moduleText)
  for module in modules do
    if modules.any fun other => other.1 = module.1 && other.2 != module.2 then
      throw s!"System.emitCertified: module name '{module.1}' has multiple bodies"

/-- Exact files for the certified path. Constraints and inventory retain the
ordinary complete key domain; only the RTL payload is replaced by the closed
compiler-produced rendering above. -/
def emissionArtifacts {system : System} {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified) :
    List EmissionArtifact :=
  artifact.realized.emissionArtifacts.map fun emitted =>
    if emitted.kind = .rtl then { emitted with text := artifact.renderedVerilog }
    else emitted

/-- The concrete `system.v` value selected by the certified emitter.  This is
not a parallel publication object: it is definitionally the first member of
`emissionArtifacts`, including the complete crossing-key inventory. -/
def rtlArtifact {system : System} {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified) : EmissionArtifact :=
  { kind := .rtl
    relativePath := "system.v"
    text := artifact.renderedVerilog
    crossingKeys := artifact.realized.artifacts.instances.map (·.key) }

@[simp] theorem rtlArtifact_kind {system : System}
    {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified) :
    artifact.rtlArtifact.kind = .rtl := rfl

@[simp] theorem rtlArtifact_path {system : System}
    {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified) :
    artifact.rtlArtifact.relativePath = "system.v" := rfl

/-- The byte-bound RTL value is literally traversed by `emit`; a release
cannot cite a cousin renderer while the writer consumes another value. -/
theorem rtlArtifact_mem {system : System} {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified) :
    artifact.rtlArtifact ∈ artifact.emissionArtifacts := by
  simp [rtlArtifact, emissionArtifacts, RealizedSystem.emissionArtifacts]

@[simp] theorem rtlArtifact_exact {system : System}
    {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified) :
    artifact.rtlArtifact.text.toUTF8 = artifact.renderedUTF8 := rfl

def emit {system : System} {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified)
    (directory : System.FilePath) : IO Unit := do
  match artifact.emissionCheck with
  | .ok _ => pure ()
  | .error message => throw <| IO.userError message
  for emitted in artifact.emissionArtifacts do
    let path := directory / emitted.relativePath
    let changed ← Loom.Artifact.writeText path emitted.text
    IO.println s!"{path} {if changed then "written" else "unchanged"}"

/-- The literal RTL artifact selected by `emissionArtifacts` is the same byte
array carried by the release theorem. -/
theorem emittedRTL_exact {system : System} {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified)
    (emitted : EmissionArtifact) (member : emitted ∈ artifact.emissionArtifacts)
    (kind : emitted.kind = .rtl) :
    emitted.text.toUTF8 = artifact.renderedUTF8 := by
  simp only [emissionArtifacts, List.mem_map] at member
  obtain ⟨base, baseMember, rfl⟩ := member
  by_cases isRTL : base.kind = .rtl
  · simp [isRTL, renderedUTF8]
  · simp [isRTL] at kind

/-- Every file traversed by the certified emitter retains the same complete
ordered crossing-key domain. Replacing the base RTL text with the closed
compiler-produced rendering cannot change its inventory identity. -/
theorem every_emitted_artifact_complete {system : System}
    {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified)
    (emitted : EmissionArtifact) (member : emitted ∈ artifact.emissionArtifacts) :
    emitted.crossingKeys =
      system.connections.map SystemConnection.key := by
  simp only [emissionArtifacts, List.mem_map] at member
  obtain ⟨base, baseMember, rfl⟩ := member
  have complete := artifact.realized.every_emitted_artifact_complete base baseMember
  by_cases isRTL : base.kind = .rtl
  · simpa [isRTL] using complete
  · simpa [isRTL] using complete

/-- The realization's executable channel model is exactly the parametric
technology-neutral refinement derived from the compiled controls and proved
register-bank witness. -/
theorem binding_refines {system : System} {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified)
    (binding : CertifiedChannelBinding) (member : binding ∈ artifact.bindings) :
    ∃ physical ∈ artifact.realized.bindings,
      physical.connection = binding.connection := by
  refine ⟨binding.toPhysical, ?_, binding.toPhysical_connection⟩
  change binding.toPhysical ∈ artifact.bindings.map (·.toPhysical)
  exact List.mem_map.mpr ⟨binding, member, rfl⟩

/-- Every binding in a certified independent-reset artifact carries an actual
loss-explicit recovery refinement. This follows from the constructor-level
reset compatibility proof; it is not inferred from a successful IO wrapper. -/
theorem binding_recoveryRefines {system : System}
    {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified)
    (policy : system.resetPolicy = .independentFlush)
    (binding : CertifiedChannelBinding) (member : binding ∈ artifact.bindings) :
    ∃ recovery : Chan.RecoveryRefinement binding.connection.chan,
      binding.recoveryRefinement? = some recovery := by
  have allCapable :
      artifact.bindings.all CertifiedChannelBinding.recoveryCapable = true := by
    simpa [resetBindingsCheck, policy] using artifact.resetCompatibility
  have capable := List.all_eq_true.mp allCapable binding member
  cases binding with
  | synchronous binding => simp [CertifiedChannelBinding.recoveryCapable] at capable
  | portable binding => simp [CertifiedChannelBinding.recoveryCapable] at capable
  | registeredStorage binding => simp [CertifiedChannelBinding.recoveryCapable] at capable
  | recoveryPortable binding =>
      exact ⟨binding.recoveryRefinement, rfl⟩

/-- Per-channel semantic join for independently reset Systems.  Once the
physical wrapper's observable protocol event is identified with the event
projected by `System.advanceRecovery`, the certified recovery refinement says
that its next concrete state represents exactly the queue stored by that
System transition.  Accepted and delivered observations agree at the same
time.

This low-level theorem accepts an event equality so it remains reusable for
custom recovery protocols. `coordinatedProtocol_event_eq_systemRecovery`
below discharges that equality for Loom's stock multi-channel coordinator. -/
theorem binding_recoveryStep_refines_advanceRecovery
    {system : System} {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified)
    (policy : system.resetPolicy = .independentFlush)
    (binding : CertifiedChannelBinding) (member : binding ∈ artifact.bindings)
    (found : system.connections.find? (fun candidate =>
      candidate.chan.name == binding.connection.chan.name) =
        some binding.connection)
    (systemEvent : System.RecoveryEvent) (external : String → InEnv)
    (systemState : system.State)
    (queue : Chan.State binding.connection.width)
    (queueEq : queue = system.channelState systemState binding.connection) :
    ∃ recovery : Chan.RecoveryRefinement binding.connection.chan,
      ∀ (concrete : recovery.ConcreteState) (request : recovery.Request),
        recovery.Rep queue concrete →
        (recovery.step concrete request).event =
            system.recoveryChannelEvent systemEvent systemState
              binding.connection →
        let next := recovery.step concrete request
        recovery.Rep
            (system.channelState
              (system.advanceRecovery systemEvent external systemState)
              binding.connection)
            next.state ∧
          (binding.connection.chan.recoveryStep queue next.event).accepted =
            next.accepted ∧
          (binding.connection.chan.recoveryStep queue next.event).delivered =
            next.delivered := by
  obtain ⟨recovery, recoveryEq⟩ :=
    artifact.binding_recoveryRefines policy binding member
  refine ⟨recovery, ?_⟩
  intro concrete request represented eventEq
  have refined := recovery.step_refines request represented
  dsimp only at refined ⊢
  have systemQueueEq := system.channelState_advanceRecovery_eq_recoveryStep
    systemEvent external systemState binding.connection found
  rw [queueEq] at refined
  rw [eventEq] at refined
  rw [queueEq, eventEq]
  rw [systemQueueEq]
  exact refined

/-- Island-side semantic join for live recovery. The exact compiled module
carried by the System certificate takes its synchronous reset edge to the
same island state that `System.advanceRecovery` assigns. This is generic
compiler correctness, not a recovery-specific RTL assumption. -/
theorem islandCompiledReset_refines_advanceRecovery
    {system : System} {certified : CertifiedSystem system}
    (_artifact : CertifiedRealizedSystem system certified)
    (event : System.RecoveryEvent) (external : String → InEnv)
    (systemState : system.State) (island : SystemIsland)
    (found : system.findIsland? island.name = some island)
    (reset : event.resets island.name = true) :
    let islandCert := certified.islandCertificate island.name island found
    Compile.forgetSt
        (islandCert.compiled.cycleOpenWithReset true
          (external island.name)
          (Compile.convSt (systemState.island island.name))) =
      (system.advanceRecovery event external systemState).island island.name := by
  dsimp only
  rw [CertifiedDesign.compiledCycleOpenWithReset_eq
    (certified.islandCertificate island.name island found)]
  simp only [Design.cycleOpenWithReset, if_true]
  exact (system.advanceRecovery_island_reset event external systemState
    island found reset).symm

/-- The closed proof package for graceful-recovery assembly. It records the
exact ordered connection coverage, a recovery refinement for every binding,
and the compiler certificate for the fixed coordinator cell. The remaining
text boundary is structural composition, as documented in
`MULTICLOCK_BOUNDARY.md`. -/
structure RecoveryAssemblyCertificate {system : System}
    {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified) where
  policy : system.resetPolicy = .independentFlush
  bindingRecovery : ∀ binding ∈ artifact.bindings,
    ∃ recovery : Chan.RecoveryRefinement binding.connection.chan,
      binding.recoveryRefinement? = some recovery
  coordinator : CertifiedDesign RecoveryCoordinator.design
  /-- A coordinator-visible endpoint completion implies that the exact
  compiler-source reset-hold expression remains asserted. -/
  endpointDoneKeepsReset : ∀ state : St,
    Chan.RecoveryProtocol.Design.bool
        (Chan.RecoveryProtocol.Design.flushedOut.rd.eval state) = true →
      Chan.RecoveryProtocol.Design.bool
        (Chan.RecoveryProtocol.Design.resetHeld.eval state) = true

def recoveryAssemblyCertificate {system : System}
    {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified)
    (policy : system.resetPolicy = .independentFlush) :
    RecoveryAssemblyCertificate artifact where
  policy := policy
  bindingRecovery := fun binding member =>
    artifact.binding_recoveryRefines policy binding member
  coordinator := RecoveryCoordinator.certified
  endpointDoneKeepsReset :=
    Chan.RecoveryProtocol.Design.resetHeld_of_flushed_any

def compiledEndpointDone (state : St) : Bool :=
  Chan.RecoveryProtocol.Design.bool
    (Chan.RecoveryProtocol.Design.flushedOut.rd.eval state)

def compiledEndpointResetHeld (state : St) : Bool :=
  Chan.RecoveryProtocol.Design.bool
    (Chan.RecoveryProtocol.Design.resetHeld.eval state)

/-- Exact compiler-source wiring fact on the global commit edge: the two
compiled endpoint reset-hold expressions pass through the two compiled guards
as asserted FIFO reset inputs. Payload and ordinary ready/pop values are
irrelevant because reset is dominant. -/
theorem compiledPair_commit_drives_fifoResets
    (p : Chan.RecoveryDatapath.Parameters)
    (state : Chan.RecoveryProtocol.Design.CompiledPair.State p.width)
    (request : Chan.RecoveryProtocol.Coordinated.Request p.width)
    (complete : Chan.RecoveryProtocol.Coordinated.commits
      (Chan.RecoveryProtocol.Design.CompiledPair.abstract state) request = true)
    (sourceValid : Bool) (sourcePayload : BitVec p.width)
    (fifoReady fifoValid sinkPop : Bool) :
    let sourceFlush := compiledEndpointResetHeld state.source
    let sinkFlush := compiledEndpointResetHeld state.sink
    Chan.RecoveryDatapath.sourceFifoResetExpr.eval
        ((Chan.RecoveryDatapath.sourceDesign p).reset.setInputs
          (Chan.RecoveryDatapath.sourceDesign p).inputs
          (Chan.RecoveryDatapath.sourceDrive p sourceValid sourcePayload fifoReady
            false sourceFlush false)) = 1#1 ∧
      Chan.RecoveryDatapath.sinkFifoResetExpr.eval
        ((Chan.RecoveryDatapath.sinkDesign p).reset.setInputs
          (Chan.RecoveryDatapath.sinkDesign p).inputs
          (Chan.RecoveryDatapath.sinkDrive p fifoValid sourcePayload sinkPop
            false sinkFlush false)) = 1#1 := by
  dsimp only
  have held :=
    Chan.RecoveryProtocol.Design.CompiledPair.commit_resets_both
      state request complete
  constructor
  · rw [Chan.RecoveryDatapath.source_fifoReset]
    simp [compiledEndpointResetHeld, held.1, Chan.RecoveryDatapath.boolBit]
  · rw [Chan.RecoveryDatapath.sink_fifoReset]
    simp [compiledEndpointResetHeld, held.2, Chan.RecoveryDatapath.boolBit]

/-- One proof object collecting every behavioral fact at a globally
coordinated channel commit. It is polymorphic in all ordinary payload, input,
and pre-edge component states. -/
structure GlobalCommitClosure
    (binding : CertifiedRecoveryPortableBinding)
    (state : Chan.RecoveryProtocol.Design.CompiledPair.State
      binding.connection.width)
    (request : Chan.RecoveryProtocol.Coordinated.Request
      binding.connection.width) : Prop where
  sourceEndpointReset : compiledEndpointResetHeld state.source = true
  sinkEndpointReset : compiledEndpointResetHeld state.sink = true
  sourceGuardReset : ∀ (valid : Bool) (payload : BitVec binding.connection.width)
      (ready : Bool),
    let p : Chan.RecoveryDatapath.Parameters :=
      { width := binding.connection.width }
    Chan.RecoveryDatapath.sourceFifoResetExpr.eval
      ((Chan.RecoveryDatapath.sourceDesign p).reset.setInputs
        (Chan.RecoveryDatapath.sourceDesign p).inputs
        (Chan.RecoveryDatapath.sourceDrive p valid payload ready false
          (compiledEndpointResetHeld state.source) false)) = 1#1
  sinkGuardReset : ∀ (valid : Bool) (payload : BitVec binding.connection.width)
      (pop : Bool),
    let p : Chan.RecoveryDatapath.Parameters :=
      { width := binding.connection.width }
    Chan.RecoveryDatapath.sinkFifoResetExpr.eval
      ((Chan.RecoveryDatapath.sinkDesign p).reset.setInputs
        (Chan.RecoveryDatapath.sinkDesign p).inputs
        (Chan.RecoveryDatapath.sinkDrive p valid payload pop false
          (compiledEndpointResetHeld state.sink) false)) = 1#1
  compiledBaseReset : ∀
      (sourceInput sinkInput writerInput readerInput : InEnv)
      (sourceState sinkState writerState readerState : St),
    binding.compiledResetEdgeBaseState sourceInput sinkInput writerInput readerInput
      sourceState sinkState writerState readerState = binding.refinement.reset
  epochReestablished : binding.EpochRep
    (Chan.RecoveryProtocol.Coordinated.step binding.connection.chan
      (Chan.RecoveryProtocol.Design.CompiledPair.abstract state) request).state
    binding.refinement.reset

/-- The full behavioral commit edge closes: endpoint outputs, guard outputs,
the four exact compiled base components, and the retained logical epoch all
meet at the ordinary refinement's empty reset state. -/
theorem globalCommit_closure
    (binding : CertifiedRecoveryPortableBinding)
    (state : Chan.RecoveryProtocol.Design.CompiledPair.State
      binding.connection.width)
    (request : Chan.RecoveryProtocol.Coordinated.Request
      binding.connection.width)
    (complete : Chan.RecoveryProtocol.Coordinated.commits
      (Chan.RecoveryProtocol.Design.CompiledPair.abstract state) request = true) :
    GlobalCommitClosure binding state request := by
  have held := Chan.RecoveryProtocol.Design.CompiledPair.commit_resets_both
    state request complete
  refine {
    sourceEndpointReset := held.1
    sinkEndpointReset := held.2
    sourceGuardReset := ?_
    sinkGuardReset := ?_
    compiledBaseReset := ?_
    epochReestablished := binding.epochRep_of_globalCommit_reset _ _ complete }
  · intro valid payload ready
    exact (compiledPair_commit_drives_fifoResets
      { width := binding.connection.width } state request complete
      valid payload ready false false).1
  · intro valid payload pop
    exact (compiledPair_commit_drives_fifoResets
      { width := binding.connection.width } state request complete
      false payload false valid pop).2
  · intro sourceInput sinkInput writerInput readerInput
      sourceState sinkState writerState readerState
    exact binding.compiledResetEdgeBaseState_eq sourceInput sinkInput
      writerInput readerInput sourceState sinkState writerState readerState

/-- System-level reset-skew closure for the generated coordinator.  Endpoint
states are indexed by the exact structured incident-half domain. If an island
reports recovery complete, every one of those compiler-source endpoint states
has its FIFO reset-hold expression asserted. -/
theorem recoveryComplete_holds_all_compiledEndpointResets
    (system : System) (island : SystemIsland) (request : Bool)
    (endpointState : RecoveryEndpointKey → St)
    (complete : system.recoveryComplete island request
      (fun endpoint => compiledEndpointDone (endpointState endpoint)) = true) :
    ∀ endpoint ∈ system.recoveryEndpointsFor island,
      compiledEndpointResetHeld (endpointState endpoint) = true := by
  apply system.recoveryComplete_implies_all island request
    (fun endpoint => compiledEndpointDone (endpointState endpoint))
    (fun endpoint => compiledEndpointResetHeld (endpointState endpoint))
  · intro endpoint done
    exact Chan.RecoveryProtocol.Design.resetHeld_of_flushed_any
      (endpointState endpoint) done
  · exact complete

/-- The generated island coordinator selects one common logical flush point
for every incident channel.  Endpoint-local FIFO resets may have happened on
different earlier clocks, but they remain hidden as stuttering behind the
coordinated protocol's retained logical epoch. -/
theorem coordinatedProtocol_event_eq_systemRecovery
    (system : System) (island : SystemIsland)
    (connection : SystemConnection) (member : connection ∈ system.connections)
    (incident : (connection.source == island.name ||
      connection.sink == island.name) = true)
    (systemEvent : System.RecoveryEvent) (systemState : system.State)
    (reset : systemEvent.resets island.name = true)
    (protocol : Chan.RecoveryProtocol.State connection.width)
    (endpointRequest : Chan.RecoveryProtocol.Request connection.width)
    (pending : protocol.recovering = true)
    (done : RecoveryEndpointKey → Bool)
    (sourceDone : done ⟨connection.key, .source⟩ =
      (Chan.RecoveryProtocol.nextSource protocol endpointRequest).flushed)
    (sinkDone : done ⟨connection.key, .sink⟩ =
      (Chan.RecoveryProtocol.nextSink protocol endpointRequest).flushed)
    (complete : system.recoveryComplete island true done = true) :
    let request : Chan.RecoveryProtocol.Coordinated.Request connection.width :=
      { endpoint := endpointRequest, commit := true }
    (Chan.RecoveryProtocol.Coordinated.step connection.chan protocol request).event =
      system.recoveryChannelEvent systemEvent systemState connection := by
  dsimp only
  have both := system.recoveryComplete_incident_both island connection member
    incident true done complete
  have sourceFlushed :
      (Chan.RecoveryProtocol.nextSource protocol endpointRequest).flushed = true := by
    rw [← sourceDone]
    exact both.1
  have sinkFlushed :
      (Chan.RecoveryProtocol.nextSink protocol endpointRequest).flushed = true := by
    rw [← sinkDone]
    exact both.2
  have committed : Chan.RecoveryProtocol.Coordinated.commits protocol
      ({ endpoint := endpointRequest, commit := true } :
        Chan.RecoveryProtocol.Coordinated.Request connection.width) = true := by
    simp [Chan.RecoveryProtocol.Coordinated.commits,
      Chan.RecoveryProtocol.Coordinated.commitReady, pending,
      sourceFlushed, sinkFlushed]
  have flush :=
    (Chan.RecoveryProtocol.Coordinated.step_event_eq_flush_iff
      connection.chan protocol
      ({ endpoint := endpointRequest, commit := true } :
        Chan.RecoveryProtocol.Coordinated.Request connection.width)).2 committed
  have affected : systemEvent.affects connection = true := by
    simp only [Bool.or_eq_true, beq_iff_eq] at incident
    rcases incident with sourceEq | sinkEq
    · simp [System.RecoveryEvent.affects, sourceEq, reset]
    · simp [System.RecoveryEvent.affects, sinkEq, reset]
  simpa [System.recoveryChannelEvent, affected] using flush

/-- Physical-event form of the same global alignment. Conservative FIFO
stalls affect only `observed`; a globally committed recovery is still the one
common `.flush` event. -/
theorem coordinatedObserved_event_eq_systemRecovery
    (system : System) (island : SystemIsland)
    (connection : SystemConnection) (member : connection ∈ system.connections)
    (incident : (connection.source == island.name ||
      connection.sink == island.name) = true)
    (systemEvent : System.RecoveryEvent) (systemState : system.State)
    (reset : systemEvent.resets island.name = true)
    (protocol : Chan.RecoveryProtocol.State connection.width)
    (endpointRequest : Chan.RecoveryProtocol.Request connection.width)
    (observed : Chan.Event connection.width)
    (pending : protocol.recovering = true)
    (done : RecoveryEndpointKey → Bool)
    (sourceDone : done ⟨connection.key, .source⟩ =
      (Chan.RecoveryProtocol.nextSource protocol endpointRequest).flushed)
    (sinkDone : done ⟨connection.key, .sink⟩ =
      (Chan.RecoveryProtocol.nextSink protocol endpointRequest).flushed)
    (complete : system.recoveryComplete island true done = true) :
    let request : Chan.RecoveryProtocol.Coordinated.Request connection.width :=
      { endpoint := endpointRequest, commit := true }
    (Chan.RecoveryProtocol.Coordinated.stepObserved connection.chan protocol
      request observed).event =
      system.recoveryChannelEvent systemEvent systemState connection := by
  dsimp only
  have ideal := coordinatedProtocol_event_eq_systemRecovery system island
    connection member incident systemEvent systemState reset protocol
    endpointRequest pending done sourceDone sinkDone complete
  have affected : systemEvent.affects connection = true := by
    simp only [Bool.or_eq_true, beq_iff_eq] at incident
    rcases incident with sourceEq | sinkEq
    · simp [System.RecoveryEvent.affects, sourceEq, reset]
    · simp [System.RecoveryEvent.affects, sinkEq, reset]
  have systemFlush :
      system.recoveryChannelEvent systemEvent systemState connection = .flush := by
    simp [System.recoveryChannelEvent, affected]
  have idealFlush :
      (Chan.RecoveryProtocol.Coordinated.step connection.chan protocol
        { endpoint := endpointRequest, commit := true }).event = .flush :=
    ideal.trans systemFlush
  have committed :=
    (Chan.RecoveryProtocol.Coordinated.step_event_eq_flush_iff
      connection.chan protocol
      { endpoint := endpointRequest, commit := true }).mp idealFlush
  have observedFlush :=
    (Chan.RecoveryProtocol.Coordinated.stepObserved_event_eq_flush_iff
      connection.chan protocol
      { endpoint := endpointRequest, commit := true } observed).2 committed
  exact observedFlush.trans systemFlush.symm

/-- End-to-end channel-state join at the globally coordinated recovery point
for an actual stock recovery binding.  This discharges the former free
`eventEq` premise from the binding theorem using the exact incident-endpoint
domain of the generated coordinator. -/
theorem recoveryPortable_globalCommit_refines_advanceRecovery
    {system : System} {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified)
    (binding : CertifiedRecoveryPortableBinding)
    (bindingMember : CertifiedChannelBinding.recoveryPortable binding ∈
      artifact.bindings)
    (island : SystemIsland)
    (connectionMember : binding.connection ∈ system.connections)
    (incident : (binding.connection.source == island.name ||
      binding.connection.sink == island.name) = true)
    (found : system.connections.find? (fun candidate =>
      candidate.chan.name == binding.connection.chan.name) =
        some binding.connection)
    (systemEvent : System.RecoveryEvent) (external : String → InEnv)
    (systemState : system.State) (reset : systemEvent.resets island.name = true)
    (queue : Chan.State binding.connection.width)
    (queueEq : queue = system.channelState systemState binding.connection)
    (protocol : Chan.RecoveryProtocol.State binding.connection.width)
    (represented : Chan.RecoveryProtocol.Rep queue protocol)
    (endpointRequest : Chan.RecoveryProtocol.Request binding.connection.width)
    (observed : Chan.Event binding.connection.width)
    (pending : protocol.recovering = true)
    (done : RecoveryEndpointKey → Bool)
    (sourceDone : done ⟨binding.connection.key, .source⟩ =
      (Chan.RecoveryProtocol.nextSource protocol endpointRequest).flushed)
    (sinkDone : done ⟨binding.connection.key, .sink⟩ =
      (Chan.RecoveryProtocol.nextSink protocol endpointRequest).flushed)
    (complete : system.recoveryComplete island true done = true) :
    let request : Chan.RecoveryProtocol.Coordinated.Request
        binding.connection.width :=
      { endpoint := endpointRequest, commit := true }
    let next := Chan.RecoveryProtocol.Coordinated.stepObserved
      binding.connection.chan protocol request observed
    (Chan.RecoveryProtocol.Rep
          (system.channelState
            (system.advanceRecovery systemEvent external systemState)
            binding.connection)
          next.state ∧
        (binding.connection.chan.recoveryStep queue next.event).accepted =
          next.accepted ∧
        (binding.connection.chan.recoveryStep queue next.event).delivered =
          next.delivered) ∧
      CertifiedChannelBinding.recoveryPortable binding ∈ artifact.bindings := by
  dsimp only
  let request : Chan.RecoveryProtocol.Coordinated.Request
      binding.connection.width :=
    { endpoint := endpointRequest, commit := true }
  have eventEq := coordinatedObserved_event_eq_systemRecovery system island
    binding.connection connectionMember incident systemEvent systemState reset
    protocol endpointRequest observed pending done sourceDone sinkDone complete
  subst queue
  have refined := Chan.RecoveryProtocol.Coordinated.stepObserved_refines
    binding.connection.chan protocol request observed
  have systemQueueEq := system.channelState_advanceRecovery_eq_recoveryStep
    systemEvent external systemState binding.connection found
  rw [← represented] at refined
  simp only [request] at refined
  rw [eventEq] at refined
  rw [systemQueueEq, eventEq]
  exact ⟨refined, bindingMember⟩

end CertifiedRealizedSystem
end Loom.Hw.System
