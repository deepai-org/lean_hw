-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.TraceContract
import Machines.Substrate.TwoClock
import Machines.Multiclock.RecoverySmoke
import Evidence.Constraints.Mock
import Evidence.Constraints.OpenXc7
import Evidence.Targets.AsyncQueueStorage

/-! Regression tests for the deliberately small ordinary-user multiclock API. -/

namespace Tests.MulticlockApi

open Loom.Hw
open Machines.Substrate.TwoClock
open Loom.Evidence.Targets.AsyncQueueStorage

example : system.resetPolicy = .coordinated := rfl

example : system.stockCheck = true := by decide
example : system.realizePortableChecked.isOk := by native_decide

/-- The application-level channel declaration generated both endpoint
adapters; no `withSource`/`withSink` assembly appears in the example. -/
example : builder.check.isOk := by decide

example : application.readReg final consumerIsland got = 42 := by decide

example : application.readChannel final queue = [] := by decide

example : queueSource.send (.lit 7) = queue.enq (.lit 7) := rfl
example : queueSink.data = queue.deq := rfl

/-! Endpoint actions are single-intent per tick. Two independent sends could
both observe pre-cycle readiness and last-write-wins would otherwise discard
the first payload, so checked assembly rejects that shape. -/

def doubleQueue : Chan 8 := { name := "double_send", depth := 2 }
def doubleSource := doubleQueue.source
def doubleProducer : Design where
  name := "double_producer"
  regs := []
  mems := []
  outputs := []
  rules := [
    ⟨"first", doubleSource.send (.lit 1)⟩,
    ⟨"second", doubleSource.send (.lit 2)⟩]
def doubleConsumer : Design where
  name := "double_consumer"
  regs := []
  mems := []
  outputs := []
  rules := []
def doubleProducerIsland : IslandHandle := .named "double_producer" doubleProducer clkA
def doubleConsumerIsland : IslandHandle := .named "double_consumer" doubleConsumer clkB
def doubleRoute := doubleQueue.between doubleProducerIsland doubleConsumerIsland
def doubleBuilder : SystemBuilder :=
  System.empty
    |>.addIsland doubleProducerIsland
    |>.addIsland doubleConsumerIsland
    |>.addChannel doubleRoute

def doubleRejected : Bool := match doubleBuilder.check with
    | .error _ => true
    | .ok _ => false

example : doubleRejected = true := by native_decide

example : (Act.ite (.reg 1 "choose")
    (doubleSource.send (.lit 1))
    (doubleSource.send (.lit 2))).maxWritesTo doubleQueue.sourceValidName 1 = 1 := by
  native_decide

def packedQueue : PackedChan (BitVec 8) := .named "packed" 2
def packedSource := packedQueue.source
def packedSink := packedQueue.sink

example : packedSource.send (.ofValue 7#8) = packedQueue.enq (.ofValue 7#8) := rfl
example : packedSink.data = packedQueue.deq := rfl

def deeperQueue : Chan 8 := ⟨"deeper", 4, .exchange⟩
def deeperSource := deeperQueue.source
def deeperSink := deeperQueue.sink

def deeperProducer : Design where
  name := "deeper_producer"
  regs := []
  mems := []
  outputs := []
  rules := [⟨"send", .ite deeperSource.canSend
    (deeperSource.send (.lit 9)) .skip⟩]

def deeperConsumer : Design where
  name := "deeper_consumer"
  regs := []
  mems := []
  outputs := []
  rules := [⟨"receive", .ite deeperSink.hasData deeperSink.consume .skip⟩]

def deeperProducerIsland : IslandHandle := .named "producer" deeperProducer clkA
def deeperConsumerIsland : IslandHandle := .named "consumer" deeperConsumer clkB
def deeperRoute : ChannelRoute 8 :=
  deeperQueue.between deeperProducerIsland deeperConsumerIsland
def deeperBuilder : SystemBuilder :=
  System.empty
    |>.addIsland deeperProducerIsland
    |>.addIsland deeperConsumerIsland
    |>.addChannel deeperRoute
    |>.withClockRel .asynchronous
def deeperSystem : System := deeperBuilder.certify (by decide)

example : deeperSystem.stockCheck = true := by native_decide
example : deeperSystem.realizePortableChecked.isOk := by native_decide

/-! The higher-throughput endpoint is explicit and destination-local.  It
uses the same abstract channel and portable CDC controller, while its timing
contract and executable behavior expose one-item-per-destination-tick steady
state service. -/

def fullRateQueue : Chan 8 := ⟨"full_rate", 4, .exchange⟩

def fullRateProducer : Design where
  name := "full_rate_producer"
  regs := []
  mems := []
  outputs := []
  rules := []

def fullRateConsumerCore : Design where
  name := "full_rate_consumer"
  regs := [⟨"observed", 8, 0⟩]
  mems := []
  outputs := ["observed"]
  rules := [⟨"consume", .ite fullRateQueue.fullRateHasData
    (.seq (.write 8 "observed" fullRateQueue.fullRateData)
      fullRateQueue.fullRateConsume) .skip⟩]

def fullRateProducerIsland : IslandHandle :=
  .named "full_rate_producer" fullRateProducer clkA
def fullRateConsumerIsland : IslandHandle :=
  .named "full_rate_consumer" fullRateConsumerCore clkB
def fullRateRoute := fullRateQueue.between fullRateProducerIsland fullRateConsumerIsland
def fullRateBuilder : SystemBuilder :=
  System.empty
    |>.addIsland fullRateProducerIsland
    |>.addIsland fullRateConsumerIsland
    |>.addFullRateChannel fullRateRoute
    |>.withClockRel .asynchronous
def fullRateSystem : System := fullRateBuilder.certify (by native_decide)

example : fullRateSystem.stockCheck = true := by native_decide
example : fullRateSystem.realizePortableChecked.isOk := by native_decide

def fullRateApplication : System.Application fullRateSystem :=
  fullRateSystem.realizePortable (by native_decide)

example : fullRateApplication.timingFor fullRateRoute =
    some (System.timingForSinkPresentation true
      System.compiledPortableTiming) := by native_decide
example : (fullRateApplication.timingFor fullRateRoute).map
    (fun timing => timing.sinkIssueInterval) =
      some (.conditional 1 .sinkTicks
        [.sinkPayloadAvailableEveryTick, .sinkConsumesWhenAvailable]) := by
  native_decide

def fullRateSinkDesign : Design :=
  fullRateQueue.withFullRateSink fullRateConsumerCore

/-- Reserved buffer coordinates without the generated maintenance rule do not
inherit the full-rate timing contract through expert assembly. -/
def malformedFullRateSinkDesign : Design :=
  { fullRateSinkDesign with rules := fullRateConsumerCore.rules }

example : !fullRateQueue.hasFullRateSinkShape malformedFullRateSinkDesign := by
  native_decide

def malformedFullRateBuilder : SystemBuilder :=
  System.empty
    |>.island "full_rate_producer"
      (fullRateQueue.withSource fullRateProducer) clkA.name
    |>.island "full_rate_consumer" malformedFullRateSinkDesign clkB.name
    |>.connect fullRateQueue "full_rate_producer" "full_rate_consumer"

private def malformedFullRateRejected : Bool :=
  match malformedFullRateBuilder.check with
    | .error _ => true
    | .ok _ => false

example : malformedFullRateRejected := by native_decide

/-- A forged maintenance-rule name with a different body is not a full-rate
endpoint and cannot authorize the one-tick timing contract. -/
def wrongBodyFullRateSinkDesign : Design :=
  { fullRateSinkDesign with
    rules := ⟨fullRateQueue.stem ++ "full_rate_sink_maintenance", .skip⟩ ::
      fullRateConsumerCore.rules }

example : !fullRateQueue.hasFullRateSinkShape wrongBodyFullRateSinkDesign := by
  native_decide

def wrongBodyFullRateBuilder : SystemBuilder :=
  System.empty
    |>.island "full_rate_producer"
      (fullRateQueue.withSource fullRateProducer) clkA.name
    |>.island "full_rate_consumer" wrongBodyFullRateSinkDesign clkB.name
    |>.connect fullRateQueue "full_rate_producer" "full_rate_consumer"

private def wrongBodyFullRateRejected : Bool :=
  match wrongBodyFullRateBuilder.check with
  | .error _ => true
  | .ok _ => false

example : wrongBodyFullRateRejected := by native_decide

def fullRateSteadyState : St :=
  { fullRateSinkDesign.reset with
    regs := (((fullRateSinkDesign.reset.regs.set
      fullRateQueue.sinkBufferCountName 1#2).set
      fullRateQueue.sinkBufferHeadName 7#8).set
      fullRateQueue.sinkPopName 1#1) }

def fullRateIncomingEight : InEnv := fun name width =>
  if name = fullRateQueue.sinkValidName then
    if h : width = 1 then h ▸ 1#1 else 0
  else if name = fullRateQueue.sinkPayloadName then
    if h : width = 8 then h ▸ 8#8 else 0
  else 0

def fullRateSteadyNext : St :=
  fullRateSinkDesign.cycleOpen fullRateIncomingEight fullRateSteadyState

example : fullRateSteadyNext.regs "observed" 8 = 7#8 := by native_decide
example : fullRateSteadyNext.regs fullRateQueue.sinkBufferCountName 2 = 1#2 := by
  native_decide
example : fullRateSteadyNext.regs fullRateQueue.sinkBufferHeadName 8 = 8#8 := by
  native_decide
example : fullRateSteadyNext.regs fullRateQueue.sinkPopName 1 = 1#1 := by
  native_decide

def deeperApplication : System.Application deeperSystem :=
  deeperSystem.realizePortable (by native_decide)

def deeperStorageShape : Cdc.AsyncQueueStorage.Portable.Shape where
  width := 8
  depth := 4
  positive := by decide

example : (Cdc.AsyncQueueStorage.Portable.readerDesign deeperStorageShape).regs = [] := rfl
example : (Cdc.AsyncQueueStorage.Portable.readerDesign deeperStorageShape).rules = [] := rfl
example : System.compiledPortableTiming.storageReadStages = 0 := rfl

/-- General depth is covered by the same certified artifact and emission
gate, not merely accepted by the application-side readiness predicate. -/
example : deeperApplication.artifact.bindings.length = 1 := by native_decide
example : deeperApplication.artifact.emissionCheck.isOk := by native_decide
example : !deeperApplication.artifact.renderedVerilog.contains "read_valid" := by
  native_decide
example : deeperApplication.artifact.realized.artifacts.instances.length = 1 := by
  native_decide

/-! The physical artifact says exactly what the emitted synchronous-reset
ports require, once per distinct clock domain. It deliberately does not
pretend to describe or validate a physical reset tree. -/
example : deeperApplication.artifact.realized.artifacts.resetIntents.map
    (fun intent => intent.clock) = [clkA.name, clkB.name] := by
  native_decide
example : deeperApplication.artifact.realized.artifacts.resetIntents.all
    (fun intent => intent.requiresClockWhileAsserted &&
      intent.assertion == .synchronous &&
      intent.release == .sampledIndependently) = true := by
  native_decide
example : deeperApplication.artifact.realized.emissionArtifacts.any
    (fun artifact => artifact.kind == .constraints && artifact.text.contains
      "This clock must tick while reset is asserted.") := by
  native_decide

/-- Expert bindings must describe timing explicitly; omission survives pure
structural construction only long enough to produce an actionable emission
failure rather than silently meaning zero cycles. -/
def untimedDeeperBinding : System.BoundImplementation :=
  System.BoundImplementation.custom deeperRoute.toSystemConnection
    "test.untimed" .different
    (Cdc.AsyncFifo.refinement deeperQueue (by decide))
    (fun _ => "test_untimed")
    (fun _ => "module test_untimed; endmodule")
    (fun _ => [.asynchronousClocks clkA.name clkB.name])

def untimedDeeperRealized : System.RealizedSystem :=
  System.realizeChecked deeperSystem [untimedDeeperBinding]
    (by native_decide) (by native_decide)

example : untimedDeeperBinding.timing.isSpecified = false := rfl
example : untimedDeeperRealized.emissionCheck.isOk = false := by native_decide

/-! One application may choose different closed realizations per typed route.
The same-clock FIFO deliberately uses depth three, which the synchronous
reference supports even though the portable Gray realization is restricted
to power-of-two depths. -/

def syncQueue : Chan 8 := ⟨"sync_depth_three", 3, .exchange⟩
def syncSource := syncQueue.source
def syncSink := syncQueue.sink

def syncProducer : Design where
  name := "sync_producer"
  regs := []
  mems := []
  outputs := []
  rules := [⟨"send", .ite syncSource.canSend
    (syncSource.send (.lit 11)) .skip⟩]

def syncConsumer : Design where
  name := "sync_consumer"
  regs := []
  mems := []
  outputs := []
  rules := [⟨"receive", .ite syncSink.hasData syncSink.consume .skip⟩]

def syncProducerIsland : IslandHandle := .named "sync_source" syncProducer clkA
def syncConsumerIsland : IslandHandle := .named "sync_sink" syncConsumer clkA
def syncRoute : ChannelRoute 8 :=
  syncQueue.between syncProducerIsland syncConsumerIsland

def mixedBuilder : SystemBuilder :=
  System.empty
    |>.addIsland deeperProducerIsland
    |>.addIsland deeperConsumerIsland
    |>.addIsland syncProducerIsland
    |>.addIsland syncConsumerIsland
    |>.addChannel deeperRoute
    |>.addChannel syncRoute
    |>.withClockRel .asynchronous

def mixedSystem : System := mixedBuilder.certify (by decide)
def mixedPlan : RealizationPlan :=
  RealizationPlan.portable.useSynchronous syncRoute

example : mixedPlan.select deeperRoute.key = .portableAsync := by native_decide
example : mixedPlan.select syncRoute.key = .synchronous := by native_decide
example : mixedSystem.selectedCheck mixedPlan = true := by native_decide
example : (mixedSystem.realizeWithChecked mixedPlan).isOk := by native_decide

def mixedApplication : System.Application mixedSystem :=
  mixedSystem.realizeWith mixedPlan (by native_decide)

def mixedIslandCache : System.CertifiedIslands mixedSystem :=
  mixedSystem.certifyIslands (by native_decide)

def mixedCachedApplication : System.Application mixedSystem :=
  mixedSystem.realizeWithCertified mixedIslandCache mixedPlan (by native_decide)

example : mixedApplication.artifact.realized.bindings.map (·.name) =
    ["loom.compiled.portable_fifo", "loom.compiled.sync_fifo"] := by
  native_decide
example : mixedApplication.artifact.emissionCheck.isOk := by native_decide
example : mixedCachedApplication.artifact.renderedUTF8 =
    mixedApplication.artifact.renderedUTF8 := by native_decide

/-! Timing is derived from the selected realization rather than guessed from
the abstract channel. Structural synchronizer stages are visible even when
the proved model supplies no finite service bound. -/

example : mixedApplication.timingFor deeperRoute =
    some System.compiledPortableTiming := by native_decide

example : mixedApplication.timingFor syncRoute =
    some System.compiledSyncTiming := by native_decide

example : mixedApplication.timingGroups.map (fun group => group.key) =
    mixedSystem.connections.map SystemConnection.key :=
  mixedApplication.timingKeys_complete

example : mixedApplication.timingReport.contains
    "channel deeper (loom.compiled.portable_fifo)" := by
  native_decide

example : mixedApplication.timingReport.contains
    "synchronizer stages: forward 2, reverse 2" := by
  native_decide

/-- The portable realization carries complete neutral physical intent, not
only an asynchronous clock-group declaration: two exact synchronizer chains
and two exact period-relative Gray-bus constraints accompany the clock pair. -/
example : mixedApplication.artifact.realized.artifacts.constraintFile.groups.head?.map
    (fun group => group.constraints.length) = some 5 := by native_decide

example : mixedApplication.artifact.emissionArtifacts.any (fun artifact =>
    artifact.relativePath.toString = "clock_constraints.md" &&
      artifact.text.contains "ordered synchronizer chain" &&
      artifact.text.contains "maximum bus skew") := by
  native_decide

def skippedPhysicalReport : System.PhysicalCheckReport
    mixedApplication.artifact.realized.artifacts where
  backend := "test backend without physical checks"
  results := mixedApplication.artifact.realized.artifacts.requirements.map
    fun requirement =>
      { requirement, status := .skip, detail := "tool unavailable" }
  coverage := by simp [Function.comp_def]

example : skippedPhysicalReport.results.length = 7 := by native_decide
example : skippedPhysicalReport.passed = false := by native_decide
example : skippedPhysicalReport.render.contains "SKIP" := by native_decide

def referencePhysicalReport := Loom.Evidence.Constraints.Mock.check
  mixedApplication.artifact.realized.artifacts

/-- The reference adapter proves the extension contract is usable: it must
consume the full timing-plus-reset list exactly once before it can report
success. This is an interface test, not target signoff evidence. -/
example : referencePhysicalReport.requirementsHandled = true := by native_decide
example : referencePhysicalReport.passed = false := by native_decide

def identifiedRun : System.PhysicalBackendRun where
  scope := .targetImplementation
  adapter := "test.real.adapter"
  target := "test-device"
  tool := "test-route"
  version := "1.0"
  runId := "run-17"
  seed := some 17

def identifiedArtifacts : System.PhysicalArtifactIdentity where
  rtlSha256 := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
  intentSha256 := "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
  constraintsSha256 := some
    "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
  implementationRtlSha256 := some
    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
  implementationConstraintsSha256 := some
    "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
  routedSha256 := some
    "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"

def identifiedPhysicalReport : System.PhysicalCheckReport
    mixedApplication.artifact.realized.artifacts where
  backend := "identified test target"
  run := identifiedRun
  artifactIdentity := identifiedArtifacts
  results := mixedApplication.artifact.realized.artifacts.requirements.map
    fun requirement =>
      { requirement, status := .pass, run := identifiedRun,
        artifacts := identifiedArtifacts,
        resolutions := requirement.objects.map fun logical =>
          { logical, resolved := "post-synthesis/" ++ logical.render } }
  coverage := by simp [Function.comp_def]

example : identifiedPhysicalReport.passed = true := by native_decide

example : !({ identifiedArtifacts with
    implementationRtlSha256 := some
      "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc" } :
    System.PhysicalArtifactIdentity).complete := by native_decide

/-- A target label and PASS rows cannot substitute for an exact routed
implementation identity. -/
def unroutedPhysicalReport : System.PhysicalCheckReport
    mixedApplication.artifact.realized.artifacts where
  backend := "identified test target without routed identity"
  run := identifiedRun
  artifactIdentity := { identifiedArtifacts with routedSha256 := none }
  results := mixedApplication.artifact.realized.artifacts.requirements.map
    fun requirement =>
      { requirement, status := .pass, run := identifiedRun,
        artifacts := { identifiedArtifacts with routedSha256 := none },
        resolutions := requirement.objects.map fun logical =>
          { logical, resolved := "post-synthesis/" ++ logical.render } }
  coverage := by simp [Function.comp_def]

example : unroutedPhysicalReport.passed = false := by native_decide

/-- PASS labels cannot bless evidence for different input bytes. -/
def staleIdentityPhysicalReport : System.PhysicalCheckReport
    mixedApplication.artifact.realized.artifacts where
  backend := "identified test target with stale observations"
  run := identifiedRun
  artifactIdentity := identifiedArtifacts
  results := mixedApplication.artifact.realized.artifacts.requirements.map
    fun requirement =>
      { requirement, status := .pass, run := identifiedRun,
        artifacts := { identifiedArtifacts with
          rtlSha256 := "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc" },
        resolutions := requirement.objects.map fun logical =>
          { logical, resolved := "post-synthesis/" ++ logical.render } }
  coverage := by simp [Function.comp_def]

example : staleIdentityPhysicalReport.passed = false := by native_decide

def openXc7Observation : Loom.Evidence.Constraints.OpenXc7.Observation where
  run := { identifiedRun with
    adapter := "loom.openxc7"
    tool := "nextpnr-xilinx"
    version := "0.8.2" }
  artifacts := identifiedArtifacts
  theoremBoundRtlMatched := true
  intentManifestMatched := true
  resolutions := mixedApplication.artifact.realized.artifacts.requirements.flatMap
    fun requirement => requirement.objects.map fun logical =>
      { logical, resolved := "routed/" ++ logical.render }
  routedSynchronizerAuditPassed := true
  resetContractReviewed := true

def openXc7PhysicalReport := Loom.Evidence.Constraints.OpenXc7.check
  mixedApplication.artifact.realized.artifacts openXc7Observation

/-- The real target adapter credits its routed structural and reset evidence,
but cannot mislabel openXC7's unsupported clock-group and Gray-bus timing
requirements as signoff. -/
example : openXc7PhysicalReport.results.countP
    (fun result => result.status == .pass) = 4 := by native_decide
example : openXc7PhysicalReport.results.countP
    (fun result => result.status == .unconstrained) = 3 := by native_decide
example : openXc7PhysicalReport.passed = false := by native_decide
example : referencePhysicalReport.results.length =
    mixedApplication.artifact.realized.artifacts.requirements.length := by
  native_decide
example : (Loom.Evidence.Constraints.Mock.render
    mixedApplication.artifact.realized.artifacts).contains "reset clkA" := by
  native_decide

def mockStorageParameters : Cdc.AsyncQueueStorage.Parameters where
  width := 8
  depth := 4
  readLatency := 1
  depthPositive := by decide
  readLatencyPositive := by decide

private def openXc7Width32Parameters : Cdc.AsyncQueueStorage.Parameters where
  width := 32
  depth := 4
  readLatency := 1
  depthPositive := by decide
  readLatencyPositive := by decide

private def openXc7Width46Parameters : Cdc.AsyncQueueStorage.Parameters where
  width := 46
  depth := 4
  readLatency := 1
  depthPositive := by decide
  readLatencyPositive := by decide

private def openXc7Width46Error : String :=
  match openXc7Zynq7000IndependentClockPolicy.check
      (openXc7Zynq7000Key openXc7Width46Parameters) with
  | .ok _ => ""
  | .error message => message

private def openXc7AcceptsWidth32 : Bool :=
  match openXc7Zynq7000IndependentClockPolicy.check
      (openXc7Zynq7000Key openXc7Width32Parameters) with
  | .ok _ => true
  | .error _ => false

private def openXc7RejectsWidth46 : Bool :=
  match openXc7Zynq7000IndependentClockPolicy.check
      (openXc7Zynq7000Key openXc7Width46Parameters) with
  | .ok _ => false
  | .error _ => true

example : openXc7AcceptsWidth32 := by native_decide
example : openXc7RejectsWidth46 := by native_decide
example : openXc7Width46Error.contains "width 46" := by native_decide

private def changedToolVersionKey : StorageQualificationKey :=
  { openXc7Zynq7000Key openXc7Width32Parameters with
    tool := { openXc7Tool with version := "0.8.3" } }

private def wrongPresentationKey : StorageQualificationKey :=
  { openXc7Zynq7000Key openXc7Width32Parameters with
    presentation := .firstWordFallThrough }

example : !openXc7Zynq7000IndependentClockPolicy.accepts changedToolVersionKey := by
  native_decide
example : !openXc7Zynq7000IndependentClockPolicy.accepts wrongPresentationKey := by
  native_decide
example : openXc7Zynq7000IndependentClockPolicy.evidence.all
    (fun evidence => evidence.key.tool == openXc7Tool) := by native_decide

example : openXc7Zynq7000IndependentClockPolicy.evidence.map (·.stage) =
      [.rtlSimulation, .primitiveInference, .routedImplementation,
        .siliconExecution, .siliconExecution, .siliconExecution] := by
  native_decide

private def checkedOpenXc7Binding :=
  openXc7Zynq7000InferredBinding openXc7Width32Parameters (by native_decide)

example : checkedOpenXc7Binding.externalAssumption.isSome := by native_decide

def mockStorageLeaf :=
  Loom.Evidence.Targets.AsyncQueueStorage.mockLeaf mockStorageParameters

/-- The target-refinement seam is exercised without choosing an FPGA family
or ASIC library: selection changes the leaf RTL, retains one explicit external
assumption, and serializes the very configuration whose equality is carried
by `Binding`. -/
example : mockStorageLeaf.moduleText.contains
    "MOCK_TARGET_STORAGE width=8 depth=4" := by native_decide
example : mockStorageLeaf.binding.externalAssumption.isSome := by native_decide
example : mockStorageLeaf.binding.configuration.readLatency =
    mockStorageParameters.readLatency := mockStorageLeaf.binding.agreesReadLatency

def mockSubstitutedRtl : String :=
  match deeperApplication.artifact.bindings with
  | [.portable binding] =>
      let shape := System.CertifiedPortable.storageShape binding.connection
        binding.depthAtLeastTwo
      let leaf := Loom.Evidence.Targets.AsyncQueueStorage.mockLeaf shape.parameters
      let physical := binding.toPhysicalWithStorageLeaf leaf (by rfl)
      physical.moduleText
        { channel := binding.connection.chan.name
          width := binding.connection.width
          depth := binding.connection.chan.depth
          policy := binding.connection.chan.policy
          source := binding.connection.source
          sourceClock := some clkA.name
          sink := binding.connection.sink
          sinkClock := some clkB.name }
  | _ => ""

example : mockSubstitutedRtl.contains "MOCK_TARGET_STORAGE" := by native_decide
example : mockSubstitutedRtl.contains "u_target_storage" := by native_decide
example : !mockSubstitutedRtl.contains "u_storage_writer" := by native_decide

def mockSubstitutedAssumptions : List String :=
  match deeperApplication.artifact.bindings with
  | [.portable binding] =>
      let shape := System.CertifiedPortable.storageShape binding.connection
        binding.depthAtLeastTwo
      let leaf := Loom.Evidence.Targets.AsyncQueueStorage.mockLeaf shape.parameters
      (binding.toPhysicalWithStorageLeaf leaf (by rfl)).externalAssumptions
  | _ => []

example : mockSubstitutedAssumptions =
    ["mock dual-clock memory satisfies the selected AsyncQueueStorage contract"] := by
  native_decide

example : mixedApplication.artifact.emissionArtifacts.map
    (fun artifact => artifact.relativePath.toString) =
    ["system.v", "clock_constraints.md", "crossings.md"] := by
  native_decide

/-- Normal users receive readable reports, not spreadsheet interchange files.
Typed `PhysicalArtifacts` values remain available to tools and expert code. -/
example : mixedApplication.artifact.emissionArtifacts.all (fun artifact =>
    !artifact.relativePath.toString.endsWith ".tsv" &&
      !artifact.relativePath.toString.endsWith ".csv") := by
  native_decide

/-! Checked hierarchical blocks retain open typed endpoints until their
parent closes them. -/

def sourceExport : ExportedSource syncQueue :=
  syncQueue.exportSource syncProducerIsland
def sinkExport : ExportedSink syncQueue :=
  syncQueue.exportSink syncConsumerIsland

def sourceBlockBuilder : SystemBuilder :=
  System.empty
    |>.addIsland syncProducerIsland
    |>.exportSource sourceExport
def sourceBlockSystem : System := sourceBlockBuilder.certify (by native_decide)

def sinkBlockBuilder : SystemBuilder :=
  System.empty
    |>.addIsland syncConsumerIsland
    |>.exportSink sinkExport
def sinkBlockSystem : System := sinkBlockBuilder.certify (by native_decide)

structure SourceBlockInterface (system : System) where
  output : DeclaredSource system syncQueue

structure SinkBlockInterface (system : System) where
  input : DeclaredSink system syncQueue

def sourceInterface : SourceBlockInterface sourceBlockSystem :=
  ⟨⟨sourceExport, by native_decide⟩⟩
def sinkInterface : SinkBlockInterface sinkBlockSystem :=
  ⟨⟨sinkExport, by native_decide⟩⟩

def sourceBlock : System.SealedBlock SourceBlockInterface (fun _ _ => Unit) where
  system := sourceBlockSystem
  islands := sourceBlockSystem.certifyIslands (by native_decide)
  interface := sourceInterface
  theorems := ()

def sinkBlock : System.SealedBlock SinkBlockInterface (fun _ _ => Unit) where
  system := sinkBlockSystem
  islands := sinkBlockSystem.certifyIslands (by native_decide)
  interface := sinkInterface
  theorems := ()

def hierarchicalBuilder : SystemBuilder :=
  System.empty
    |>.includeBlock sourceBlock
    |>.includeBlock sinkBlock
    |>.connectDeclaredExports sourceBlock.interface.output sinkBlock.interface.input
    |>.withClockRel .asynchronous

def hierarchicalSystem : System := hierarchicalBuilder.certify (by native_decide)
def hierarchicalRoute : ChannelRoute 8 :=
  syncQueue.between syncProducerIsland syncConsumerIsland
def hierarchicalPlan : RealizationPlan :=
  RealizationPlan.portable.useSynchronous hierarchicalRoute

example : hierarchicalSystem.openSources = [] := by native_decide
example : hierarchicalSystem.openSinks = [] := by native_decide
example : hierarchicalSystem.connections.length = 1 := by native_decide
example : hierarchicalSystem.selectedCheck hierarchicalPlan = true := by native_decide
example : (hierarchicalSystem.realizeWithChecked hierarchicalPlan).isOk := by
  native_decide

/-- Flattening cannot silently reinterpret a child's reset contract. -/
def mismatchedResetHierarchy : SystemBuilder :=
  System.empty
    |>.includeBlock sourceBlock
    |>.withIndependentReset

example : mismatchedResetHierarchy.check.isOk = false := by native_decide

/-- A cross-clock route cannot accidentally select the synchronous circuit. -/
def invalidClockPlan : RealizationPlan :=
  RealizationPlan.portable.useSynchronous deeperRoute

example : mixedSystem.selectedCheck invalidClockPlan = false := by native_decide
example : (mixedSystem.realizeWithChecked invalidClockPlan).isOk = false := by
  native_decide
example : (mixedSystem.selectedReadinessReport invalidClockPlan).contains
    "synchronous realization requires one clock" := by native_decide

def recoveryBuilder : SystemBuilder := mixedBuilder.withIndependentReset
def recoverySystem : System := recoveryBuilder.certify (by decide)

def loadedRecoveryState : recoverySystem.State :=
  { recoverySystem.reset with
    channel := fun name =>
      if name = deeperQueue.name then ⟨8, [1#8, 2#8]⟩
      else if name = syncQueue.name then ⟨8, [3#8]⟩
      else recoverySystem.reset.channel name }

def resetAsyncSource : System.RecoveryEvent where
  tick := ⟨[]⟩
  resetIslands := [deeperProducerIsland.name]

example : recoverySystem.recoveryEventOk resetAsyncSource = true := by native_decide
example : mixedSystem.recoveryEventOk resetAsyncSource = false := by native_decide

/-- Resetting either endpoint explicitly discards that channel's old epoch,
while a nonincident channel is untouched. -/
example : recoverySystem.channelState
    (recoverySystem.applyRecovery resetAsyncSource loadedRecoveryState)
    deeperRoute.toSystemConnection = [] := by native_decide
example : recoverySystem.channelState
    (recoverySystem.applyRecovery resetAsyncSource loadedRecoveryState)
    syncRoute.toSystemConnection = [3#8] := by native_decide
example : ((recoverySystem.applyRecovery resetAsyncSource loadedRecoveryState).island
    deeperProducerIsland.name).regs deeperQueue.sourceValidName 1 = 0 := by
  native_decide

example : (recoverySystem.runRecoveryPrefixChecked #[resetAsyncSource]).isOk := by
  native_decide

/-! The channel-level proof boundary now records recovery completion as a
loss-explicit epoch change. Existing certified implementations embed without
new proof work; `atomicFlush` is the specification witness, not emitted RTL. -/

def syncRecoverySpec : Chan.RecoveryRefinement syncQueue :=
  Chan.RecoveryRefinement.atomicFlush
    (syncQueue.syncRefinement (by decide))

def syncRecoveryRequests : List syncRecoverySpec.Request :=
  [some { push := some 7#8, pop := false }, none]

def syncRecoveryAbstract : Chan.RecoveryRefinement.AbstractTraceResult 8 :=
  Chan.RecoveryRefinement.runAbstract syncQueue []
    (syncRecoverySpec.observedEvents syncRecoverySpec.reset syncRecoveryRequests)

example : syncRecoveryAbstract.state = [] := by native_decide
example : syncRecoveryAbstract.accepted = [7#8] := by native_decide
example : syncRecoveryAbstract.delivered = [] := by native_decide
example : syncRecoveryAbstract.discarded = [[7#8]] := by native_decide

example := syncRecoverySpec.equivalent syncRecoveryRequests

def protocolRecoverySpec : Chan.RecoveryRefinement syncQueue :=
  Chan.RecoveryProtocol.refinement syncQueue

def protocolTick (recover : Bool := false) (push : Option (BitVec 8) := none) :
    Chan.RecoveryProtocol.Request 8 :=
  { sourceTick := true
    sinkTick := true
    sourceRecover := recover
    transfer := { push, pop := false } }

/-- The first word is accepted, a held-high graceful request is synchronized
and acknowledged, and exactly one completed recovery discards that old
epoch. Holding the request for several clocks does not manufacture repeated
epochs. -/
def protocolRecoveryRequests : List protocolRecoverySpec.Request :=
  [protocolTick false (some 7#8)] ++
    List.replicate 4 (protocolTick true) ++
    List.replicate 20 (protocolTick false)

def protocolRecoveryAbstract :
    Chan.RecoveryRefinement.AbstractTraceResult 8 :=
  Chan.RecoveryRefinement.runAbstract syncQueue []
    (protocolRecoverySpec.observedEvents protocolRecoverySpec.reset
      protocolRecoveryRequests)

def protocolRecoveryConcrete :=
  protocolRecoverySpec.runConcrete protocolRecoverySpec.reset
    protocolRecoveryRequests

example : protocolRecoveryAbstract.state = [] := by native_decide
example : protocolRecoveryAbstract.accepted = [7#8] := by native_decide
example : protocolRecoveryAbstract.discarded = [[7#8]] := by native_decide
example : protocolRecoveryConcrete.state.recovering = false := by native_decide
example : protocolRecoveryConcrete.state.source = {} := by native_decide
example : protocolRecoveryConcrete.state.sink = {} := by native_decide
example := protocolRecoverySpec.equivalent protocolRecoveryRequests

def sourceProtocolTick (recover : Bool := false) :
    Chan.RecoveryProtocol.Request 8 :=
  { sourceTick := true, sourceRecover := recover }

def sinkProtocolTick (recover : Bool := false) :
    Chan.RecoveryProtocol.Request 8 :=
  { sinkTick := true, sinkRecover := recover }

/-- A sink-initiated recovery also completes under a maximally alternating
clock schedule; no aligned edge is required by the protocol theorem. -/
def alternatingRecoveryRequests : List protocolRecoverySpec.Request :=
  [{ sourceTick := true, transfer := { push := some 9#8 } },
    sinkProtocolTick true] ++
    (List.range 24).map fun index =>
      if index % 2 = 0 then sourceProtocolTick else sinkProtocolTick

def alternatingRecoveryAbstract :
    Chan.RecoveryRefinement.AbstractTraceResult 8 :=
  Chan.RecoveryRefinement.runAbstract syncQueue []
    (protocolRecoverySpec.observedEvents protocolRecoverySpec.reset
      alternatingRecoveryRequests)

example : alternatingRecoveryAbstract.state = [] := by native_decide
example : alternatingRecoveryAbstract.discarded = [[9#8]] := by native_decide

example : Chan.RecoveryProtocol.Design.compilerReady = true := by native_decide
example : Chan.RecoveryProtocol.Design.endpoint.emitCheck.isOk := by native_decide
def recoveryEndpointCertificate :
    CertifiedDesign Chan.RecoveryProtocol.Design.endpoint :=
  Chan.RecoveryProtocol.Design.certify (by native_decide)
example := Chan.RecoveryProtocol.Design.view_reset
example := Chan.RecoveryProtocol.Design.view_cycle_any

example : recoverySystem.channelState
    (recoverySystem.advanceRecovery resetAsyncSource (fun _ _ _ => 0)
      loadedRecoveryState) deeperRoute.toSystemConnection =
      (deeperQueue.recoveryStep
        (recoverySystem.channelState loadedRecoveryState
          deeperRoute.toSystemConnection)
        (recoverySystem.recoveryChannelEvent resetAsyncSource loadedRecoveryState
          deeperRoute.toSystemConnection)).state := by
  apply recoverySystem.channelState_advanceRecovery_eq_recoveryStep
  rfl

/-- A mixed plan with ordinary channel leaves fails closed under independent
reset and identifies the missing recovery capability. -/
example : recoverySystem.selectedCheck mixedPlan = false := by native_decide
example : (recoverySystem.selectedReadinessReport mixedPlan).contains
    "independentFlush reset policy requires a recovery-capable realization" := by
  native_decide

/-! Expert-level physical leaf checkpoint. The ordinary application gate
stays closed until whole-island coordination is proved, but the complete
recovery-capable channel wrapper is already constructed solely from compiled
Design components and passes certified emission checks. -/

def recoveryDeeperBuilder : SystemBuilder :=
  deeperBuilder.withIndependentReset
def recoveryDeeperSystem : System :=
  recoveryDeeperBuilder.certify (by decide)
def recoveryDeeperConnection : SystemConnection :=
  deeperRoute.toSystemConnection

def recoveryPhysicalBinding : System.CertifiedRecoveryPortableBinding :=
  recoveryDeeperSystem.recoveryPortableBindingFromCheck
    recoveryDeeperConnection (by native_decide) (by native_decide)
      (by native_decide)

def recoveryDeeperIslands : System.CertifiedIslands recoveryDeeperSystem :=
  recoveryDeeperSystem.certifyIslands (by native_decide)

def recoveryDeeperCertified : CertifiedSystem recoveryDeeperSystem where
  islandCertificate := recoveryDeeperIslands.certificate
  channelCertificate := by
    intro connection member
    have equal : connection = recoveryDeeperConnection := by
      change connection ∈ [recoveryDeeperConnection] at member
      simpa using member
    subst connection
    exact recoveryPhysicalBinding.refinement

def recoveryDeeperArtifact :
    System.CertifiedRealizedSystem recoveryDeeperSystem
      recoveryDeeperCertified where
  bindings := [.recoveryPortable recoveryPhysicalBinding]
  coverage := rfl
  clockRules := by native_decide
  resetCompatibility := by native_decide

example : recoveryPhysicalBinding.recoveryRefinement.ConcreteState =
    Chan.RecoveryProtocol.State 8 := rfl
example : recoveryDeeperArtifact.emissionCheck.isOk := by native_decide
example : recoveryDeeperArtifact.renderedVerilog.contains
    "input wire producer__recover" := by native_decide
example : recoveryDeeperArtifact.renderedVerilog.contains
    "channel_recovery_endpoint" := by native_decide
example : recoveryDeeperArtifact.renderedVerilog.contains
    ".rst(source_fifo_reset)" := by native_decide

/-! The same artifact is available through the application facade. An author
selects the recovery-capable stock plan; endpoint certificates, datapath
certificates, storage witnesses, coverage, and coordinator wiring remain
library details. -/

def recoveryDeeperPlan : RealizationPlan := RealizationPlan.recoveryPortable

example : recoveryDeeperPlan.select recoveryDeeperConnection.key =
    .recoveryPortableAsync := by native_decide
example : recoveryDeeperSystem.selectedCheck recoveryDeeperPlan = true := by
  native_decide
example : (recoveryDeeperSystem.realizeWithChecked recoveryDeeperPlan).isOk := by
  native_decide

def recoveryDeeperApplication : System.Application recoveryDeeperSystem :=
  recoveryDeeperSystem.realizeWith recoveryDeeperPlan (by native_decide)

def recoveryApplicationEvent : System.RecoveryEvent where
  tick := deeperProducerIsland.clock.tick
  resetIslands := [deeperProducerIsland.name]

def recoveryApplicationState : recoveryDeeperApplication.State :=
  recoveryDeeperApplication.runRecovery #[recoveryApplicationEvent]

example : (recoveryDeeperApplication.runRecoveryChecked
    #[recoveryApplicationEvent]).isOk := by native_decide
example : recoveryApplicationState.semantic =
    recoveryDeeperSystem.runRecoveryPrefix #[recoveryApplicationEvent] :=
  recoveryDeeperApplication.runRecovery_semantic_eq
    #[recoveryApplicationEvent]

example : recoveryDeeperApplication.artifact.emissionCheck.isOk := by
  native_decide
example : recoveryDeeperApplication.artifact.renderedUTF8 =
    recoveryDeeperArtifact.renderedUTF8 := by native_decide
example : recoveryDeeperApplication.timingFor deeperRoute =
    some System.compiledRecoveryPortableTiming := by native_decide
example : recoveryDeeperApplication.timingReport.contains
    "recovery: schedule-dependent" := by native_decide
example : recoveryDeeperApplication.timingReport.contains
    "recovery_request_held" := by native_decide
example : recoveryDeeperApplication.artifact.renderedVerilog.contains
    "output wire producer__recovered" := by native_decide
example : recoveryDeeperApplication.artifact.renderedVerilog.contains
    "system_recovery_coordinator_cell" := by native_decide
example : recoveryDeeperApplication.artifact.renderedVerilog.contains
    ".rst(producer__recovery_reset)" := by native_decide
example : recoveryDeeperApplication.artifact.realized.artifacts.recoveryInterfaces.length =
    recoveryDeeperSystem.islands.length := by native_decide
example : (System.renderRecoveryInterfaces
    recoveryDeeperApplication.artifact.realized.artifacts.recoveryInterfaces).contains
      "not a one-cycle pulse and not a sticky host-readable status" := by
  native_decide
example : (System.renderRecoveryInterfaces
    recoveryDeeperApplication.artifact.realized.artifacts.recoveryInterfaces).contains
      "hold it until `producer__recovered` is high" := by
  native_decide

def recoveryDeeperAssemblyCertificate :=
  recoveryDeeperApplication.artifact.recoveryAssemblyCertificate (by rfl)

example := recoveryDeeperAssemblyCertificate.bindingRecovery

example (input : InEnv) (state : St) :
    Compile.forgetSt
        (Loom.Emit.MicroVerilog.Module.cycleOpenWithReset
          (Compile.compile Chan.RecoveryProtocol.Design.endpoint)
          true input (Compile.convSt state)) =
      Chan.RecoveryProtocol.Design.endpoint.reset := by
  simpa [Design.cycleOpenWithReset] using
    Compile.compile_cycleOpenWithReset
      Chan.RecoveryProtocol.Design.endpoint
      (Compile.designWFCheck_sound _ (by native_decide)) true input state

/-- The generic binding lemma joins directly to the exact queue projection
when supplied an event equality. The stock coordinator discharges that
equality in the multi-channel tests below. -/
example (systemEvent : System.RecoveryEvent) (external : String → InEnv)
    (systemState : recoveryDeeperSystem.State)
    (queue : Chan.State recoveryPhysicalBinding.connection.width)
    (queueEq : queue = recoveryDeeperSystem.channelState systemState
      recoveryPhysicalBinding.connection) :
    ∃ recovery : Chan.RecoveryRefinement recoveryPhysicalBinding.connection.chan,
      ∀ (concrete : recovery.ConcreteState) (request : recovery.Request),
        recovery.Rep queue concrete →
        (recovery.step concrete request).event =
            recoveryDeeperSystem.recoveryChannelEvent systemEvent systemState
              recoveryPhysicalBinding.connection →
        let next := recovery.step concrete request
        recovery.Rep
            (recoveryDeeperSystem.channelState
              (recoveryDeeperSystem.advanceRecovery systemEvent external systemState)
              recoveryPhysicalBinding.connection)
            next.state ∧
          (recoveryPhysicalBinding.connection.chan.recoveryStep queue
            next.event).accepted = next.accepted ∧
          (recoveryPhysicalBinding.connection.chan.recoveryStep queue
            next.event).delivered = next.delivered := by
  exact recoveryDeeperArtifact.binding_recoveryStep_refines_advanceRecovery
    (by rfl) (.recoveryPortable recoveryPhysicalBinding)
    (by
      change (.recoveryPortable recoveryPhysicalBinding :
        System.CertifiedChannelBinding) ∈
          [(.recoveryPortable recoveryPhysicalBinding :
            System.CertifiedChannelBinding)]
      simp)
    (by rfl) systemEvent external systemState queue queueEq

/-! One island with two incident channels exercises the large-SoC
coordination fold rather than only the one-channel degenerate case. -/

example : Machines.Multiclock.RecoverySmoke.application.artifact.emissionCheck.isOk := by
  native_decide
example : Machines.Multiclock.RecoverySmoke.application.artifact.bindings.length = 2 := by
  native_decide
example : Machines.Multiclock.RecoverySmoke.application.artifact.renderedVerilog.contains
    ".left(recovery_center__recover), .right(__loom_recovery_recovery_in_src_done), .and_out(recovery_center__recovery_acc_0)" := by
  native_decide
example : Machines.Multiclock.RecoverySmoke.application.artifact.renderedVerilog.contains
    ".left(recovery_center__recovery_acc_0), .right(__loom_recovery_recovery_in_dst_done), .and_out(recovery_center__recovery_acc_1)" := by
  native_decide
example : Machines.Multiclock.RecoverySmoke.application.artifact.renderedVerilog.contains
    ".left(recovery_center__recovery_acc_1), .right(__loom_recovery_recovery_out_src_done), .and_out(recovery_center__recovery_acc_2)" := by
  native_decide
example : Machines.Multiclock.RecoverySmoke.application.artifact.renderedVerilog.contains
    ".left(recovery_center__recovery_acc_2), .right(__loom_recovery_recovery_out_dst_done), .and_out(recovery_center__recovered)" := by
  native_decide
example : Machines.Multiclock.RecoverySmoke.application.artifact.renderedVerilog.contains
    ".rst(recovery_center__recovery_reset)" := by native_decide

example := Machines.Multiclock.RecoverySmoke.system.recoveryEndpointsFor_contains_both
  Machines.Multiclock.RecoverySmoke.centerIsland.toSystemIsland
  Machines.Multiclock.RecoverySmoke.inputRoute.toSystemConnection
  (by
    change Machines.Multiclock.RecoverySmoke.inputRoute.toSystemConnection ∈
      [Machines.Multiclock.RecoverySmoke.inputRoute.toSystemConnection,
       Machines.Multiclock.RecoverySmoke.outputRoute.toSystemConnection]
    simp)
  (by native_decide)

def globallyReadyEndpoint : Chan.RecoveryProtocol.Endpoint :=
  { flushed := true }

def globallyReadyInputProtocol :
    Chan.RecoveryProtocol.State 8 :=
  { queue := [19#8]
    source := globallyReadyEndpoint
    sink := globallyReadyEndpoint
    recovering := true }

def globallyReadyOutputProtocol :
    Chan.RecoveryProtocol.State 8 :=
  { queue := [23#8]
    source := globallyReadyEndpoint
    sink := globallyReadyEndpoint
    recovering := true }

def globallyReadyRequest (width : Nat) :
    Chan.RecoveryProtocol.Request width := {}

def allRecoveryEndpointsDone : System.RecoveryEndpointKey → Bool :=
  fun _ => true

def centerRecoveryEvent : System.RecoveryEvent where
  tick := { clocks := [] }
  resetIslands := [Machines.Multiclock.RecoverySmoke.centerIsland.name]

/-- Both channels linearize on the same island-level recovery event even
though either physical FIFO may have reached its held-reset state earlier. -/
example :
    let request : Chan.RecoveryProtocol.Coordinated.Request 8 :=
      { endpoint := globallyReadyRequest 8, commit := true }
    (Chan.RecoveryProtocol.Coordinated.step
        Machines.Multiclock.RecoverySmoke.inputQueue
        globallyReadyInputProtocol request).event =
      Machines.Multiclock.RecoverySmoke.system.recoveryChannelEvent
        centerRecoveryEvent Machines.Multiclock.RecoverySmoke.system.reset
        Machines.Multiclock.RecoverySmoke.inputRoute.toSystemConnection := by
  exact System.CertifiedRealizedSystem.coordinatedProtocol_event_eq_systemRecovery
    Machines.Multiclock.RecoverySmoke.system
    Machines.Multiclock.RecoverySmoke.centerIsland.toSystemIsland
    Machines.Multiclock.RecoverySmoke.inputRoute.toSystemConnection
    (by
      change Machines.Multiclock.RecoverySmoke.inputRoute.toSystemConnection ∈
        [Machines.Multiclock.RecoverySmoke.inputRoute.toSystemConnection,
         Machines.Multiclock.RecoverySmoke.outputRoute.toSystemConnection]
      simp)
    (by native_decide) centerRecoveryEvent
    Machines.Multiclock.RecoverySmoke.system.reset (by native_decide)
    globallyReadyInputProtocol (globallyReadyRequest 8) rfl
    allRecoveryEndpointsDone (by native_decide) (by native_decide)
    (by native_decide)

example :
    let request : Chan.RecoveryProtocol.Coordinated.Request 8 :=
      { endpoint := globallyReadyRequest 8, commit := true }
    (Chan.RecoveryProtocol.Coordinated.step
        Machines.Multiclock.RecoverySmoke.outputQueue
        globallyReadyOutputProtocol request).event =
      Machines.Multiclock.RecoverySmoke.system.recoveryChannelEvent
        centerRecoveryEvent Machines.Multiclock.RecoverySmoke.system.reset
        Machines.Multiclock.RecoverySmoke.outputRoute.toSystemConnection := by
  exact System.CertifiedRealizedSystem.coordinatedProtocol_event_eq_systemRecovery
    Machines.Multiclock.RecoverySmoke.system
    Machines.Multiclock.RecoverySmoke.centerIsland.toSystemIsland
    Machines.Multiclock.RecoverySmoke.outputRoute.toSystemConnection
    (by
      change Machines.Multiclock.RecoverySmoke.outputRoute.toSystemConnection ∈
        [Machines.Multiclock.RecoverySmoke.inputRoute.toSystemConnection,
         Machines.Multiclock.RecoverySmoke.outputRoute.toSystemConnection]
      simp)
    (by native_decide) centerRecoveryEvent
    Machines.Multiclock.RecoverySmoke.system.reset (by native_decide)
    globallyReadyOutputProtocol (globallyReadyRequest 8) rfl
    allRecoveryEndpointsDone (by native_decide) (by native_decide)
    (by native_decide)

/-- Mixing an ordinary coordinated-reset binding into an independent-reset
artifact is rejected before a `CertifiedRealizedSystem` can be constructed. -/
example : recoveryDeeperSystem.selectedCheck RealizationPlan.portable = false := by
  native_decide
example : (recoveryDeeperSystem.realizeWithChecked
    RealizationPlan.portable).isOk = false := by native_decide

def unsupportedDepth : Chan 8 := ⟨"bad_depth", 3, .exchange⟩
def unsupportedRoute : ChannelRoute 8 :=
  unsupportedDepth.between deeperProducerIsland deeperConsumerIsland
def unsupportedBuilder : SystemBuilder :=
  System.empty
    |>.addIsland deeperProducerIsland
    |>.addIsland deeperConsumerIsland
    |>.addChannel unsupportedRoute
    |>.withClockRel .asynchronous
def unsupportedSystem : System := unsupportedBuilder.certify (by decide)

example : unsupportedSystem.stockCheck = false := by decide
example : unsupportedSystem.realizePortableChecked.isOk = false := by native_decide
example : unsupportedSystem.readinessIssues.contains
    ⟨"channel bad_depth", "portable Gray FIFO depth must be a power of two; declared 3"⟩ := by
  native_decide

example : application.artifact.renderedUTF8 =
    application.artifact.renderedVerilog.toUTF8 :=
  application.artifact.renderedUTF8_eq

example (event : NamedClockEvent) (state : system.State) :
    (system.resolveConnection event state connection).result =
      system.connectionResult event state connection := by simp

example (event : NamedClockEvent) (state : system.State) :
    (system.resolveConnection event state connection).sinkPayload =
      (System.channelState state connection).head?.getD 0 := by simp

example {input middle output : List Nat}
    (first : TraceContract.mapPrefix (fun value => value + 1) input middle)
    (second : TraceContract.mapPrefix (fun value => value * 2) middle output) :
    TraceContract.mapPrefix (fun value => (value + 1) * 2) input output := by
  simpa [Function.comp_def] using TraceContract.mapPrefix_comp first second

example {input middle output : TraceContract.CountTrace}
    (first : TraceContract.deliveredWithin 3 input middle)
    (second : TraceContract.deliveredWithin 5 middle output) :
    TraceContract.deliveredWithin 8 input output := by
  simpa using TraceContract.deliveredWithin_comp first second

example := monitor_ok_system
example := channel_capacity_system
example := certifiedArtifact_bytes
example := certifiedArtifact_complete

end Tests.MulticlockApi
