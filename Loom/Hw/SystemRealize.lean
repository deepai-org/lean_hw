-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.System
import Loom.Hw.ChanRefinement
import Loom.Hw.EmitIO
import Loom.Hw.RecoveryCoordinatorDesign

/-!
# Explicit physical realization of named systems

`System` remains the technology-neutral semantic assembly.  This file adds
the separate object required for physical emission: every connection is
bound, in declaration order, to one certified channel implementation.

This module deliberately contains no behavioral CDC Verilog. A physical
binding joins a semantic refinement to an explicit artifact-boundary
renderer; that join is not itself a proof that the rendered text implements
the refinement. Optional handwritten reference renderers therefore live in
`Evidence`, while the certified path is being replaced by compiler-produced
per-domain `Design`s.
-/

namespace Loom.Hw
namespace System

/-- Exact hierarchy-relative hardware object named by physical intent. The
path is derived from generated instances rather than rediscovered by a regex.
A backend is responsible for escaping it in its own query language. -/
structure PhysicalObject where
  path : List String
  deriving DecidableEq, Repr

def PhysicalObject.render (object : PhysicalObject) : String :=
  String.intercalate "/" object.path

/-- Which period supplies a relative physical bound. `fasterOf` is resolved
only after a target clock plan supplies actual periods. -/
inductive PeriodReference where
  | clock (name : String)
  | fasterOf (left right : String)
  deriving DecidableEq, Repr

def PeriodReference.describe : PeriodReference → String
  | .clock name => s!"the `{name}` clock"
  | .fasterOf left right =>
      s!"the faster endpoint clock (`{left}` or `{right}`)"

/-- A technology-neutral bound relative to a clock period. This avoids
inventing nanoseconds before a board or ASIC clock plan is selected. -/
structure PeriodBound where
  reference : PeriodReference
  numerator : Nat := 1
  denominator : Nat := 1
  deriving DecidableEq, Repr

/-- Technology-neutral physical intent. Backends may render this as SDC, XDC,
Quartus assignments, ASIC implementation directives, or a signoff checklist;
the semantic system does not depend on any one lowering. -/
inductive TimingConstraint where
  | asynchronousClocks (left right : String)
  | maxDelay (fromClock toClock : String) (nanoseconds : Nat)
  | falsePath (fromClock toClock : String)
  /-- Ordered destination-domain sampling registers. Placement/preservation
  and synchronizer identification are required facts, not vendor syntax. -/
  | synchronizerChain (destinationClock : String)
      (stages : List PhysicalObject)
  /-- A coherent multi-bit CDC launch into the first sampling stage. Both
  skew and datapath delay are bounded relative to a clock period. -/
  | coherentBus (sourceClock destinationClock : String)
      (launch capture : PhysicalObject) (width : Nat)
      (maxSkew maxDelay : PeriodBound)
  deriving DecidableEq, Repr

/-! ## Technology-neutral reset delivery intent

This records only the digital contract implemented by the generated neutral
RTL.  It is not a reset-tree description and makes no claim about clock
availability, metastability, placement, or a target library. -/

inductive ResetPolarity where
  | activeHigh
  | activeLow
  deriving DecidableEq, Repr

inductive ResetSampling where
  | synchronous
  | asynchronous
  deriving DecidableEq, Repr

inductive ResetRelease where
  /-- Each domain samples release on its own clock; no reset synchronizer is
  generated or implied. -/
  | sampledIndependently
  /-- Reserved for a future generated synchronizer. Every stage must then be
  named in the physical-intent manifest. -/
  | synchronized (stages : List PhysicalObject)
  deriving DecidableEq, Repr

/-- Compact physical reset contract for one clock domain. Logical traffic
recovery remains the separate `SystemResetPolicy`. -/
structure ResetIntent where
  clock : String
  source : String
  polarity : ResetPolarity
  assertion : ResetSampling
  release : ResetRelease
  requiresClockWhileAsserted : Bool
  deriving DecidableEq, Repr

/-- The current neutral modules all sample the shared active-high `rst`
synchronously. Consequently every domain must tick while reset is asserted,
and release may be observed on different ticks in different domains. -/
def resetIntents (sys : System) : List ResetIntent :=
  (sys.islands.map (fun island => island.clock)).eraseDups.map fun clock =>
    { clock
      source := "rst"
      polarity := .activeHigh
      assertion := .synchronous
      release := .sampledIndependently
      requiresClockWhileAsserted := true }

@[simp] theorem resetIntents_clock_coverage (sys : System) :
    (resetIntents sys).map (fun intent => intent.clock) =
      (sys.islands.map (fun island => island.clock)).eraseDups := by
  simp only [resetIntents, List.map_map]
  change List.map id _ = _
  exact List.map_id _

@[simp] theorem resetIntents_sources (sys : System) :
    (resetIntents sys).map (fun intent => intent.source) =
      List.replicate (resetIntents sys).length "rst" := by
  unfold resetIntents
  generalize (sys.islands.map (fun island => island.clock)).eraseDups = clocks
  induction clocks with
  | nil => rfl
  | cons clock rest ih =>
      simp only [List.map_cons, List.length_cons, List.length_map, ih]
      rw [List.replicate_succ]

inductive ClockRule where
  | same
  | different
  | any
  deriving DecidableEq, Repr

/-! ## Technology-neutral channel timing

These values describe latency introduced by a selected realization.  They do
not invent a global clock for asynchronous systems and do not turn a physical
clock period into a semantic fact. -/

inductive TimingUnit where
  | sourceTicks
  | sinkTicks
  | sharedTicks
  | systemEvents
  | grants
  deriving DecidableEq, Repr

/-- Premises that commonly turn elastic service into a finite bound.  A
realization must not report a conditional bound without listing every premise
on which it depends. -/
inductive TimingPremise where
  | sourceContinuesTicking
  | sinkContinuesTicking
  | sourceReadyEveryTick
  | sinkPayloadAvailableEveryTick
  | sinkConsumesWhenAvailable
  | sourceEventuallyObservesSink
  | sinkEventuallyObservesSource
  | recoveryRequestHeld
  deriving DecidableEq, Repr

/-- What the selected realization can honestly say about service. `exact` and
`conditional` are theorem-facing claims; `scheduleDependent` deliberately
contains no optimistic number. -/
inductive TimingBound where
  | exact (amount : Nat) (unit : TimingUnit)
  | conditional (amount : Nat) (unit : TimingUnit)
      (premises : List TimingPremise)
  | scheduleDependent (premises : List TimingPremise)
  | unspecified
  | notApplicable
  deriving DecidableEq, Repr

/-- Inspectable structural latency and service contract for one channel
realization. Synchronizer counts describe the selected circuit; `delivery`
and `recovery` state whether a finite semantic bound is actually supplied. -/
structure ChannelTiming where
  /-- Registers between an application `send` action and a physical offer. -/
  sourceOfferStages : Nat
  /-- Registers between an application `consume` action and a physical pop. -/
  sinkConsumeStages : Nat
  forwardSynchronizerStages : Nat
  reverseSynchronizerStages : Nat
  storageReadStages : Nat
  /-- Best back-to-back application issue rate of the generated source
  endpoint while the selected realization remains ready. -/
  sourceIssueInterval : TimingBound
  /-- Best back-to-back application consumption rate while payloads remain
  continuously visible. This exposes endpoint throttling separately from CDC
  service latency. -/
  sinkIssueInterval : TimingBound
  delivery : TimingBound
  recovery : TimingBound := .notApplicable
  deriving DecidableEq, Repr

namespace ChannelTiming

/-- Honest fallback for expert bindings that have not supplied timing
evidence. It is inspectable as unknown rather than silently treated as
zero-latency. -/
def unspecified : ChannelTiming where
  sourceOfferStages := 0
  sinkConsumeStages := 0
  forwardSynchronizerStages := 0
  reverseSynchronizerStages := 0
  storageReadStages := 0
  sourceIssueInterval := .unspecified
  sinkIssueInterval := .unspecified
  delivery := .unspecified

def isSpecified (timing : ChannelTiming) : Bool :=
  timing.delivery != .unspecified

end ChannelTiming

/-- The fields that identify one abstract connection independently of its
island `Design` values.  Equality of ordered key lists is the realization
coverage certificate. -/
structure ConnectionKey where
  channel : String
  width : Nat
  depth : Nat
  policy : FullCoTickPolicy
  source : String
  sink : String
  deriving DecidableEq, Repr

def _root_.Loom.Hw.SystemConnection.key (connection : SystemConnection) : ConnectionKey :=
  { channel := connection.chan.name
    width := connection.width
    depth := connection.chan.depth
    policy := connection.chan.policy
    source := connection.source
    sink := connection.sink }

/-- A physical binding for one particular typed channel. The refinement field
certifies the executable implementation model only. `moduleText` is an
explicit, separately documented artifact boundary; possession of this
structure must never be described as RTL/refinement correspondence. -/
structure BoundImplementation where
  connection : SystemConnection
  name : String
  clockRule : ClockRule
  refinement : Chan.Refinement connection.chan
  moduleName : CrossingInfo → String
  moduleText : CrossingInfo → String
  instanceText : CrossingInfo → String
  constraints : CrossingInfo → List TimingConstraint
  timing : ChannelTiming := .unspecified

namespace BoundImplementation

private def channelStem (info : CrossingInfo) : String :=
  "__loom_chan_" ++ info.channel ++ "_"

def islandSignal (island signal : String) : String := island ++ "__" ++ signal
def islandOutput (island signal : String) : String :=
  islandSignal island ("o_" ++ signal)

def channelInstance (moduleName : String) (info : CrossingInfo) : String :=
  let sourceClock := info.sourceClock.getD "missing_source_clock"
  let sinkClock := info.sinkClock.getD "missing_sink_clock"
  let stem := channelStem info
  let sourceValid := islandOutput info.source (stem ++ "src_valid")
  let sourcePayload := islandOutput info.source (stem ++ "src_payload")
  let sourceReady := islandSignal info.source (stem ++ "src_ready")
  let sinkValid := islandSignal info.sink (stem ++ "dst_valid")
  let sinkPayload := islandSignal info.sink (stem ++ "dst_payload")
  let sinkPop := islandOutput info.sink (stem ++ "dst_pop")
  s!"{moduleName} u_{info.channel} (\n" ++
  s!"  .src_clk({sourceClock}), .dst_clk({sinkClock}), .rst(rst),\n" ++
  s!"  .src_valid({sourceValid}), .src_payload({sourcePayload}), .src_ready({sourceReady}),\n" ++
  s!"  .dst_valid({sinkValid}), .dst_payload({sinkPayload}), .dst_pop({sinkPop}));\n" ++
  s!"assign {islandSignal info.source (stem ++ "src_accepted")} = " ++
    s!"{sourceValid} && {sourceReady};\n"

/-- Artifact-boundary extension point for external implementations using the
ordinary coordinated-reset channel interface. Generic Loom supplies no
handwritten behavioral module through this constructor. -/
def custom (connection : SystemConnection) (name : String) (clockRule : ClockRule)
    (refinement : Chan.Refinement connection.chan)
    (moduleName moduleText : CrossingInfo → String)
    (constraints : CrossingInfo → List TimingConstraint)
    (timing : ChannelTiming := .unspecified) : BoundImplementation :=
  { connection, name, clockRule, refinement, moduleName, moduleText, constraints, timing
    instanceText := fun info => channelInstance (moduleName info) info }

/-- Structural-instance extension point for a binding whose checked wrapper
has additional protocol ports, such as graceful recovery. The renderer remains
an explicit artifact boundary; certified callers separately restrict which
closed bindings may use it. -/
def customInstance (connection : SystemConnection) (name : String)
    (clockRule : ClockRule) (refinement : Chan.Refinement connection.chan)
    (moduleName moduleText instanceText : CrossingInfo → String)
    (constraints : CrossingInfo → List TimingConstraint)
    (timing : ChannelTiming := .unspecified) : BoundImplementation :=
  ⟨connection, name, clockRule, refinement, moduleName, moduleText,
    instanceText, constraints, timing⟩

end BoundImplementation

private abbrev islandSignal := BoundImplementation.islandSignal
private abbrev islandOutput := BoundImplementation.islandOutput

def BoundImplementation.key (binding : BoundImplementation) : ConnectionKey :=
  binding.connection.key

def clockRuleOk (sys : System) (binding : BoundImplementation) : Bool :=
  match sys.findIsland? binding.connection.source,
      sys.findIsland? binding.connection.sink with
  | some source, some sink =>
      let info : CrossingInfo :=
        { channel := binding.connection.chan.name
          width := binding.connection.width
          depth := binding.connection.chan.depth
          policy := binding.connection.chan.policy
          source := binding.connection.source
          sourceClock := some source.clock
          sink := binding.connection.sink
          sinkClock := some sink.clock }
      let constrained := !(binding.constraints info).isEmpty
      match binding.clockRule with
      | .same => source.clock == sink.clock
      | .different => source.clock != sink.clock && constrained
      | .any => source.clock == sink.clock || constrained
  | _, _ => false

/-- A fully bound physical system.  Its constructor is private: emission APIs
cannot receive a missing, duplicated, reordered, or wrong-clock binding. -/
structure RealizedSystem where
  private mk ::
  system : System
  bindings : List BoundImplementation
  coverage : bindings.map BoundImplementation.key =
    system.connections.map SystemConnection.key
  clockRules : bindings.all (clockRuleOk system) = true

/-- Fail-closed physical assembly. Binding order is canonical declaration
order, which makes artifact/inventory completeness structural rather than a
post-hoc set comparison. -/
def realize (sys : System) (bindings : List BoundImplementation) :
    Except String RealizedSystem :=
  if coverage : bindings.map BoundImplementation.key =
      sys.connections.map SystemConnection.key then
    if clocks : bindings.all (clockRuleOk sys) = true then
      pure ⟨sys, bindings, coverage, clocks⟩
    else throw "channel realization does not match endpoint clocks"
  else throw "channel realizations must cover every connection exactly once, in declaration order"

/-- Kernel-checked constructor for generated declarations whose two physical
assembly gates can be discharged during elaboration. -/
def realizeChecked (sys : System) (bindings : List BoundImplementation)
    (coverage : bindings.map BoundImplementation.key =
      sys.connections.map SystemConnection.key)
    (clockRules : bindings.all (clockRuleOk sys) = true) : RealizedSystem :=
  ⟨sys, bindings, coverage, clockRules⟩

structure InstanceArtifact where
  key : ConnectionKey
  implementation : String
  moduleName : String
  moduleText : String
  instanceText : String

structure ConstraintGroup where
  key : ConnectionKey
  constraints : List TimingConstraint

structure TimingGroup where
  key : ConnectionKey
  implementation : String
  timing : ChannelTiming

/-- Structured top-level plan.  Rendering is deliberately downstream of this
value, so the list proved complete below is the very list traversed by the
top-level printer rather than parallel report metadata. -/
structure TopModuleArtifact where
  ports : List String
  wires : List String
  islandInstances : List String
  channelInstances : List InstanceArtifact

/-- Structured technology-neutral constraint-report plan, for the same reason as
`TopModuleArtifact`: its checked groups are exactly what the renderer walks. -/
structure ConstraintFileArtifact where
  groups : List ConstraintGroup

/-- One exact neutral physical requirement, paired with its connection key so
a backend result cannot drift across channels with similar signal names. -/
structure ConstraintRequirement where
  key : ConnectionKey
  intent : TimingConstraint
  deriving DecidableEq, Repr

def ConstraintFileArtifact.requirements
    (file : ConstraintFileArtifact) : List ConstraintRequirement :=
  file.groups.flatMap fun group =>
    group.constraints.map fun intent => { key := group.key, intent }

/-- The physical artifact plan. The complete abstract inventory is carried
verbatim, while the emitted top and human-facing constraint report retain
their checked structures until the final text-rendering boundary. -/
structure PhysicalArtifacts where
  inventory : List CrossingInfo
  instances : List InstanceArtifact
  islandModules : List (String × String)
  topModule : TopModuleArtifact
  constraintFile : ConstraintFileArtifact
  /-- Exact per-domain reset delivery contracts. This is emitted beside CDC
  intent but remains distinct from logical channel recovery policy. -/
  resetIntents : List ResetIntent
  /-- Typed inspection data, deliberately not an emitted sidecar file. -/
  timing : List TimingGroup
  inventoryText : String

/-- Every obligation exported to a downstream implementation flow. Reset
delivery is included alongside channel timing intent so exact coverage cannot
silently forget either class. -/
inductive PhysicalRequirement where
  | timing (requirement : ConstraintRequirement)
  | reset (intent : ResetIntent)
  deriving DecidableEq, Repr

def PhysicalArtifacts.requirements
    (artifacts : PhysicalArtifacts) : List PhysicalRequirement :=
  artifacts.constraintFile.requirements.map PhysicalRequirement.timing ++
    artifacts.resetIntents.map PhysicalRequirement.reset

/-- Result vocabulary shared by FPGA and ASIC evidence adapters. `pass` means
the named backend actually accepted/checked the requirement; generic Loom
emission never manufactures it. `skip` is an explicit unavailable check and
`unconstrained` means the backend left required intent uncovered. -/
inductive PhysicalCheckStatus where
  | pass
  | skip
  | unconstrained
  deriving DecidableEq, Repr

structure PhysicalCheckResult where
  requirement : PhysicalRequirement
  status : PhysicalCheckStatus
  detail : String := ""
  deriving Repr

/-- A backend report is constructible only with exact ordered coverage of the
full neutral requirement list. This prevents a successful wrapper from
silently omitting a Gray bus, synchronizer chain, or reset-domain contract. -/
structure PhysicalCheckReport (artifacts : PhysicalArtifacts) where
  backend : String
  results : List PhysicalCheckResult
  coverage : results.map (fun result => result.requirement) =
    artifacts.requirements

def PhysicalCheckReport.passed {artifacts : PhysicalArtifacts}
    (report : PhysicalCheckReport artifacts) : Bool :=
  report.results.all fun result => result.status == .pass

def PhysicalCheckStatus.render : PhysicalCheckStatus → String
  | .pass => "PASS"
  | .skip => "SKIP"
  | .unconstrained => "UNCONSTRAINED"

private def infoFor (sys : System) (binding : BoundImplementation) : CrossingInfo :=
  { channel := binding.connection.chan.name
    width := binding.connection.width
    depth := binding.connection.chan.depth
    policy := binding.connection.chan.policy
    source := binding.connection.source
    sourceClock := (sys.findIsland? binding.connection.source).map (fun island => island.clock)
    sink := binding.connection.sink
    sinkClock := (sys.findIsland? binding.connection.sink).map (fun island => island.clock) }

private def endpointOutputs (sys : System) (islandName : String) : List String :=
  sys.connections.flatMap fun connection =>
    (if connection.source = islandName then
      [connection.chan.sourceValidName, connection.chan.sourcePayloadName]
    else []) ++
    (if connection.sink = islandName then [connection.chan.sinkPopName] else [])

private def endpointOutput (sys : System) (islandName outputName : String) : Bool :=
  (endpointOutputs sys islandName).contains outputName

private def endpointInput (sys : System) (islandName inputName : String) : Bool :=
  sys.connections.any fun connection =>
    (connection.source = islandName &&
      (inputName = connection.chan.sourceReadyName ||
        inputName = connection.chan.sourceAcceptedName)) ||
    (connection.sink = islandName &&
      (inputName = connection.chan.sinkValidName ||
        inputName = connection.chan.sinkPayloadName))

private def physicalIslandDesign (_sys : System) (island : SystemIsland) : Design :=
  island.design

private def portWidth (width : Nat) : String :=
  if width = 1 then "" else s!"[{width - 1}:0] "

private def islandModule (sys : System) (island : SystemIsland) : String × String :=
  let design := physicalIslandDesign sys island
  (design.name, Loom.Emit.MicroVerilog.Print.print (Loom.Hw.Compile.compile design))

private def clockPorts (sys : System) : List String :=
  (sys.islands.map (fun island => island.clock)).eraseDups

private def topPorts (sys : System) : List String :=
  (clockPorts sys).map ("input wire " ++ ·) ++ ["input wire rst"] ++
  (if sys.resetPolicy = .independentFlush then
    sys.islands.flatMap fun island =>
      [s!"input wire {islandSignal island.name "recover"}",
       s!"output wire {islandSignal island.name "recovered"}"]
   else []) ++
  sys.islands.flatMap fun island =>
    let externalInputs := island.design.inputs.filter fun input =>
      !endpointInput sys island.name input.name
    let externalOutputs := island.design.regs.filter fun reg =>
      island.design.outputs.contains reg.name &&
        !endpointOutput sys island.name reg.name
    externalInputs.map (fun input =>
      s!"input wire {portWidth input.width}{islandSignal island.name input.name}") ++
    externalOutputs.map (fun reg =>
      s!"output wire {portWidth reg.width}{islandOutput island.name reg.name}")

private def topPortNames (sys : System) : List String :=
  clockPorts sys ++ ["rst"] ++
    (if sys.resetPolicy = .independentFlush then
      sys.islands.flatMap fun island =>
        [islandSignal island.name "recover", islandSignal island.name "recovered"]
     else []) ++ sys.islands.flatMap fun island =>
    let externalInputs := island.design.inputs.filter fun input =>
      !endpointInput sys island.name input.name
    let externalOutputs := island.design.regs.filter fun reg =>
      island.design.outputs.contains reg.name &&
        !endpointOutput sys island.name reg.name
    externalInputs.map (fun input => islandSignal island.name input.name) ++
      externalOutputs.map (fun reg => islandOutput island.name reg.name)

/-- One physical endpoint half whose graceful-recovery completion contributes
to an island's reset gate. Keeping the side explicit prevents an incident
channel from being mistaken for one completion bit. -/
inductive RecoveryEndpointSide where
  | source
  | sink
  deriving DecidableEq, Repr

structure RecoveryEndpointKey where
  connection : ConnectionKey
  side : RecoveryEndpointSide
  deriving DecidableEq, Repr

def _root_.Loom.Hw.SystemConnection.recoveryEndpointKeys
    (connection : SystemConnection) : List RecoveryEndpointKey :=
  [⟨connection.key, .source⟩, ⟨connection.key, .sink⟩]

def RecoveryEndpointKey.doneSignal (endpoint : RecoveryEndpointKey) : String :=
  let suffix := match endpoint.side with
    | .source => "src_done"
    | .sink => "dst_done"
  s!"__loom_recovery_{endpoint.connection.channel}_{suffix}"

/-- Exact ordered recovery domain for one island: both physical halves of
every incident channel, in connection order. -/
def recoveryEndpointsFor (sys : System)
    (island : SystemIsland) : List RecoveryEndpointKey :=
  sys.connections.flatMap fun connection =>
    if connection.source = island.name || connection.sink = island.name then
      connection.recoveryEndpointKeys
    else []

/-- A requested island may reset only after every endpoint half of every
incident channel has flushed. Waiting merely for the local halves is too weak:
the remote half may have acknowledged the request but not yet completed its
own FIFO reset. -/
def recoveryDoneSignals (sys : System) (island : SystemIsland) : List String :=
  (recoveryEndpointsFor sys island).map RecoveryEndpointKey.doneSignal

/-- Technology-neutral Boolean meaning of one island's recovery gate. -/
def recoveryComplete (sys : System) (island : SystemIsland)
    (request : Bool) (done : RecoveryEndpointKey → Bool) : Bool :=
  RecoveryCoordinator.fold request
    ((recoveryEndpointsFor sys island).map done)

theorem recoveryComplete_iff (sys : System) (island : SystemIsland)
    (request : Bool) (done : RecoveryEndpointKey → Bool) :
    recoveryComplete sys island request done = true ↔
      request = true ∧ ∀ endpoint ∈ recoveryEndpointsFor sys island,
        done endpoint = true := by
  rw [recoveryComplete, RecoveryCoordinator.fold_true_iff]
  simp

/-- The coordinator never hides a missing endpoint-side obligation. Any
property implied by each asserted `done` signal holds for every physical half
of every incident channel when the island reports complete. -/
theorem recoveryComplete_implies_all (sys : System) (island : SystemIsland)
    (request : Bool) (done property : RecoveryEndpointKey → Bool)
    (doneImplies : ∀ endpoint, done endpoint = true → property endpoint = true)
    (complete : recoveryComplete sys island request done = true) :
    ∀ endpoint ∈ recoveryEndpointsFor sys island, property endpoint = true := by
  have allDone := (recoveryComplete_iff sys island request done).mp complete
  intro endpoint member
  exact doneImplies endpoint (allDone.2 endpoint member)

theorem recoveryEndpointsFor_contains_both (sys : System)
    (island : SystemIsland) (connection : SystemConnection)
    (member : connection ∈ sys.connections)
    (incident : (connection.source == island.name ||
      connection.sink == island.name) = true) :
    ⟨connection.key, .source⟩ ∈ recoveryEndpointsFor sys island ∧
      ⟨connection.key, .sink⟩ ∈ recoveryEndpointsFor sys island := by
  simp only [Bool.or_eq_true, beq_iff_eq] at incident
  simp only [recoveryEndpointsFor, List.mem_flatMap]
  refine ⟨⟨connection, member, ?_⟩, ⟨connection, member, ?_⟩⟩
  all_goals simp [incident, SystemConnection.recoveryEndpointKeys]

/-- A completed island-level recovery exposes both halves of every incident
channel as done.  This is the structural fact used to commit all affected
logical channel epochs at one System-level linearization point, even when the
physical halves reached their done states on different earlier clocks. -/
theorem recoveryComplete_incident_both (sys : System)
    (island : SystemIsland) (connection : SystemConnection)
    (member : connection ∈ sys.connections)
    (incident : (connection.source == island.name ||
      connection.sink == island.name) = true)
    (request : Bool) (done : RecoveryEndpointKey → Bool)
    (complete : recoveryComplete sys island request done = true) :
    done ⟨connection.key, .source⟩ = true ∧
      done ⟨connection.key, .sink⟩ = true := by
  have both := recoveryEndpointsFor_contains_both sys island connection
    member incident
  have allDone := (recoveryComplete_iff sys island request done).mp complete
  exact ⟨allDone.2 _ both.1, allDone.2 _ both.2⟩

private def internalWires (sys : System) : List String :=
  (if sys.resetPolicy = .independentFlush then
    (sys.connections.flatMap fun connection =>
      [s!"wire __loom_recovery_{connection.chan.name}_src_done;",
       s!"wire __loom_recovery_{connection.chan.name}_dst_done;"]) ++
    (sys.islands.flatMap fun island =>
      let incidentCount := (recoveryDoneSignals sys island).length
      [s!"wire {islandSignal island.name "recovery_reset"};"] ++
        (List.range (incidentCount - 1)).map fun index =>
          s!"wire {islandSignal island.name s!"recovery_acc_{index}"};")
   else []) ++ sys.islands.flatMap fun island =>
    let drivenInputs := island.design.inputs.filter fun input =>
      endpointInput sys island.name input.name
    let physical := physicalIslandDesign sys island
    let internalOutputs := physical.regs.filter fun reg =>
      physical.outputs.contains reg.name && endpointOutput sys island.name reg.name
    drivenInputs.map (fun input =>
      s!"wire {portWidth input.width}{islandSignal island.name input.name};") ++
    internalOutputs.map (fun reg =>
      s!"wire {portWidth reg.width}{islandOutput island.name reg.name};")

private def internalWireNames (sys : System) : List String :=
  (if sys.resetPolicy = .independentFlush then
    (sys.connections.flatMap fun connection =>
      [s!"__loom_recovery_{connection.chan.name}_src_done",
       s!"__loom_recovery_{connection.chan.name}_dst_done"]) ++
    (sys.islands.flatMap fun island =>
      let incidentCount := (recoveryDoneSignals sys island).length
      [islandSignal island.name "recovery_reset"] ++
        (List.range (incidentCount - 1)).map fun index =>
          islandSignal island.name s!"recovery_acc_{index}")
   else []) ++ sys.islands.flatMap fun island =>
    let drivenInputs := island.design.inputs.filter fun input =>
      endpointInput sys island.name input.name
    let physical := physicalIslandDesign sys island
    let internalOutputs := physical.regs.filter fun reg =>
      physical.outputs.contains reg.name && endpointOutput sys island.name reg.name
    drivenInputs.map (fun input => islandSignal island.name input.name) ++
      internalOutputs.map (fun reg => islandOutput island.name reg.name)

private def islandInstance (sys : System) (island : SystemIsland) : String :=
  let physical := physicalIslandDesign sys island
  let connections :=
    [s!".clk({island.clock})",
      s!".rst({if sys.resetPolicy = .independentFlush then
        islandSignal island.name "recovery_reset" else "rst"})"] ++
    physical.inputs.map (fun input =>
      s!".{input.name}({islandSignal island.name input.name})") ++
    (physical.regs.filter (fun reg => physical.outputs.contains reg.name)).map (fun reg =>
      s!".o_{reg.name}({islandOutput island.name reg.name})")
  s!"{physical.name} u_island_{island.name} (" ++
    String.intercalate ", " connections ++ ");"

private def recoveryCoordinatorChain (island : SystemIsland) :
    Nat → String → List String → List String
  | _, _, [] => []
  | index, previous, [done] =>
      [s!"{RecoveryCoordinator.design.name} u_recovery_{island.name}_{index} (" ++
        s!".clk({island.clock}), .rst(rst), .left({previous}), .right({done}), " ++
        s!".and_out({islandSignal island.name "recovered"}), .or_out());"]
  | index, previous, done :: rest =>
      let next := islandSignal island.name s!"recovery_acc_{index}"
      (s!"{RecoveryCoordinator.design.name} u_recovery_{island.name}_{index} (" ++
        s!".clk({island.clock}), .rst(rst), .left({previous}), .right({done}), " ++
        s!".and_out({next}), .or_out());") ::
          recoveryCoordinatorChain island (index + 1) next rest

private def recoveryCoordinatorInstances (sys : System) : List String :=
  if sys.resetPolicy = .independentFlush then
    sys.islands.flatMap fun island =>
      let done := match recoveryDoneSignals sys island with
        | [] => ["1'b1"]
        | signals => signals
      recoveryCoordinatorChain island 0 (islandSignal island.name "recover") done ++
        [s!"{RecoveryCoordinator.design.name} u_recovery_reset_{island.name} (" ++
          s!".clk({island.clock}), .rst(rst), .left(rst), " ++
          s!".right({islandSignal island.name "recovered"}), .and_out(), " ++
          s!".or_out({islandSignal island.name "recovery_reset"}));"]
  else []

def TopModuleArtifact.render (top : TopModuleArtifact) : String :=
  let header := "module loom_system(\n  " ++
    String.intercalate ",\n  " top.ports ++ "\n);"
  let channels := top.channelInstances.map (fun artifact => artifact.instanceText)
  String.intercalate "\n" <|
    [header] ++ top.wires ++ top.islandInstances ++ channels ++ ["endmodule"]

private def describeConstraint : TimingConstraint → String
  | .asynchronousClocks left right =>
      s!"Treat `{left}` and `{right}` as asynchronous clocks."
  | .maxDelay fromClock toClock nanoseconds =>
      s!"Constrain `{fromClock}` to `{toClock}` to at most {nanoseconds} ns."
  | .falsePath fromClock toClock =>
      s!"Treat `{fromClock}` to `{toClock}` as a false path."
  | .synchronizerChain destinationClock stages =>
      s!"Preserve and identify the ordered synchronizer chain " ++
        String.intercalate " -> " (stages.map fun stage => s!"`{stage.render}`") ++
        s!" in destination clock `{destinationClock}`."
  | .coherentBus sourceClock destinationClock launch capture width maxSkew maxDelay =>
      s!"Constrain the {width}-bit coherent CDC bus `{launch.render}` -> " ++
        s!"`{capture.render}` (`{sourceClock}` to `{destinationClock}`): " ++
        s!"maximum bus skew {maxSkew.numerator}/{maxSkew.denominator} of " ++
        s!"{maxSkew.reference.describe} period and maximum datapath delay " ++
        s!"{maxDelay.numerator}/{maxDelay.denominator} of " ++
        s!"{maxDelay.reference.describe} period."

private def describeResetIntent (intent : ResetIntent) : String :=
  let polarity := match intent.polarity with
    | .activeHigh => "active high"
    | .activeLow => "active low"
  let assertion := match intent.assertion with
    | .synchronous => "sampled synchronously"
    | .asynchronous => "asserted asynchronously"
  let release := match intent.release with
    | .sampledIndependently =>
        "release is sampled independently by this domain; no reset synchronizer is implied"
    | .synchronized stages =>
        "release is synchronized through " ++
          String.intercalate " -> " (stages.map PhysicalObject.render)
  s!"Clock `{intent.clock}`: `{intent.source}` is {polarity} and {assertion}; " ++
    release ++ ". " ++
    (if intent.requiresClockWhileAsserted then
      "This clock must tick while reset is asserted."
    else "No asserted-reset clock-availability premise is declared.")

def renderResetIntents (intents : List ResetIntent) : String :=
  String.intercalate "\n" <|
    ["", "# Reset delivery intent", "",
      "This describes generated RTL behavior, not a physical reset tree."] ++
    intents.map fun intent => "- " ++ describeResetIntent intent

private def describePhysicalRequirement : PhysicalRequirement → String
  | .timing requirement =>
      s!"channel `{requirement.key.channel}` — " ++
        describeConstraint requirement.intent
  | .reset intent => describeResetIntent intent

def PhysicalCheckReport.render {artifacts : PhysicalArtifacts}
    (report : PhysicalCheckReport artifacts) : String :=
  (String.intercalate "\n" <|
    [s!"# Physical constraint results: {report.backend}", ""] ++
    report.results.map fun result =>
      s!"- {result.status.render}: " ++
        describePhysicalRequirement result.requirement ++
        (if result.detail.isEmpty then "" else " " ++ result.detail)) ++ "\n"

def ConstraintFileArtifact.renderNeutral
    (file : ConstraintFileArtifact) : String :=
  (String.intercalate "\n" <|
    ["# Clock-crossing constraint intent", "",
      "This technology-neutral review report is derived from the checked System.",
      "A selected FPGA or ASIC backend may translate it into tool-specific constraints."] ++
    file.groups.flatMap fun group =>
      ["", s!"## Channel `{group.key.channel}`"] ++
      match group.constraints with
      | [] => ["", "No external clock constraint is required by this realization."]
      | constraints => [""] ++ constraints.map fun constraint =>
          "- " ++ describeConstraint constraint) ++ "\n"

def TimingUnit.render : TimingUnit → String
  | .sourceTicks => "source_ticks"
  | .sinkTicks => "sink_ticks"
  | .sharedTicks => "shared_ticks"
  | .systemEvents => "system_events"
  | .grants => "grants"

def TimingPremise.render : TimingPremise → String
  | .sourceContinuesTicking => "source_continues_ticking"
  | .sinkContinuesTicking => "sink_continues_ticking"
  | .sourceReadyEveryTick => "source_ready_every_tick"
  | .sinkPayloadAvailableEveryTick => "sink_payload_available_every_tick"
  | .sinkConsumesWhenAvailable => "sink_consumes_when_available"
  | .sourceEventuallyObservesSink => "source_eventually_observes_sink"
  | .sinkEventuallyObservesSource => "sink_eventually_observes_source"
  | .recoveryRequestHeld => "recovery_request_held"

private def renderPremises (premises : List TimingPremise) : String :=
  String.intercalate "," (premises.map TimingPremise.render)

/-- Human-facing description used only when explicitly requested. The typed
`ChannelTiming` value remains the proof/program interface. -/
def TimingBound.describe : TimingBound → String
  | .exact amount unit => s!"exactly {amount} {unit.render}"
  | .conditional amount unit premises =>
      s!"at most {amount} {unit.render} when {renderPremises premises}"
  | .scheduleDependent [] => "schedule-dependent; no finite bound stated"
  | .scheduleDependent premises =>
      "schedule-dependent; progress requires " ++ renderPremises premises
  | .unspecified => "unspecified"
  | .notApplicable => "not applicable"

def TimingGroup.describe (group : TimingGroup) : String :=
  String.intercalate "\n" [
    s!"channel {group.key.channel} ({group.implementation})",
    s!"  endpoint stages: send {group.timing.sourceOfferStages}, consume {group.timing.sinkConsumeStages}",
    s!"  synchronizer stages: forward {group.timing.forwardSynchronizerStages}, reverse {group.timing.reverseSynchronizerStages}",
    s!"  storage read stages: {group.timing.storageReadStages}",
    s!"  source issue: {group.timing.sourceIssueInterval.describe}",
    s!"  sink issue: {group.timing.sinkIssueInterval.describe}",
    s!"  delivery: {group.timing.delivery.describe}",
    s!"  recovery: {group.timing.recovery.describe}" ]

private def describeCoTickPolicy : FullCoTickPolicy → String
  | .refusePush => "refuse push"
  | .exchange => "exchange"

private def renderInventoryRow (info : CrossingInfo) : String :=
  String.intercalate " | " [s!"`{info.channel}`", toString info.width,
    toString info.depth, describeCoTickPolicy info.policy, s!"`{info.source}`",
    s!"`{info.sourceClock.getD "unknown"}`", s!"`{info.sink}`",
    s!"`{info.sinkClock.getD "unknown"}`"]

private def renderInventory (inventory : List CrossingInfo) : String :=
  (String.intercalate "\n" <|
    ["# Clock-crossing inventory", "",
      "This human-readable report is derived from the checked System declaration.", "",
      "Channel | Width | Depth | Co-tick policy | Source | Source clock | Sink | Sink clock",
      "--- | ---: | ---: | --- | --- | --- | --- | ---"] ++
      inventory.map renderInventoryRow) ++ "\n"

def RealizedSystem.artifacts (realized : RealizedSystem) : PhysicalArtifacts :=
  let inventory := realized.system.crossingInventory
  let instances := realized.bindings.map fun binding =>
      let info := infoFor realized.system binding
      { key := binding.key, implementation := binding.name
        moduleName := binding.moduleName info
        moduleText := binding.moduleText info
        instanceText := binding.instanceText info }
  let constraintGroups := realized.bindings.map fun binding =>
      let info := infoFor realized.system binding
      { key := binding.key, constraints := binding.constraints info }
  let timingGroups := realized.bindings.map fun binding =>
      { key := binding.key, implementation := binding.name,
        timing := binding.timing }
  { inventory
    instances
    islandModules :=
      (if realized.system.resetPolicy = .independentFlush then
        [(RecoveryCoordinator.design.name,
          RecoveryCoordinator.certified.renderedVerilog)] else []) ++
        realized.system.islands.map (islandModule realized.system)
    topModule :=
      { ports := topPorts realized.system
        wires := internalWires realized.system
        islandInstances := recoveryCoordinatorInstances realized.system ++
          realized.system.islands.map (islandInstance realized.system)
        channelInstances := instances }
    constraintFile := { groups := constraintGroups }
    resetIntents := resetIntents realized.system
    timing := timingGroups
    inventoryText := renderInventory inventory }

private def validIdentifier (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest =>
      (first.isAlpha || first == '_') &&
        rest.all (fun c => c.isAlphanum || c == '_')

/-- Pure fail-closed gate applied before any multiclock file is written.  It
reuses the ordinary Design emission checks for every island and additionally
checks the identifiers and namespaces introduced by structural assembly. -/
def RealizedSystem.emissionCheck (realized : RealizedSystem) : Except String Unit := do
  for island in realized.system.islands do
    let physical := physicalIslandDesign realized.system island
    physical.emitCheck
    let signalNames := physical.inputs.map (·.name) ++
      physical.regs.map (·.name) ++ physical.mems.map (·.name)
    for name in island.name :: island.clock :: signalNames do
      if !validIdentifier name then
        throw s!"System.emit: '{name}' is not a portable Verilog identifier"
  for connection in realized.system.connections do
    if !validIdentifier connection.chan.name then
      throw s!"System.emit: channel '{connection.chan.name}' is not a portable Verilog identifier"
  for binding in realized.bindings do
    if !binding.timing.isSpecified then
      throw (s!"System.emit: channel '{binding.connection.chan.name}' realization " ++
        s!"'{binding.name}' has no timing contract")
  let artifacts := realized.artifacts
  let moduleNames := artifacts.islandModules.map (fun module => module.1) ++
    artifacts.instances.map (fun artifact => artifact.moduleName)
  for name in moduleNames do
    if !validIdentifier name then
      throw s!"System.emit: module '{name}' is not a portable Verilog identifier"
  if moduleNames.length != moduleNames.eraseDups.length then
    throw "System.emit: generated module-name collision"
  let instanceNames := realized.system.islands.map (fun island => "u_island_" ++ island.name) ++
    realized.system.connections.map (fun connection => "u_" ++ connection.chan.name)
  if instanceNames.length != instanceNames.eraseDups.length then
    throw "System.emit: generated instance-name collision"
  let ports := topPortNames realized.system
  if ports.length != ports.eraseDups.length then
    throw "System.emit: generated top-level port-name collision"
  let wires := internalWireNames realized.system
  if wires.length != wires.eraseDups.length ||
      wires.any (fun wire => ports.contains wire) then
    throw "System.emit: generated top-level net-name collision"

inductive ArtifactKind where
  | rtl
  | constraints
  | inventory
  deriving DecidableEq, Repr

/-- One exact text artifact and the crossing keys it covers. -/
structure EmissionArtifact where
  kind : ArtifactKind
  relativePath : System.FilePath
  text : String
  crossingKeys : List ConnectionKey

/-- Exact files emitted for a realized system.  The RTL file contains the
verified-printer island modules, selected CDC modules, and generated top. -/
def RealizedSystem.emissionArtifacts (realized : RealizedSystem) :
    List EmissionArtifact :=
  let artifacts := realized.artifacts
  let keys := artifacts.instances.map (fun artifact => artifact.key)
  let rtl := String.intercalate "\n\n" <|
    artifacts.islandModules.map (fun islandModule => islandModule.2) ++
    artifacts.instances.map (fun artifact => artifact.moduleText) ++
    [artifacts.topModule.render]
  [ { kind := .rtl, relativePath := "system.v", text := rtl, crossingKeys := keys },
    { kind := .constraints, relativePath := "clock_constraints.md",
      text := artifacts.constraintFile.renderNeutral ++
        renderResetIntents artifacts.resetIntents ++ "\n",
      crossingKeys := artifacts.constraintFile.groups.map (fun group => group.key) },
    { kind := .inventory, relativePath := "crossings.md",
      text := artifacts.inventoryText, crossingKeys := keys } ]

/-- Write the exact pure artifact values under one output directory. -/
def RealizedSystem.emit (realized : RealizedSystem) (directory : System.FilePath) : IO Unit := do
  match realized.emissionCheck with
  | .ok _ => pure ()
  | .error message => throw <| IO.userError message
  for artifact in realized.emissionArtifacts do
    let path := directory / artifact.relativePath
    let changed ← Loom.Artifact.writeText path artifact.text
    IO.println s!"{path} {if changed then "written" else "unchanged"}"

/-- The report is not reconstructed from emitted text: it is definitionally
the checked system inventory that drove physical generation. -/
@[simp] theorem RealizedSystem.artifact_inventory (realized : RealizedSystem) :
    realized.artifacts.inventory = realized.system.crossingInventory := rfl

/-- Every declared crossing has exactly one generated instance, in the same
order.  This follows from the opaque realization coverage certificate. -/
theorem RealizedSystem.instance_keys_complete (realized : RealizedSystem) :
    realized.artifacts.topModule.channelInstances.map (fun artifact => artifact.key) =
      realized.system.connections.map SystemConnection.key := by
  simp only [RealizedSystem.artifacts, List.map_map]
  exact realized.coverage

/-- Constraint generation has the identical complete domain; a group may be
empty only when its selected implementation needs no external timing intent. -/
theorem RealizedSystem.constraint_keys_complete (realized : RealizedSystem) :
    realized.artifacts.constraintFile.groups.map (fun group => group.key) =
      realized.system.connections.map SystemConnection.key := by
  simp only [RealizedSystem.artifacts, List.map_map]
  exact realized.coverage

/-- Timing inspection is generated over exactly the selected connection
domain; a realization cannot be emitted without a timing row. -/
theorem RealizedSystem.timing_keys_complete (realized : RealizedSystem) :
    realized.artifacts.timing.map (fun group => group.key) =
      realized.system.connections.map SystemConnection.key := by
  simp only [RealizedSystem.artifacts, List.map_map]
  exact realized.coverage

/-- RTL, constraints, and inventory are emitted from one complete key domain;
there is no wrapper path on which a declared crossing disappears. -/
theorem RealizedSystem.every_emitted_artifact_complete (realized : RealizedSystem)
    (artifact : EmissionArtifact) (member : artifact ∈ realized.emissionArtifacts) :
    artifact.crossingKeys =
      realized.system.connections.map SystemConnection.key := by
  simp only [RealizedSystem.emissionArtifacts, List.mem_cons] at member
  rcases member with first | second | third
  · subst artifact
    exact realized.instance_keys_complete
  · subst artifact
    exact realized.constraint_keys_complete
  · rcases third with third | impossible
    · subst artifact
      exact realized.instance_keys_complete
    · simp at impossible

end System
end Loom.Hw
