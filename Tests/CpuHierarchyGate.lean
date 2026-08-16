-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Arbiter
import Loom.Hw.ComponentHierarchy
import Loom.Hw.ExternalHierarchy
import Loom.Hw.Pipeline
import Loom.Hw.Plugin

/-!
# CPU-scale typed-hierarchy integration gate

This is intentionally smaller than a processor, but it crosses the pressure
points that isolated unit tests miss: deterministic plugins select a concrete
pipeline link and arbiter, domain-owned components form one ready/valid
network, backpressure reaches both producers, a typed flush discards an
occupied stage, a provider replacement supplies a bypass, the hierarchy is
certified, the proved simulator runs the exact flattened design, and canonical
RTL comes from that same certificate.
-/

namespace Tests.CpuHierarchyGate

open Loom.Hw
open Loom.Hw.Plugin

private inductive CoreDomain
private instance : ClockDomain CoreDomain where name := "core_clk"

private abbrev Payload := BitVec 32
private def payloadType := "CpuTransaction"

private def sourcePorts : Stream.SourcePorts CoreDomain Payload :=
  Stream.sourcePorts "out" payloadType

private def sourceComponent? (name : String) (tag : BitVec 32) :
    Except String (DomainComponent CoreDomain) := do
  let sequence : Reg 32 := ⟨"sequence"⟩
  let valid : Expr 1 := .ult sequence.rd (.lit 16)
  let accepted := .and valid sourcePorts.ready.bitReg.rd
  let component : Component :=
    { name
      interface := ⟨sourcePorts.decls⟩
      design :=
        { name
          regs := [sequence.decl 0]
          mems := []
          inputs := [sourcePorts.ready.bitReg.input]
          rules := [⟨"advance", .ite accepted
            (sequence.set (.add sequence.rd (.lit 1))) .skip⟩]
          outputs := []
          combOutputs :=
            [⟨sourcePorts.valid.name, 1, valid⟩,
             ⟨sourcePorts.payload.name, 32, .xor sequence.rd (.lit tag)⟩] } }
  DomainComponent.seal? component.name component.interface
    (DomainDesign.authored component.design)

private structure MergePorts where
  first : Stream.SinkPorts CoreDomain Payload
  second : Stream.SinkPorts CoreDomain Payload
  output : Stream.SourcePorts CoreDomain Payload

private def mergePorts : MergePorts :=
  { first := Stream.sinkPorts "first" payloadType
    second := Stream.sinkPorts "second" payloadType
    output := Stream.sourcePorts "out" payloadType }

private def mergeComponent? (roundRobin : Bool) :
    Except String (DomainComponent CoreDomain) := do
  let turn : Reg 1 := ⟨"turn"⟩
  let request0 := mergePorts.first.valid.bitReg.rd
  let request1 := mergePorts.second.valid.bitReg.rd
  let (grant0, grant1, update) :=
    if roundRobin then
      let arbiter : Arbiter.TwoWayRoundRobin := ⟨turn⟩
      let result := arbiter.grants request0 request1
      (result.grant0, result.grant1,
        arbiter.advance result mergePorts.output.ready.bitReg.rd)
    else
      let grant0 := request0
      let grant1 := .and request1 (.not request0)
      (grant0, grant1, Act.skip)
  let valid := .or grant0 grant1
  let payload := .mux grant0 mergePorts.first.payload.reg.rd
    (.mux grant1 mergePorts.second.payload.reg.rd (.lit 0))
  let component : Component :=
    { name := if roundRobin then "RoundRobinMerge" else "FixedMerge"
      interface := ⟨mergePorts.first.decls ++ mergePorts.second.decls ++
        mergePorts.output.decls⟩
      design :=
        { name := if roundRobin then "round_robin_merge" else "fixed_merge"
          regs := if roundRobin then [turn.decl 0] else []
          mems := []
          inputs :=
            [mergePorts.first.valid.bitReg.input,
             mergePorts.first.payload.reg.input,
             mergePorts.second.valid.bitReg.input,
             mergePorts.second.payload.reg.input,
             mergePorts.output.ready.bitReg.input]
          rules := if roundRobin then [⟨"rotate", update⟩] else []
          outputs := []
          combOutputs :=
            [⟨mergePorts.first.ready.name, 1,
              .and mergePorts.output.ready.bitReg.rd grant0⟩,
             ⟨mergePorts.second.ready.name, 1,
              .and mergePorts.output.ready.bitReg.rd grant1⟩,
             ⟨mergePorts.output.valid.name, 1, valid⟩,
             ⟨mergePorts.output.payload.name, 32, payload⟩] } }
  DomainComponent.seal? component.name component.interface
    (DomainDesign.authored component.design)

private def sinkPorts : Stream.SinkPorts CoreDomain Payload :=
  Stream.sinkPorts "in" payloadType

private def sinkComponent? : Except String (DomainComponent CoreDomain) := do
  let count : Reg 32 := ⟨"count"⟩
  let digest : Reg 32 := ⟨"digest"⟩
  let ledger : Reg 32 := ⟨"ledger"⟩
  let pause : Reg 1 := ⟨"pause"⟩
  let ready := .not pause.rd
  let accepted := .and sinkPorts.valid.bitReg.rd ready
  let component : Component :=
    { name := "RetireSink"
      interface := ⟨sinkPorts.decls⟩
      design :=
        { name := "retire_sink"
          regs := [count.decl 0, digest.decl 0, ledger.decl 0, pause.decl 0]
          mems := []
          inputs := [sinkPorts.valid.bitReg.input, sinkPorts.payload.reg.input]
          rules :=
            [⟨"alternate_ready", pause.set (.not pause.rd)⟩,
             ⟨"retire", .ite accepted
                (.seq (count.set (.add count.rd (.lit 1)))
                  (.seq (digest.set (.xor digest.rd sinkPorts.payload.reg.rd))
                    (ledger.set (.add (.mul ledger.rd (.lit 33))
                      sinkPorts.payload.reg.rd)))) .skip⟩]
          outputs := []
          combOutputs := [⟨sinkPorts.ready.name, 1, ready⟩] } }
  DomainComponent.seal? component.name component.interface
    (DomainDesign.authored component.design)

private def memoryInput : Port .input CoreDomain (BitVec 32) :=
  ⟨"write_data", payloadType⟩

private def memoryOutput : Port .output CoreDomain (BitVec 32) :=
  ⟨"read_data", payloadType⟩

private def memoryInterface : ComponentInterface :=
  ⟨[memoryInput.decl, memoryOutput.decl]⟩

private def memoryComponent : Component :=
  let address : Reg 4 := ⟨"address"⟩
  let storage : Mem 4 32 := ⟨"storage"⟩
  { name := "CpuMemoryService"
    interface := memoryInterface
    design :=
      { name := "cpu_memory_service"
        regs := [address.decl 0]
        mems := [storage.decl]
        inputs := [memoryInput.bitReg.input]
        rules := [⟨"write_and_advance",
          .seq (storage.write 0 address.rd memoryInput.bitReg.rd)
            (address.set (.add address.rd (.lit 1)))⟩]
        outputs := []
        combOutputs := [⟨memoryOutput.name, 32, storage.rd address.rd⟩] } }

private def memoryDomainComponent : DomainComponent CoreDomain where
  implementation := DomainDesign.authored memoryComponent.design
  sealed :=
    { component := memoryComponent
      interfaceOk := by native_decide
      readsOk := by native_decide
      certified := CertifiedDesign.ofChecks (by native_decide) (by native_decide) }
  implementationEq := rfl
  domainOk := by native_decide

/- The external contract deliberately abstracts the implementation state but
retains the exact interface and observation function. The same internal memory
used by the CPU graph can therefore discharge this leaf without changing its
client connection. -/
private def memoryBehavior : ComponentContract memoryInterface where
  State := St
  init := fun _ => True
  step := fun _ _ _ _ => True
  observe := fun input state =>
    BoundComponentGraph.componentOutputEnv memoryComponent input state
  step_input_congr := by intros; trivial
  observe_input_congr := by
    intro state left right _agree port member
    simp [ComponentInterface.outputs, memoryInterface, memoryInput,
      memoryOutput, Port.decl] at member
    rcases member with ⟨rfl | rfl, direction⟩
    · exact Bool.noConfusion direction
    · change BoundComponentGraph.componentOutputEnv memoryComponent left state
          "read_data" 32 =
        BoundComponentGraph.componentOutputEnv memoryComponent right state
          "read_data" 32
      rfl

private def memorySpecification : ExternalComponent where
  name := "cpu_memory_contract"
  version := "1"
  interface := memoryInterface
  behavior := memoryBehavior
  domains := [⟨"core_clk", .rising, .synchronous true⟩]
  combinational := [⟨memoryOutput.name, memoryInput.name⟩]
  latency := [⟨memoryOutput.name, some memoryInput.name, 0, some 0⟩]

private def memoryBinding : ExternalBinding memorySpecification where
  format := .verilog
  moduleName := "cpu_memory_macro"
  parameters := [("WORDS", "16"), ("WIDTH", "32")]
  artifact := Loom.Artifact.Identity.ofText "module cpu_memory_macro; endmodule\n"
  evidence := .assumptionOnly
  assumptions := [⟨"memory_contract", "bound bytes implement cpu_memory_contract v1"⟩]

private def sealedMemoryExternal : SealedExternal where
  specification := memorySpecification
  specificationValid := by native_decide
  binding := memoryBinding
  bindingValid := by native_decide

private def domainMemoryExternal : DomainExternal CoreDomain where
  sealed := sealedMemoryExternal
  domainOk := by native_decide

private def memoryExternalInstance : ExternalInstance CoreDomain :=
  ⟨"memory", domainMemoryExternal⟩

private def memoryWitness : BoundComponentGraph.DesignContractWitness
    memoryDomainComponent memorySpecification where
  interfaceEq := rfl
  abstract := fun state => state
  init := trivial
  tick := by intros; trivial
  reset := by intros; trivial
  hold := by intros; trivial
  observe := by
    intro input state port member
    rfl

private def memoryReplacement :
    BoundComponentGraph.InternalReplacement memoryExternalInstance where
  component := memoryDomainComponent
  witness := memoryWitness

private def flushOutput : Port .output CoreDomain (BitVec 1) :=
  Port.bits .output 1 "flush"

/-- A deterministic one-cycle squash pulse. Keeping it as an ordinary
component makes the flush dependency part of the same typed hierarchy. -/
private def flushController? : Except String (DomainComponent CoreDomain) := do
  let tick : Reg 4 := ⟨"tick"⟩
  let component : Component :=
    { name := "FlushController"
      interface := ⟨[flushOutput.decl]⟩
      design :=
        { name := "flush_controller"
          regs := [tick.decl 0]
          mems := []
          inputs := []
          rules := [⟨"advance", tick.set (.add tick.rd (.lit 1))⟩]
          outputs := []
          combOutputs := [⟨flushOutput.name, 1, .eq tick.rd (.lit 5)⟩] } }
  DomainComponent.seal? component.name component.interface
    (DomainDesign.authored component.design)

private structure Selection where
  depth : Nat
  stages : List (DomainComponent CoreDomain)
  selectedIndex : Nat
  selectedFlushable : Bool
  merge : DomainComponent CoreDomain

private inductive CpuService : Type → Type where
  | depth : CpuService Nat
  | roundRobin : CpuService Bool
  | flushable : CpuService Bool
  | datapath : CpuService Selection

private instance : ServiceCatalog CpuService where
  name
    | .depth => "pipeline_depth"
    | .roundRobin => "round_robin"
    | .flushable => "flushable_stage"
    | .datapath => "datapath"
  matchKey
    | .depth, .depth => .same rfl
    | .roundRobin, .roundRobin => .same rfl
    | .flushable, .flushable => .same rfl
    | .datapath, .datapath => .same rfl
    | _, _ => .different
  matchKey_sound := by
    intro α β left right equal matched
    cases left <;> cases right <;> simp_all
  matchKey_refl := by
    intro α key
    cases key <;> rfl

private def configPlugin (name : String) (depth : Nat) (roundRobin flushable : Bool) :
    Spec (κ := CpuService) where
  name
  providers :=
    [{ Value := Nat, name := "depth", key := .depth, requires := [],
       build := fun _ => .ok depth },
     { Value := Bool, name := "arbiter", key := .roundRobin, requires := [],
       build := fun _ => .ok roundRobin },
     { Value := Bool, name := "selected_stage", key := .flushable, requires := [],
       build := fun _ => .ok flushable }]

private def datapathPlugin : Spec (κ := CpuService) where
  name := "datapath"
  providers :=
    [{ Value := Selection
       name := "build"
       key := .datapath
       requires := [Key.of .depth, Key.of .roundRobin, Key.of .flushable]
       build := fun requirements => do
         let depth ← requirements.getUnique? .depth
         let roundRobin ← requirements.getUnique? .roundRobin
         let useFlushable ← requirements.getUnique? .flushable
         if depth == 0 then throw "CPU datapath requires at least one pipeline link"
         let registered ← Stream.registerSlice? (δ := CoreDomain) (α := Payload)
           "execute_registered" payloadType
         let selected ← if useFlushable then
             Pipeline.flushableComponent? (δ := CoreDomain) (α := Payload)
               "execute_flushable" payloadType
           else
             Pipeline.bypassComponent? (δ := CoreDomain) (α := Payload)
               "execute_bypass" payloadType
         let selectedIndex := depth / 2
         let stages := (List.replicate selectedIndex registered) ++ [selected] ++
           List.replicate (depth - selectedIndex - 1) registered
         let merge ← mergeComponent? roundRobin
         return ⟨depth, stages, selectedIndex, useFlushable, merge⟩ }]

private def selection? (plugins : List (Spec (κ := CpuService))) :
    Except String Selection :=
  match resolve? plugins with
  | .error message => .error message
  | .ok resolved => Resolved.getUnique? resolved .datapath

private def graphFor? (plugins : List (Spec (κ := CpuService))) :
    Except String (ComponentHierarchy.CheckedBatch CoreDomain) := do
  let selection ← selection? plugins
  let first ← sourceComponent? "SourceA" 0x10000000
  let second ← sourceComponent? "SourceB" 0x20000000
  let sink ← sinkComponent?
  let flushController ← flushController?
  let firstInst : DomainComponentInstance CoreDomain := ⟨"source_a", first⟩
  let secondInst : DomainComponentInstance CoreDomain := ⟨"source_b", second⟩
  let mergeInst : DomainComponentInstance CoreDomain := ⟨"merge", selection.merge⟩
  let sinkInst : DomainComponentInstance CoreDomain := ⟨"sink", sink⟩
  let memoryInst : DomainComponentInstance CoreDomain :=
    ⟨"memory", memoryDomainComponent⟩
  let flushInst : DomainComponentInstance CoreDomain :=
    ⟨"flush_control", flushController⟩
  let mut batch := DomainComponentBatch.empty (δ := CoreDomain) "cpu_hierarchy_gate"
  batch := batch.addInstance firstInst
  batch := batch.addInstance secondInst
  batch := batch.addInstance mergeInst
  let mut stageInstances : List (DomainComponentInstance CoreDomain) := []
  for (stage, index) in selection.stages.zipIdx do
    let stageInst : DomainComponentInstance CoreDomain :=
      ⟨s!"pipeline_{index}", stage⟩
    batch := batch.addInstance stageInst
    stageInstances := stageInstances ++ [stageInst]
  batch := batch.addInstance sinkInst
  batch := batch.addInstance memoryInst
  batch := batch.addInstance flushInst
  let firstSource ← sourcePorts.resolve firstInst
  let secondSource ← sourcePorts.resolve secondInst
  let firstSink ← mergePorts.first.resolve mergeInst
  let secondSink ← mergePorts.second.resolve mergeInst
  let mergedSource ← mergePorts.output.resolve mergeInst
  let linkPorts := Pipeline.linkPorts (δ := CoreDomain) (α := Payload)
    payloadType
  let some firstStage := stageInstances.head?
    | throw "plugin produced an empty CPU pipeline"
  let some lastStage := stageInstances.getLast?
    | throw "plugin produced an empty CPU pipeline"
  let pipelineSink ← linkPorts.input.resolve firstStage
  let pipelineSource ← linkPorts.output.resolve lastStage
  let retireSink ← sinkPorts.resolve sinkInst
  let memorySink ← memoryInst.input? memoryInput
  batch ← Stream.connectBatch batch firstSource firstSink
  batch ← Stream.connectBatch batch secondSource secondSink
  batch ← Stream.connectBatch batch mergedSource pipelineSink
  for index in List.range (stageInstances.length - 1) do
    let some sourceStage := stageInstances[index]?
      | throw "pipeline source-stage indexing failure"
    let some sinkStage := stageInstances[index + 1]?
      | throw "pipeline sink-stage indexing failure"
    let source ← linkPorts.output.resolve sourceStage
    let sink ← linkPorts.input.resolve sinkStage
    batch ← Stream.connectBatch batch source sink
  batch ← Stream.connectBatch batch pipelineSource retireSink
  batch := batch.connect (← Connection.typed firstSource.payload memorySink)
  if selection.selectedFlushable then
    let some selectedStage := stageInstances[selection.selectedIndex]?
      | throw "selected pipeline stage index is out of bounds"
    let source ← flushInst.output? flushOutput
    let sink ← selectedStage.input? (Pipeline.flushPort (δ := CoreDomain))
    batch := batch.connect (← Connection.typed source sink)
  ComponentHierarchy.checkBatch? batch

private def roundRobinPlugins : List (Spec (κ := CpuService)) :=
  [configPlugin "flushable_config" 3 true true, datapathPlugin]

private def replacementPlugins : List (Spec (κ := CpuService)) :=
  [configPlugin "bypass_config" 3 true false, datapathPlugin]

private def fixedPlugins : List (Spec (κ := CpuService)) :=
  [configPlugin "fixed_config" 3 false false, datapathPlugin]

/- The CPU source is an unchanged client of either the contracted memory leaf
or the exact internal memory component used in `graphFor?`. -/
private def substitutedMemoryHierarchy? :
    Except String (BoundComponentGraph CoreDomain) :=
  (sourceComponent? "SourceA" 0x10000000).bind fun clientComponent => do
  let sourceInst : DomainComponentInstance CoreDomain := ⟨"source_a", clientComponent⟩
  let sourceEndpoint : OutputEndpoint CoreDomain Payload :=
    { instancePath := sourceInst.path
      componentName := clientComponent.sealed.component.name
      port := sourcePorts.payload
      expression := .lit 0 }
  let memoryEndpoint ← memoryExternalInstance.input? memoryInput
  let connection ← HierarchyConnection.typed
    (HierarchyOutput.ofInternal sourceEndpoint) memoryEndpoint
  let graph ← (BoundComponentGraph.empty (δ := CoreDomain)
    "cpu_memory_substitution").addInternal sourceInst
  let graph ← graph.addExternal memoryExternalInstance
  let graph ← graph.connect connection
  return (← graph.substituteInternal memoryExternalInstance memoryReplacement).graph

#guard match selection? roundRobinPlugins with
  | .ok selected => selected.depth == 3 && selected.stages.length == 3 &&
      selected.selectedIndex == 1 && selected.selectedFlushable &&
      selected.stages[1]?.map (fun stage => stage.sealed.component.name) ==
        some "execute_flushable" &&
      selected.merge.sealed.component.name == "RoundRobinMerge"
  | .error _ => false

/- Provider replacement changes the generated hierarchy without changing the
consumer plugin or service type. -/
#guard match selection? replacementPlugins with
  | .ok selected => selected.depth == 3 && selected.stages.length == 3 &&
      !selected.selectedFlushable &&
      selected.stages[1]?.map (fun stage => stage.sealed.component.name) ==
        some "execute_bypass" &&
      selected.merge.sealed.component.name == "RoundRobinMerge"
  | .error _ => false

#guard match selection? fixedPlugins with
  | .ok selected => selected.merge.sealed.component.name == "FixedMerge" &&
      !selected.selectedFlushable
  | .error _ => false

#guard match graphFor? roundRobinPlugins with
  | .ok checked => checked.graph.instances.length == 9 &&
      checked.graph.connectionCount == 20 && checked.certificate.erased.order.length > 0
  | .error _ => false

#guard match substitutedMemoryHierarchy? with
  | .error _ => false
  | .ok graph =>
      graph.internal.length == 2 && graph.external.isEmpty &&
      graph.connections.length == 1 && graph.externalArtifacts.isEmpty &&
      graph.externalAssumptions.isEmpty &&
      graph.emissionPlan.instances.any fun planned =>
        planned.path == "memory" && !planned.external &&
          planned.moduleName == memoryComponent.design.name

private def runCycles (design : Design) : Nat → St
  | 0 => design.reset
  | count + 1 => design.cycle (runCycles design count)

/- The sink deliberately accepts every other cycle. After twelve cycles the
three-stage path has retired four transactions; the exact count locks
backpressure, pipeline latency, payload propagation, an occupied-stage flush,
and hierarchical signal substitution together. -/
#guard match graphFor? roundRobinPlugins with
  | .error _ => false
  | .ok checked =>
      match checked.graph.flatten? with
      | .error _ => false
      | .ok implementation =>
          let beforeFlush := runCycles implementation.design 5
          let afterFlush := runCycles implementation.design 6
          let final := runCycles implementation.design 12
          beforeFlush.regs "pipeline_1__full" 1 == 1#1 &&
          afterFlush.regs "pipeline_1__full" 1 == 0#1 &&
          final.mems "memory__storage" 0 32 == 0x10000000#32 &&
          final.regs "sink__count" 32 == 4#32 &&
          final.regs "sink__digest" 32 == 3#32 &&
          final.regs "sink__ledger" 32 == 0x60000023#32

/- Replacing only the service-provided middle link with a bypass changes
latency and removes flush loss without changing the consumer or graph builder. -/
#guard match graphFor? replacementPlugins with
  | .error _ => false
  | .ok checked =>
      match checked.graph.flatten? with
      | .error _ => false
      | .ok implementation =>
          let final := runCycles implementation.design 12
          final.regs "sink__count" 32 == 5#32 &&
          final.regs "sink__digest" 32 == 0x10000002#32 &&
          final.regs "sink__ledger" 32 == 0x70000464#32

/- Semantic simulation and certified RTL generation share one sealed
composition and one certificate. This is not an independent RTL execution
claim. -/
#guard match graphFor? roundRobinPlugins with
  | .error _ => false
  | .ok checked =>
      match checked.certificate.seal? with
      | .error _ => false
      | .ok sealed =>
          sealed.certified.renderedVerilog.contains "module cpu_hierarchy_gate" &&
          sealed.certified.renderedVerilog.contains "sink__count"

end Tests.CpuHierarchyGate
