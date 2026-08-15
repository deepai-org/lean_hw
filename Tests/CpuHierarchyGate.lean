-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Arbiter
import Loom.Hw.ComponentHierarchy
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
  let pause : Reg 1 := ⟨"pause"⟩
  let ready := .not pause.rd
  let accepted := .and sinkPorts.valid.bitReg.rd ready
  let component : Component :=
    { name := "RetireSink"
      interface := ⟨sinkPorts.decls⟩
      design :=
        { name := "retire_sink"
          regs := [count.decl 0, digest.decl 0, pause.decl 0]
          mems := []
          inputs := [sinkPorts.valid.bitReg.input, sinkPorts.payload.reg.input]
          rules :=
            [⟨"alternate_ready", pause.set (.not pause.rd)⟩,
             ⟨"retire", .ite accepted
                (.seq (count.set (.add count.rd (.lit 1)))
                  (digest.set (.xor digest.rd sinkPorts.payload.reg.rd))) .skip⟩]
          outputs := []
          combOutputs := [⟨sinkPorts.ready.name, 1, ready⟩] } }
  DomainComponent.seal? component.name component.interface
    (DomainDesign.authored component.design)

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
    Except String (DomainComponentGraph CoreDomain) := do
  let selection ← selection? plugins
  let first ← sourceComponent? "SourceA" 0x10000000
  let second ← sourceComponent? "SourceB" 0x20000000
  let sink ← sinkComponent?
  let flushController ← flushController?
  let firstInst : DomainComponentInstance CoreDomain := ⟨"source_a", first⟩
  let secondInst : DomainComponentInstance CoreDomain := ⟨"source_b", second⟩
  let mergeInst : DomainComponentInstance CoreDomain := ⟨"merge", selection.merge⟩
  let sinkInst : DomainComponentInstance CoreDomain := ⟨"sink", sink⟩
  let flushInst : DomainComponentInstance CoreDomain :=
    ⟨"flush_control", flushController⟩
  let mut graph := DomainComponentGraph.empty (δ := CoreDomain) "cpu_hierarchy_gate"
  graph ← graph.addInstance firstInst
  graph ← graph.addInstance secondInst
  graph ← graph.addInstance mergeInst
  let mut stageInstances : List (DomainComponentInstance CoreDomain) := []
  for (stage, index) in selection.stages.zipIdx do
    let stageInst : DomainComponentInstance CoreDomain :=
      ⟨s!"pipeline_{index}", stage⟩
    graph ← graph.addInstance stageInst
    stageInstances := stageInstances ++ [stageInst]
  graph ← graph.addInstance sinkInst
  graph ← graph.addInstance flushInst
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
  graph ← Stream.connect graph firstSource firstSink
  graph ← Stream.connect graph secondSource secondSink
  graph ← Stream.connect graph mergedSource pipelineSink
  for index in List.range (stageInstances.length - 1) do
    let some sourceStage := stageInstances[index]?
      | throw "pipeline source-stage indexing failure"
    let some sinkStage := stageInstances[index + 1]?
      | throw "pipeline sink-stage indexing failure"
    let source ← linkPorts.output.resolve sourceStage
    let sink ← linkPorts.input.resolve sinkStage
    graph ← Stream.connect graph source sink
  graph ← Stream.connect graph pipelineSource retireSink
  if selection.selectedFlushable then
    let some selectedStage := stageInstances[selection.selectedIndex]?
      | throw "selected pipeline stage index is out of bounds"
    let source ← flushInst.output? flushOutput
    let sink ← selectedStage.input? (Pipeline.flushPort (δ := CoreDomain))
    graph ← graph.connect (← Connection.typed source sink)
  return graph

private def roundRobinPlugins : List (Spec (κ := CpuService)) :=
  [configPlugin "flushable_config" 3 true true, datapathPlugin]

private def replacementPlugins : List (Spec (κ := CpuService)) :=
  [configPlugin "bypass_config" 3 true false, datapathPlugin]

private def fixedPlugins : List (Spec (κ := CpuService)) :=
  [configPlugin "fixed_config" 3 false false, datapathPlugin]

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
  | .ok graph => graph.instances.length == 8 && graph.connectionCount == 19 &&
      graph.validB && (ComponentHierarchy.checkDomain? graph).isOk
  | .error _ => false

private def runCycles (design : Design) : Nat → St
  | 0 => design.reset
  | count + 1 => design.cycle (runCycles design count)

/- The sink deliberately accepts every other cycle. After twelve cycles the
three-stage path has retired four transactions; the exact count locks
backpressure, pipeline latency, payload propagation, an occupied-stage flush,
and hierarchical signal substitution together. -/
#guard match graphFor? roundRobinPlugins with
  | .error _ => false
  | .ok graph =>
      match graph.flatten? with
      | .error _ => false
      | .ok implementation =>
          let beforeFlush := runCycles implementation.design 5
          let afterFlush := runCycles implementation.design 6
          let final := runCycles implementation.design 12
          beforeFlush.regs "pipeline_1__full" 1 == 1#1 &&
          afterFlush.regs "pipeline_1__full" 1 == 0#1 &&
          final.regs "sink__count" 32 == 4#32 &&
          final.regs "sink__digest" 32 == 3#32

/- Replacing only the service-provided middle link with a bypass changes
latency and removes flush loss without changing the consumer or graph builder. -/
#guard match graphFor? replacementPlugins with
  | .error _ => false
  | .ok graph =>
      match graph.flatten? with
      | .error _ => false
      | .ok implementation =>
          let final := runCycles implementation.design 12
          final.regs "sink__count" 32 == 5#32 &&
          final.regs "sink__digest" 32 == 0x10000002#32

/- Simulation and RTL share one sealed composition and one certificate. -/
#guard match graphFor? roundRobinPlugins with
  | .error _ => false
  | .ok graph =>
      match graph.seal? with
      | .error _ => false
      | .ok sealed =>
          sealed.certified.renderedVerilog.contains "module cpu_hierarchy_gate" &&
          sealed.certified.renderedVerilog.contains "sink__count"

end Tests.CpuHierarchyGate
