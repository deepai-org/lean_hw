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
pipeline and arbiter, five domain-owned components form one ready/valid
network, backpressure reaches both producers, the hierarchy is certified,
the proved simulator runs the exact flattened design, and canonical RTL comes
from that same certificate.
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

private structure Selection where
  depth : Nat
  pipeline : DomainComponent CoreDomain
  merge : DomainComponent CoreDomain

private inductive CpuService : Type → Type where
  | depth : CpuService Nat
  | roundRobin : CpuService Bool
  | datapath : CpuService Selection

private instance : ServiceCatalog CpuService where
  name
    | .depth => "pipeline_depth"
    | .roundRobin => "round_robin"
    | .datapath => "datapath"
  matchKey
    | .depth, .depth => .same rfl
    | .roundRobin, .roundRobin => .same rfl
    | .datapath, .datapath => .same rfl
    | _, _ => .different
  matchKey_sound := by
    intro α β left right equal matched
    cases left <;> cases right <;> simp_all
  matchKey_refl := by
    intro α key
    cases key <;> rfl

private def configPlugin (name : String) (depth : Nat) (roundRobin : Bool) :
    Spec (κ := CpuService) where
  name
  providers :=
    [{ Value := Nat, name := "depth", key := .depth, requires := [],
       build := fun _ => .ok depth },
     { Value := Bool, name := "arbiter", key := .roundRobin, requires := [],
       build := fun _ => .ok roundRobin }]

private def datapathPlugin : Spec (κ := CpuService) where
  name := "datapath"
  providers :=
    [{ Value := Selection
       name := "build"
       key := .datapath
       requires := [Key.of .depth, Key.of .roundRobin]
       build := fun requirements => do
         let depth ← requirements.getUnique? .depth
         let roundRobin ← requirements.getUnique? .roundRobin
         let pipeline ← Pipeline.component? (δ := CoreDomain) (α := Payload)
           "execute_pipe" payloadType depth
         let merge ← mergeComponent? roundRobin
         return ⟨depth, pipeline, merge⟩ }]

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
  let firstInst : DomainComponentInstance CoreDomain := ⟨"source_a", first⟩
  let secondInst : DomainComponentInstance CoreDomain := ⟨"source_b", second⟩
  let mergeInst : DomainComponentInstance CoreDomain := ⟨"merge", selection.merge⟩
  let pipelineInst : DomainComponentInstance CoreDomain :=
    ⟨"pipeline", selection.pipeline⟩
  let sinkInst : DomainComponentInstance CoreDomain := ⟨"sink", sink⟩
  let mut graph := DomainComponentGraph.empty (δ := CoreDomain) "cpu_hierarchy_gate"
  graph ← graph.addInstance firstInst
  graph ← graph.addInstance secondInst
  graph ← graph.addInstance mergeInst
  graph ← graph.addInstance pipelineInst
  graph ← graph.addInstance sinkInst
  let firstSource ← sourcePorts.resolve firstInst
  let secondSource ← sourcePorts.resolve secondInst
  let firstSink ← mergePorts.first.resolve mergeInst
  let secondSink ← mergePorts.second.resolve mergeInst
  let mergedSource ← mergePorts.output.resolve mergeInst
  let pipelinePorts := Pipeline.componentPorts (δ := CoreDomain)
    (α := Payload) payloadType selection.depth
  let pipelineSink ← pipelinePorts.input.resolve pipelineInst
  let pipelineSource ← pipelinePorts.output.resolve pipelineInst
  let retireSink ← sinkPorts.resolve sinkInst
  graph ← Stream.connect graph firstSource firstSink
  graph ← Stream.connect graph secondSource secondSink
  graph ← Stream.connect graph mergedSource pipelineSink
  Stream.connect graph pipelineSource retireSink

private def roundRobinPlugins : List (Spec (κ := CpuService)) :=
  [configPlugin "wide_config" 3 true, datapathPlugin]

private def replacementPlugins : List (Spec (κ := CpuService)) :=
  [configPlugin "compact_config" 1 false, datapathPlugin]

#guard match selection? roundRobinPlugins with
  | .ok selected => selected.depth == 3 && selected.merge.sealed.component.name ==
      "RoundRobinMerge"
  | .error _ => false

/- Provider replacement changes the generated hierarchy without changing the
consumer plugin or service type. -/
#guard match selection? replacementPlugins with
  | .ok selected => selected.depth == 1 && selected.merge.sealed.component.name ==
      "FixedMerge"
  | .error _ => false

#guard match graphFor? roundRobinPlugins with
  | .ok graph => graph.instances.length == 5 && graph.connectionCount == 12 &&
      graph.validB && (ComponentHierarchy.checkDomain? graph).isOk
  | .error _ => false

private def runCycles (design : Design) : Nat → St
  | 0 => design.reset
  | count + 1 => design.cycle (runCycles design count)

/- The sink deliberately accepts every other cycle. After twelve cycles the
three-stage path has retired four transactions; the exact count locks
backpressure, pipeline latency, and hierarchical signal substitution together. -/
#guard match graphFor? roundRobinPlugins with
  | .error _ => false
  | .ok graph =>
      match graph.flatten? with
      | .error _ => false
      | .ok implementation =>
          (runCycles implementation.design 12).regs "sink__count" 32 == 4#32

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
