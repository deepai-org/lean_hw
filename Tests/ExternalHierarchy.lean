-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ExternalHierarchy

namespace Tests.ExternalHierarchy

open Loom.Hw

private inductive CoreClock
private instance : ClockDomain CoreClock where name := "core"
private inductive OtherClock
private instance : ClockDomain OtherClock where name := "other"

private def inputPort : Port .input CoreClock (BitVec 8) :=
  Port.bits .input 8 "input"

private def outputPort : Port .output CoreClock (BitVec 8) :=
  Port.bits .output 8 "output"

private def interface : ComponentInterface := ⟨[inputPort.decl, outputPort.decl]⟩

private def behavior : ComponentContract interface where
  State := Unit
  init := fun _ => True
  step := fun _ _ _ _ => True
  observe := fun _ _ _ _ => 0
  step_input_congr := by simp
  observe_input_congr := by intros; rfl

private def specification : ExternalComponent where
  name := "neutral_leaf"
  version := "1"
  interface := interface
  behavior := behavior
  domains := [⟨"core", .rising, .synchronous true⟩]
  combinational := [⟨"output", "input"⟩]
  latency := [⟨"output", some "input", 0, some 0⟩]

private def binding : ExternalBinding specification where
  format := .verilog
  moduleName := "neutral_leaf_impl"
  parameters := [("WIDTH", "8")]
  artifact := Loom.Artifact.Identity.ofText "module neutral_leaf_impl; endmodule\n"
  evidence := .assumptionOnly
  assumptions := [⟨"contract", "bound bytes implement neutral_leaf v1"⟩]

private def sealedExternal : SealedExternal where
  specification := specification
  specificationValid := by native_decide
  binding := binding
  bindingValid := by native_decide

private def domainExternal : DomainExternal CoreClock where
  sealed := sealedExternal
  domainOk := by native_decide

private def sourceExternal : ExternalInstance CoreClock := ⟨"source", domainExternal⟩
private def sinkExternal : ExternalInstance CoreClock := ⟨"sink", domainExternal⟩

private def internalComponent : Component where
  name := "NeutralLeafInternal"
  interface := interface
  design :=
    { name := "neutral_leaf_internal"
      regs := []
      mems := []
      inputs := [inputPort.reg.input]
      rules := []
      outputs := []
      combOutputs := [⟨outputPort.name, 8, .lit 0#8⟩] }

private def internalDomainComponent : DomainComponent CoreClock where
  sealed :=
    { component := internalComponent
      interfaceOk := by native_decide
      readsOk := by native_decide
      certified := CertifiedDesign.ofChecks (by native_decide) (by native_decide) }
  domainOk := by native_decide

private def graph : Except String (BoundComponentGraph CoreClock) := do
  let output ← sourceExternal.output? outputPort
  let input ← sinkExternal.input? inputPort
  let connection ← HierarchyConnection.typed output input
  let graph ← (BoundComponentGraph.empty (δ := CoreClock) "bound_top").addExternal sourceExternal
  let graph ← graph.addExternal sinkExternal
  graph.connect connection

#guard match graph with
  | .error _ => false
  | .ok value =>
      value.external.length == 2 && value.connections.length == 1 &&
      value.externalArtifacts.length == 2 &&
      value.externalAssumptions.map (·.name) == ["source.contract", "sink.contract"] &&
      value.emissionPlan.instances.length == 2 &&
      value.emissionPlan.instances.all (·.external) &&
      (value.emissionPlan.instances[1]?).any fun planned =>
        (planned.ports.find? (·.port == "input")).any
          (·.net == "source__output")

private def internalWitness :
    BoundComponentGraph.DesignContractWitness internalDomainComponent specification where
  interfaceEq := rfl
  abstract := fun _ => ()
  init := trivial
  tick := by intros; trivial
  reset := by intros; trivial
  hold := by intros; trivial
  observe := by
    intro input state port member
    simp [specification, ComponentInterface.outputs, interface, inputPort,
      outputPort, Port.bits, Port.decl] at member
    rcases member with ⟨rfl | rfl, direction⟩
    · exact Bool.noConfusion direction
    · change 0#8 = BoundComponentGraph.componentOutputEnv
        internalComponent input state "output" 8
      rfl

private def replacement : BoundComponentGraph.InternalReplacement sourceExternal where
  component := internalDomainComponent
  witness := internalWitness

private def substituted : Except String (BoundComponentGraph CoreClock) := do
  let original ← graph
  return (← original.substituteInternal sourceExternal replacement).graph

#guard match substituted with
  | .error _ => false
  | .ok value =>
      value.internal.length == 1 && value.external.length == 1 &&
      value.externalArtifacts.length == 1 &&
      value.externalAssumptions.map (·.name) == ["sink.contract"] &&
      value.emissionPlan.instances.any fun planned =>
        !planned.external && planned.moduleName == "neutral_leaf_internal"

#check_failure (BoundComponentGraph.connect (δ := CoreClock) :
  BoundComponentGraph CoreClock → HierarchyConnection OtherClock →
    Except String (BoundComponentGraph CoreClock))

end Tests.ExternalHierarchy
