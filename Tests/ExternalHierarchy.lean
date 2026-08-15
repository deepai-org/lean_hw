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

private def graph : Except String (BoundComponentGraph CoreClock) := do
  match SealedExternal.check? specification binding with
  | .error message => throw message
  | .ok sealed =>
      match DomainExternal.check? (δ := CoreClock) sealed with
      | .error message => throw message
      | .ok component => do
          let source : ExternalInstance CoreClock := ⟨"source", component⟩
          let sink : ExternalInstance CoreClock := ⟨"sink", component⟩
          let output ← source.output? outputPort
          let input ← sink.input? inputPort
          let connection ← HierarchyConnection.typed output input
          let graph ← (BoundComponentGraph.empty (δ := CoreClock) "bound_top").addExternal source
          let graph ← graph.addExternal sink
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

#check_failure (BoundComponentGraph.connect (δ := CoreClock) :
  BoundComponentGraph CoreClock → HierarchyConnection OtherClock →
    Except String (BoundComponentGraph CoreClock))

end Tests.ExternalHierarchy
