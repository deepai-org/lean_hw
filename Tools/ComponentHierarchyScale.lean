-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ComponentHierarchy
import Loom.Hw.Pipeline

namespace Tools.ComponentHierarchyScale

open Loom.Hw

private def accepts (edges : List (String × String)) : Bool :=
  ComponentGraph.topologicalOrderCheckB edges
    (ComponentGraph.proposeTopologicalOrder edges)

private def branchingEdges (branches : Nat) : List (String × String) :=
  (List.range branches).flatMap fun index =>
    [("root", s!"left{index}"), ("root", s!"right{index}"),
     (s!"left{index}", s!"leaf{index}"),
     (s!"right{index}", s!"leaf{index}")]

private def referencePathB (edges : List (String × String)) :
    Nat → String → String → Bool
  | 0, _, _ => false
  | fuel + 1, source, target =>
      edges.any fun edge => edge.1 == source &&
        (edge.2 == target || referencePathB edges fuel edge.2 target)

private def referenceAcyclicB (edges : List (String × String)) : Bool :=
  let nodes := (edges.flatMap fun edge => [edge.1, edge.2]).eraseDups
  nodes.all fun node => !referencePathB edges nodes.length node node

private def tinyEdges : List (String × String) :=
  [("a", "a"), ("a", "b"), ("a", "c"),
   ("b", "a"), ("b", "b"), ("b", "c"),
   ("c", "a"), ("c", "b"), ("c", "c")]

private inductive ScaleDomain
private instance : ClockDomain ScaleDomain where name := "scale_clk"

private def nodeInput : Port .input ScaleDomain (BitVec 32) :=
  Port.bits .input 32 "in"

private def nodeOutput : Port .output ScaleDomain (BitVec 32) :=
  Port.bits .output 32 "out"

private def nodeComponent? : Except String (DomainComponent ScaleDomain) := do
  let component : Component :=
    { name := "ScaleNode"
      interface := ⟨[nodeInput.decl, nodeOutput.decl]⟩
      design :=
        { name := "scale_node"
          regs := []
          mems := []
          inputs := [nodeInput.reg.input]
          rules := []
          outputs := []
          combOutputs := [⟨nodeOutput.name, 32,
            .xor nodeInput.bitReg.rd (.lit 1)⟩] } }
  DomainComponent.seal? component.name component.interface
    (DomainDesign.authored component.design)

/-- A complete binary-tree hierarchy. Instance and connection insertion only
accumulates typed inventory; no topology or graph-wide scan occurs here. -/
private def componentBatch? (count : Nat) (selectedEdges : Option (List Nat) := none) :
    Except String (DomainComponentBatch ScaleDomain) := do
  if count == 0 then throw "scale hierarchy requires at least one component"
  let component ← nodeComponent?
  let mut instances : Array (DomainComponentInstance ScaleDomain) := #[]
  let mut batch := DomainComponentBatch.empty (δ := ScaleDomain) "scale_branching"
  for index in List.range count do
    let inst : DomainComponentInstance ScaleDomain := ⟨s!"node{index}", component⟩
    instances := instances.push inst
    batch := batch.addInstance inst
  for offset in List.range (count - 1) do
    let childIndex := offset + 1
    if selectedEdges.all (fun selected => selected.contains offset) then
      let parentIndex := (childIndex - 1) / 2
      let some parent := instances[parentIndex]?
        | throw "scale parent index escaped the instance inventory"
      let some child := instances[childIndex]?
        | throw "scale child index escaped the instance inventory"
      let source ← parent.output? nodeOutput
      let sink ← child.input? nodeInput
      batch := batch.connect (← Connection.typed source sink)
  return batch.expose s!"node{count - 1}" nodeOutput.name

private def timedExcept {α : Type} (label : String)
    (work : Unit → Except String α) : IO α := do
  let started ← IO.monoMsNow
  let value ← IO.ofExcept (work ())
  let finished ← IO.monoMsNow
  IO.println s!"component hierarchy scale: {label}_ms={finished - started}"
  return value

def main : IO Unit := do
  let large := branchingEdges 4096
  unless accepts large do
    throw <| IO.userError "large branching DAG was rejected"
  let exhaustive := tinyEdges.sublists.all fun edges =>
    accepts edges == referenceAcyclicB edges
  unless exhaustive do
    throw <| IO.userError "optimized topology proposal disagrees with the reference checker"

  let branchCount := 1023
  let branchingBatch ← timedExcept "batch_construction_1023" fun _ =>
    componentBatch? branchCount
  unless branchingBatch.instanceCount == branchCount &&
      branchingBatch.connectionCount == branchCount - 1 do
    throw <| IO.userError "batch builder lost a branching-hierarchy item"
  let checkedBranching ← timedExcept "batch_structural_certification_1023" fun _ =>
    ComponentHierarchy.checkBatch? branchingBatch
  unless checkedBranching.certificate.erased.order.length > 0 do
    throw <| IO.userError "batch hierarchy has an empty topological certificate"

  let flattenSelections := (List.range 3).sublists
  let flattenEquivalent ← flattenSelections.allM fun selected => do
    match componentBatch? 4 (some selected) with
    | .error _ => pure false
    | .ok batch =>
        match ComponentHierarchy.checkBatch? batch with
        | .error _ => pure false
        | .ok checked =>
            match checked.graph.flatten? with
            | .error _ => pure false
            | .ok optimized =>
                let reference := checked.graph.flattenReference
                pure <| Loom.Emit.MicroVerilog.Print.print
                    (Compile.compile optimized.design) ==
                  Loom.Emit.MicroVerilog.Print.print (Compile.compile reference.design)
  unless flattenEquivalent do
    throw <| IO.userError "optimized flattener disagrees with slow reference"

  let depth := 128
  let batch ← timedExcept "pipeline_batch_construction" fun _ => do
    let slice ← Stream.registerSlice? (δ := ScaleDomain) (α := BitVec 32)
      "scale_pipeline_stage" "ScaleWord"
    Pipeline.componentBatchOf? (δ := ScaleDomain) (α := BitVec 32)
      "scale_pipeline" "ScaleWord" (List.replicate depth slice)
  let checked ← timedExcept "pipeline_structural_certification" fun _ =>
    ComponentHierarchy.checkBatch? batch
  let graph := checked.graph
  let orderLength := checked.certificate.erased.order.length
  let implementation ← timedExcept "canonical_flatten" fun _ => graph.flatten?
  let flattenedRegisters := implementation.design.regs.length
  let renderedBytes ← timedExcept "simulator_compiler_seal" fun _ => do
    let sealed ← checked.certificate.seal?
    return sealed.certified.renderedUTF8.size
  IO.println s!"component hierarchy scale: PASS topology_edges={large.length} topology_small_graphs={tinyEdges.sublists.length} flatten_small_graphs={flattenSelections.length} branching_components={branchCount} branching_connections={branchingBatch.connectionCount} pipeline_depth={depth} pipeline_connections={graph.connectionCount} order_nodes={orderLength} flattened_registers={flattenedRegisters} rendered_bytes={renderedBytes}"

end Tools.ComponentHierarchyScale

def main : IO Unit := Tools.ComponentHierarchyScale.main
