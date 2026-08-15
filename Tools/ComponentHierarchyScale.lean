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
  let depth := 128
  let graph ← timedExcept "construction" fun _ =>
    Pipeline.componentGraph? (δ := ScaleDomain) (α := BitVec 32)
      "scale_pipeline" "ScaleWord" depth
  let orderLength ← timedExcept "structural_certification" fun _ => do
    let certificate ← ComponentHierarchy.checkDomain? graph
    return certificate.erased.order.length
  let implementation ← timedExcept "canonical_flatten" fun _ => graph.flatten?
  let flattenedRegisters := implementation.design.regs.length
  let renderedBytes ← timedExcept "simulator_compiler_seal" fun _ => do
    let sealed ← graph.seal?
    return sealed.certified.renderedUTF8.size
  IO.println s!"component hierarchy scale: PASS edges={large.length} small_graphs={tinyEdges.sublists.length} pipeline_depth={depth} connections={graph.connectionCount} order_nodes={orderLength} flattened_registers={flattenedRegisters} rendered_bytes={renderedBytes}"

end Tools.ComponentHierarchyScale

def main : IO Unit := Tools.ComponentHierarchyScale.main
