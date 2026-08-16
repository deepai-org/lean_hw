-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Component

/-!
# Compositional component-graph certificates

This layer is separate from `Component` deliberately: ordinary component
construction does not pay to elaborate hierarchy certification machinery.
The certificate below reuses each instance's existing `CertifiedDesign` and
checks only obligations introduced by composition. It does not compile or
prepare the monolithic flattened `Design`.
-/

namespace Loom.Hw

universe v

namespace ComponentHierarchy

/-- Small projection used by the namespace checker. Proof-heavy child
certificates and implementation syntax do not enter this trust boundary. -/
structure NamespaceShape where
  path : String
  signals : List String
  rules : List String
  deriving Repr, DecidableEq, BEq

def NamespaceShape.ofInstance (inst : ComponentInstance) : NamespaceShape :=
  let design := inst.component.component.design
  { path := inst.path
    signals := design.names ++ design.combOutputs.map (·.name)
    rules := design.rules.map (·.name) }

/-- Distinct paths alone are insufficient: `a.b__c` and `a__b.c` can flatten
to the same name. Check the actual derived signal and rule namespaces. -/
def namespacesDisjointB (instances : List NamespaceShape) : Bool :=
  let signals := instances.flatMap fun inst =>
    inst.signals.map (inst.path ++ "__" ++ ·)
  let rules := instances.flatMap fun inst =>
    inst.rules.map (inst.path ++ "__" ++ ·)
  signals.eraseDups.length == signals.length &&
    rules.eraseDups.length == rules.length

def graphNamespacesDisjointB (graph : ComponentGraph) : Bool :=
  namespacesDisjointB (graph.instances.map NamespaceShape.ofInstance)

/-- A graph certificate containing only newly introduced composition facts.
Child compiler/simulator certificates remain available directly from every
`graph.instances` entry. -/
structure Certificate (graph : ComponentGraph) where
  nameValid : (!graph.name.isEmpty) = true
  pathsUnique : graph.pathsUniqueB = true
  connectionsValid : graph.connectionsValidB = true
  exportBoundaryValid : graph.exportsValidB = true
  namespacesDisjoint : graphNamespacesDisjointB graph = true
  order : List String
  order_eq : order = ComponentGraph.proposeTopologicalOrder graph.dependencyEdges
  topology : ComponentGraph.topologicalOrderCheckB graph.dependencyEdges order = true

namespace Certificate

theorem graphValid {graph : ComponentGraph} (certificate : Certificate graph) :
    graph.validB = true := by
  unfold ComponentGraph.validB ComponentGraph.combinationalAcyclicB
  change (!graph.name.isEmpty && graph.pathsUniqueB &&
    graph.connectionsValidB && graph.exportsValidB &&
    ComponentGraph.topologicalOrderCheckB graph.dependencyEdges
      (ComponentGraph.proposeTopologicalOrder graph.dependencyEdges)) = true
  rw [← certificate.order_eq]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨certificate.nameValid, certificate.pathsUnique⟩,
    certificate.connectionsValid⟩, certificate.exportBoundaryValid⟩,
    certificate.topology⟩

/-- Child compiler/simulator evidence is reused verbatim rather than derived
again from the flattened design. -/
def childCertified {graph : ComponentGraph} (_certificate : Certificate graph)
    (inst : ComponentInstance) (_member : inst ∈ graph.instances) :
    CertifiedDesign inst.component.component.design :=
  inst.component.certified

theorem dependencyAcyclic {graph : ComponentGraph} (certificate : Certificate graph) :
    ComponentGraph.DependencyAcyclic graph.dependencyEdges :=
  ComponentGraph.topologicalOrderCheckB_sound certificate.topology

/-- Every stored substitution still names an output and input of the certified
children with the checked width, semantic payload name, and clock domain. -/
theorem connectionValid {graph : ComponentGraph} (certificate : Certificate graph)
    {connection : Connection} (member : connection ∈ graph.connections) :
    graph.connectionValidB connection = true := by
  have valid := certificate.connectionsValid
  simp only [ComponentGraph.connectionsValidB, Bool.and_eq_true] at valid
  exact List.all_eq_true.mp valid.1 connection member

/-- Every exported coordinate belongs to an output of the named child. This
is the final hierarchy boundary obligation; unlisted child outputs remain
internal after lowering. -/
theorem exportValid {graph : ComponentGraph} (certificate : Certificate graph)
    {exposed : String × String} (member : exposed ∈ graph.exports) :
    (match graph.findInstance? exposed.1 with
      | none => false
      | some inst => (inst.findPort? .output exposed.2).isSome) = true := by
  exact List.all_eq_true.mp certificate.exportBoundaryValid exposed member

/-- Prepare compiler and simulator evidence without executing any structural
graph obligation again. The structural premise is derived from this exact
certificate; only checks about the newly flattened scalar Design remain. -/
def seal? {graph : ComponentGraph} (certificate : Certificate graph) :
    Except String (ComponentGraph.Sealed graph) := do
  let hGraph := certificate.graphValid
  graph.flatten.emitCheck
  if hReads : graph.flatten.readsOkB = true then
    if hCompiler : Compile.designWFCheck graph.flatten = true then
      if hSimulator : graph.flatten.fastWFB = true then
        return { graphValid := hGraph
                 readsOk := hReads
                 certified := CertifiedDesign.ofChecks hCompiler hSimulator }
      throw s!"component graph '{graph.name}' is not simulator-ready"
    throw s!"component graph '{graph.name}' is not compiler-ready"
  throw s!"component graph '{graph.name}' contains an undeclared or wrong-width read"

end Certificate

def check? (graph : ComponentGraph) : Except String (Certificate graph) := do
  if hName : (!graph.name.isEmpty) = true then
    if hPaths : graph.pathsUniqueB = true then
      if hConnections : graph.connectionsValidB = true then
        if hExports : graph.exportsValidB = true then
          if hNamespaces : graphNamespacesDisjointB graph = true then
            let order := ComponentGraph.proposeTopologicalOrder graph.dependencyEdges
            if hTopology : ComponentGraph.topologicalOrderCheckB
                graph.dependencyEdges order = true then
              return ⟨hName, hPaths, hConnections, hExports,
                hNamespaces, order, rfl, hTopology⟩
            throw s!"component graph '{graph.name}' has no checked topological order"
          throw s!"component graph '{graph.name}' has colliding flattened namespaces"
        throw s!"component graph '{graph.name}' has an invalid export boundary"
      throw s!"component graph '{graph.name}' has an invalid connection substitution"
    throw s!"component graph '{graph.name}' has duplicate instance paths"
  throw "component graph name must not be empty"

structure DomainCertificate {δ : Type v} [ClockDomain δ]
    (graph : DomainComponentGraph δ) where
  erased : Certificate graph.raw

def checkDomain? {δ : Type v} [ClockDomain δ] (graph : DomainComponentGraph δ) :
    Except String (DomainCertificate graph) :=
  DomainCertificate.mk <$> check? graph.raw

def DomainCertificate.seal? {δ : Type v} [ClockDomain δ]
    {graph : DomainComponentGraph δ} (certificate : DomainCertificate graph) :
    Except String (ComponentGraph.Sealed graph.raw) :=
  certificate.erased.seal?

/-- A batch sealed exactly once. The graph is retained beside the certificate
so later flattening, simulation preparation, and compilation consume the same
checked inventory rather than rebuilding or revalidating it. -/
structure CheckedBatch (δ : Type v) [ClockDomain δ] where
  graph : DomainComponentGraph δ
  certificate : DomainCertificate graph

def checkBatch? {δ : Type v} [ClockDomain δ] (batch : DomainComponentBatch δ) :
    Except String (CheckedBatch δ) := do
  let graph := DomainComponentBatch.Expert.materialize batch
  let certificate ← checkDomain? graph
  return ⟨graph, certificate⟩

end ComponentHierarchy

end Loom.Hw
