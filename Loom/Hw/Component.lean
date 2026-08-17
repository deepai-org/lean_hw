-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.CertifiedDesign
import Loom.Hw.Compose
import Loom.Hw.EmitIO
import Loom.Hw.Hierarchy
import Loom.Hw.Packed

/-!
# Typed component hierarchy

This module is the technology-neutral hierarchy boundary.  Components retain
typed ports and stable instance paths while their internal implementation is
still one ordinary `Design`.  `ComponentGraph.flatten?` is the only lowering:
it prefixes, composes, and connects those Designs with the existing verified
core operations.  There is no second circuit semantics.

The first layer deliberately handles internal Loom components only.  External
leaves use the adjacent contract layer rather than smuggling HDL text into a
component body.
-/

namespace Loom.Hw

universe u v

/-- Erased, inspectable form of a typed port.  `semanticType` preserves nominal
meaning after the Lean payload type is erased for heterogeneous interface
storage. -/
structure PortDecl where
  name : String
  direction : PortDirection
  width : Nat
  semanticType : String
  domain : String
  deriving Repr, DecidableEq, BEq

/-- One canonical artifact name for a phantom clock-domain type.  The type is
the connection authority; the name is only its erased diagnostic/emission
identity. -/
class ClockDomain (δ : Type v) where
  name : String

/-- A nominally typed component port.  Connections constructed from `Port`
values can only join the same Lean payload and clock-domain types;
`PortDecl` keeps enough information to validate imported or dynamically
assembled graphs after those types are erased. -/
structure Port (direction : PortDirection) (δ : Type v) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  name : String
  semanticType : String

namespace Port

variable {direction : PortDirection} {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α]

def decl (port : Port direction δ α) : PortDecl :=
  ⟨port.name, direction, HwPacked.width α, port.semanticType,
    ClockDomain.name δ⟩

/-- The scalar core handle is derived from the typed boundary declaration. -/
def reg (port : Port direction δ α) : Reg (HwPacked.width α) := ⟨port.name⟩

/-- A bit-vector port retains its literal width in the handle type.  Keeping
this specialization avoids asking later proofs to reduce an erased
`HwPacked.width` projection merely to recover `w`. -/
def bitReg {w : Nat} (port : Port direction δ (BitVec w)) : Reg w := ⟨port.name⟩

/-- Canonical scalar bit-vector port.  Packed records should use a stable
semantic name chosen by their declaration generator. -/
def bits (direction : PortDirection) (width : Nat) (name : String) :
    Port direction δ (BitVec width) :=
  ⟨name, s!"BitVec[{width}]"⟩

end Port

/-- Complete boundary of one component.  Port order is retained for stable
emission, but names are globally unique across both directions. -/
structure ComponentInterface where
  ports : List PortDecl
  deriving Repr, DecidableEq, BEq

namespace ComponentInterface

def inputs (interface : ComponentInterface) : List PortDecl :=
  interface.ports.filter (·.direction == .input)

def outputs (interface : ComponentInterface) : List PortDecl :=
  interface.ports.filter (·.direction == .output)

def namesUniqueB (interface : ComponentInterface) : Bool :=
  Inventory.uniqueB (interface.ports.map (·.name))

def locallyValidB (interface : ComponentInterface) : Bool :=
  interface.namesUniqueB &&
    interface.ports.all fun port =>
      !port.name.isEmpty && !port.semanticType.isEmpty &&
        !port.domain.isEmpty && port.width > 0

def contains (interface : ComponentInterface) (port : PortDecl) : Bool :=
  interface.ports.contains port

end ComponentInterface

private def samePortShape (port : PortDecl)
    (name : String) (width : Nat) (direction : PortDirection) : Bool :=
  port.name == name && port.width == width && port.direction == direction

/-- One internal Loom component.  `interface` may retain nominal packed types,
while `design` remains the durable scalar core implementation. -/
structure Component where
  name : String
  interface : ComponentInterface
  design : Design

namespace Component

private def expressionReads : {w : Nat} → Expr w → List String
  | _, .lit _ => []
  | _, .reg _ name => [name]
  | _, .memRead _ _ address => expressionReads address
  | _, .and left right | _, .or left right | _, .xor left right
  | _, .add left right | _, .sub left right | _, .mul left right
  | _, .udiv left right | _, .urem left right
  | _, .shl left right | _, .shr left right
  | _, .eq left right | _, .ult left right | _, .slt left right =>
      expressionReads left ++ expressionReads right
  | _, .not value => expressionReads value
  | _, .mux condition yes no =>
      expressionReads condition ++ expressionReads yes ++ expressionReads no
  | _, .slice value _ _ | _, .zext value _ | _, .sext value _ =>
      expressionReads value

/-- Direct input-to-combinational-output dependencies. State outputs have no
same-cycle dependency edge. Expressions are already fully expanded Loom
trees, so this relation is exact rather than inferred from naming. -/
def combinationalDependencies (component : Component) : List (String × String) :=
  let inputNames := component.design.inputs.map (·.name)
  component.design.combOutputs.flatMap fun output =>
    (expressionReads output.value).eraseDups.filterMap fun input =>
      if inputNames.contains input then some (input, output.name) else none

/-- The scalar shape exported by the underlying Design. -/
def designPortShapes (component : Component) : List (String × Nat × PortDirection) :=
  component.design.inputs.map (fun input => (input.name, input.width, .input)) ++
  component.design.exportedRegs.map
    (fun reg => (reg.name, reg.width, .output)) ++
  component.design.combOutputs.map
    (fun output => (output.name, output.width, .output))

/-- Exact interface/implementation correspondence.  A nominal type may refine
the scalar bits, but every Design port occurs exactly once at the same width
and direction and no interface-only port is tolerated. -/
def interfaceOkB (component : Component) : Bool :=
  let shapes := component.designPortShapes
  component.interface.locallyValidB &&
    component.interface.ports.length == shapes.length &&
    component.interface.ports.all (fun port =>
      shapes.any fun shape => samePortShape port shape.1 shape.2.1 shape.2.2) &&
    shapes.all (fun shape => component.interface.ports.any fun port =>
      samePortShape port shape.1 shape.2.1 shape.2.2)

/-- A sealed component retains the executable certificates of its sole Design
implementation plus the checked typed boundary. -/
structure Sealed where
  component : Component
  interfaceOk : component.interfaceOkB = true
  readsOk : component.design.readsOkB = true
  certified : CertifiedDesign component.design

/-- Fail-closed component construction.  The ordinary emission gate remains
authoritative; hierarchy only moves interface failures to the component site. -/
def seal? (component : Component) : Except String Sealed := do
  if component.name.isEmpty then
    throw "component name must not be empty"
  else
    if hInterface : component.interfaceOkB = true then
      component.design.emitCheck
      if hReads : component.design.readsOkB = true then
        if hCompiler : Compile.designWFCheck component.design = true then
          if hSimulator : component.design.fastWFB = true then
            return { component
                     interfaceOk := hInterface
                     readsOk := hReads
                     certified := CertifiedDesign.ofChecks hCompiler hSimulator }
          else
            throw s!"component '{component.name}' is not simulator-ready"
        else
          throw s!"component '{component.name}' is not compiler-ready"
      else
        throw s!"component '{component.name}' contains an undeclared or wrong-width read"
    else
      throw s!"component '{component.name}' interface does not exactly match its Design ports"

/-- Successful sealing retains the exact input component; certification does
not rewrite or normalize its implementation. -/
theorem seal?_component_eq {component : Component} {sealed : Sealed}
    (result : component.seal? = .ok sealed) : sealed.component = component := by
  unfold seal? at result
  split at result
  · simp at result
  split at result
  · cases hEmit : component.design.emitCheck with
    | error message => simp [hEmit, Except.instMonad, Except.bind] at result
    | ok _unit =>
      simp [hEmit, Except.instMonad, Except.bind] at result
      split at result <;> try simp_all
      split at result <;> try simp_all
      split at result <;> try simp_all
      simp [Except.pure] at result
      subst sealed
      rfl
  · simp at result

end Component

/-- A scalar `Design` with ownership of every sequential element by one clock
domain. The scalar implementation still has exactly the core's one-clock
semantics; this wrapper records which System clock is permitted to tick it. -/
structure DomainDesign (δ : Type v) [ClockDomain δ] where
  private mk ::
  design : Design

namespace DomainDesign

/-- Ordinary authoring boundary for a scalar design created in a known domain.
All of the design's registers and memories acquire the same owner together. -/
def authored {δ : Type v} [ClockDomain δ] (design : Design) : DomainDesign δ :=
  ⟨design⟩

namespace Expert

/-- Import/generator boundary for legacy scalar designs. Prefer carrying a
`DomainDesign` from the point at which new synchronous logic is authored. -/
def ofDesign {δ : Type v} [ClockDomain δ] (design : Design) : DomainDesign δ :=
  authored design

end Expert

end DomainDesign

/-- A sealed component whose implementation and entire public boundary belong
to one nominal clock domain. This is the ordinary building block for
synchronous hierarchy; the erased `Component.Sealed` form remains the
import/generator boundary. -/
structure DomainComponent (δ : Type v) [ClockDomain δ] where
  implementation : DomainDesign δ
  sealed : Component.Sealed
  implementationEq : sealed.component.design = implementation.design
  domainOk : sealed.component.interface.ports.all
    (fun port => port.domain == ClockDomain.name δ) = true

namespace DomainComponent

/-- Seal an implementation which already carries its timing owner. The
component cannot be constructed first and assigned a domain afterward. -/
def seal? {δ : Type v} [ClockDomain δ] (name : String)
    (interface : ComponentInterface) (implementation : DomainDesign δ) :
    Except String (DomainComponent δ) := do
  let component : Component := { name, interface, design := implementation.design }
  match hSeal : component.seal? with
  | .error message => throw message
  | .ok sealed =>
    have sealedEq : sealed.component = component :=
      Component.seal?_component_eq hSeal
    have hEq : sealed.component.design = implementation.design := by
      rw [sealedEq]
    if h : sealed.component.interface.ports.all
        (fun port => port.domain == ClockDomain.name δ) = true then
      return ⟨implementation, sealed, hEq, h⟩
    throw s!"component '{sealed.component.name}' contains a port outside clock domain '{ClockDomain.name δ}'"

namespace Expert

/-- Compatibility/import path for an erased sealed component. This operation
deliberately assigns all scalar state to `δ` after the original seal. -/
def check? {δ : Type v} [ClockDomain δ] (sealed : Component.Sealed) :
    Except String (DomainComponent δ) := do
  if h : sealed.component.interface.ports.all
      (fun port => port.domain == ClockDomain.name δ) = true then
    let implementation := DomainDesign.Expert.ofDesign (δ := δ)
      sealed.component.design
    return ⟨implementation, sealed, rfl, h⟩
  throw s!"component '{sealed.component.name}' contains a port outside clock domain '{ClockDomain.name δ}'"

end Expert

end DomainComponent

structure HierarchyInstance (α : Type u) where
  path : InstancePath
  component : α

/-- One occurrence of a sealed component. -/
abbrev ComponentInstance := HierarchyInstance Component.Sealed

namespace ComponentInstance

def signalPrefix (inst : ComponentInstance) : String := inst.path ++ "__"

def findPort? (inst : ComponentInstance) (direction : PortDirection)
    (name : String) : Option PortDecl :=
  inst.component.component.interface.ports.find? fun port =>
    port.direction == direction && port.name == name

end ComponentInstance

/-- A typed input endpoint belonging to a particular instance. -/
structure InputEndpoint (δ : Type v) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  instancePath : InstancePath
  componentName : String
  port : Port .input δ α

/-- A typed output endpoint with its underlying component-local expression.
The expression is renamed when the instance graph is flattened. -/
structure OutputEndpoint (δ : Type v) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  instancePath : InstancePath
  componentName : String
  port : Port .output δ α
  expression : Expr (HwPacked.width α)

private def castExpr? {actual expected : Nat} (equal : actual = expected)
    (expression : Expr actual) : Expr expected := by
  subst equal
  exact expression

namespace ComponentInstance

/-- Resolve a typed input from a sealed component.  Both the nominal erased
type and the Lean payload width must match. -/
def input? {δ : Type v} {α : Type u} [ClockDomain δ] [HwPacked α]
    (inst : ComponentInstance)
    (port : Port .input δ α) : Except String (InputEndpoint δ α) := do
  if inst.component.component.interface.contains port.decl then
    return ⟨inst.path, inst.component.component.name, port⟩
  throw s!"instance '{inst.path}' has no input '{port.name}' with semantic type '{port.semanticType}' in domain '{ClockDomain.name δ}'"

private def outputExpr? (inst : ComponentInstance) (name : String)
    (width : Nat) : Option (Expr width) :=
  match inst.component.component.design.exportedRegs.find?
      (fun reg => reg.name == name) with
  | some reg =>
      if equal : reg.width = width then
        some (castExpr? equal (.reg reg.width reg.name))
      else none
  | none =>
      match inst.component.component.design.combOutputs.find?
          (fun output => output.name == name) with
      | some output =>
          if equal : output.width = width then
            some (castExpr? equal output.value)
          else none
      | none => none

/-- Resolve a typed output and retain its component-local driver expression. -/
def output? {δ : Type v} {α : Type u} [ClockDomain δ] [HwPacked α]
    (inst : ComponentInstance)
    (port : Port .output δ α) : Except String (OutputEndpoint δ α) := do
  if !inst.component.component.interface.contains port.decl then
    throw s!"instance '{inst.path}' has no output '{port.name}' with semantic type '{port.semanticType}' in domain '{ClockDomain.name δ}'"
  match inst.outputExpr? port.name (HwPacked.width α) with
  | some expression =>
      return ⟨inst.path, inst.component.component.name, port, expression⟩
  | none =>
      throw s!"instance '{inst.path}' output '{port.name}' has no matching Design expression"

end ComponentInstance

/-- Erased connection stored in a heterogeneous component graph.  The public
`Connection.typed` constructor establishes nominal payload equality first. -/
structure Connection where
  private mk ::
  width : Nat
  semanticType : String
  domain : String
  sourceInstance : String
  sourceComponent : String
  sourcePort : String
  sourceExpression : Expr width
  sinkInstance : String
  sinkComponent : String
  sinkPort : String

/-- A connection whose two endpoints were checked in the same nominal clock
domain.  Erasure is private to the indexed graph lowering. -/
structure DomainConnection (δ : Type v) [ClockDomain δ] where
  private mk ::
  raw : Connection

namespace Connection

/-- Construct a same-clock connection.  Different payload types cannot reach
this function; different domains are rejected instead of becoming an implicit
CDC crossing. -/
def typed {δ : Type v} {α : Type u} [ClockDomain δ] [HwPacked α]
    (source : OutputEndpoint δ α) (sink : InputEndpoint δ α) :
    Except String (DomainConnection δ) := do
  unless source.port.semanticType == sink.port.semanticType do
    throw s!"connection semantic type name mismatch: '{source.port.semanticType}' versus '{sink.port.semanticType}'"
  return ⟨{ width := HwPacked.width α
            semanticType := source.port.semanticType
            domain := ClockDomain.name δ
            sourceInstance := source.instancePath
            sourceComponent := source.componentName
            sourcePort := source.port.name
            sourceExpression := source.expression
            sinkInstance := sink.instancePath
            sinkComponent := sink.componentName
            sinkPort := sink.port.name }⟩

namespace Expert

/-- Explicit erasing constructor for importers and legacy graph generators.
Ordinary hierarchy should retain `DomainConnection δ`. -/
def typedErased {δ : Type v} {α : Type u} [ClockDomain δ] [HwPacked α]
    (source : OutputEndpoint δ α) (sink : InputEndpoint δ α) :
    Except String Connection := do
  return (← Connection.typed source sink).raw

end Expert

def sourceFullName (connection : Connection) : String :=
  connection.sourceInstance ++ "__" ++ connection.sourcePort

def sinkFullName (connection : Connection) : String :=
  connection.sinkInstance ++ "__" ++ connection.sinkPort

def replacement? (connection : Connection) (name : String) (width : Nat) :
    Option (Expr width) :=
  if _nameEqual : connection.sinkFullName = name then
    if widthEqual : connection.width = width then
      some (castExpr? widthEqual
        (connection.sourceExpression.mapSignals
          (connection.sourceInstance ++ "__" ++ ·)))
    else none
  else none

end Connection

/-- A typed instance graph before canonical lowering.  External visibility is
explicit: component outputs do not leak merely because an instance exists. -/
structure ComponentGraph where
  name : String
  instances : List ComponentInstance := []
  connections : List Connection := []
  exports : List (String × String) := []

namespace ComponentGraph

namespace Expert

/-- Erased importer/generator boundary. Ordinary hierarchy construction uses
`DomainComponentGraph.empty`. -/
def empty (name : String) : ComponentGraph := { name }

end Expert

@[deprecated ComponentGraph.Expert.empty (since := "2026-08-15")]
def empty (name : String) : ComponentGraph := Expert.empty name

def findInstance? (graph : ComponentGraph) (path : String) : Option ComponentInstance :=
  graph.instances.find? (·.path == path)

def Expert.addInstance (graph : ComponentGraph) (inst : ComponentInstance) :
    Except String ComponentGraph := do
  if inst.path.isEmpty then throw "component instance path must not be empty"
  if graph.instances.any (·.path == inst.path) then
    throw s!"duplicate component instance path '{inst.path}'"
  return { graph with instances := graph.instances ++ [inst] }

@[deprecated ComponentGraph.Expert.addInstance (since := "2026-08-15")]
def addInstance (graph : ComponentGraph) (inst : ComponentInstance) :
    Except String ComponentGraph := Expert.addInstance graph inst

private def endpointPresent (graph : ComponentGraph) (instancePath componentName : String)
    (direction : PortDirection) (portName semanticType domain : String)
    (width : Nat) : Bool :=
  graph.instances.any fun inst =>
    inst.path == instancePath &&
    inst.component.component.name == componentName &&
    inst.component.component.interface.ports.any fun port =>
      port.name == portName && port.direction == direction &&
      port.semanticType == semanticType && port.domain == domain &&
      port.width == width

def connectionValidB (graph : ComponentGraph) (connection : Connection) : Bool :=
  graph.endpointPresent connection.sourceInstance connection.sourceComponent
      .output connection.sourcePort connection.semanticType connection.domain
      connection.width &&
  graph.endpointPresent connection.sinkInstance connection.sinkComponent
      .input connection.sinkPort connection.semanticType connection.domain
      connection.width

def dependencyEdges (graph : ComponentGraph) : List (String × String) :=
  let internal := graph.instances.flatMap fun inst =>
    inst.component.component.combinationalDependencies.map fun edge =>
      (inst.signalPrefix ++ edge.1, inst.signalPrefix ++ edge.2)
  let wiring := graph.connections.map fun connection =>
    (connection.sourceFullName, connection.sinkFullName)
  internal ++ wiring

/-- Small executable check that every dependency edge is covered and points
strictly forward in the proposed order. -/
def edgesForwardB (order : List String) : List (String × String) → Bool
  | [] => true
  | edge :: rest =>
      order.contains edge.1 && order.contains edge.2 &&
        decide (order.idxOf edge.1 < order.idxOf edge.2) &&
        edgesForwardB order rest

/-- Small structural certificate checker: uniqueness plus forward-edge
coverage. -/
def topologicalOrderCheckB (edges : List (String × String))
    (order : List String) : Bool :=
  Inventory.uniqueB order && edgesForwardB order edges

/-- Kernel-level meaning of a topological certificate.  The order contains no
duplicates, covers both endpoints of every edge, and places every source
strictly before its sink. -/
def TopologicalOrder (edges : List (String × String)) (order : List String) : Prop :=
  topologicalOrderCheckB edges order = true

/-- A finite dependency graph is acyclic when it admits a checked topological
order.  This definition is independent of the algorithm proposing the order. -/
def DependencyAcyclic (edges : List (String × String)) : Prop :=
  ∃ order, TopologicalOrder edges order

theorem topologicalOrderCheckB_sound {edges : List (String × String)}
    {order : List String} (checked : topologicalOrderCheckB edges order = true) :
    DependencyAcyclic edges :=
  ⟨order, checked⟩

/-- Fast, untrusted proposal generation. Kahn's algorithm visits each node and
edge once with expected constant-time hash-table operations. A cyclic input
merely yields a partial order which the structural checker rejects. -/
def proposeTopologicalOrder (edges : List (String × String)) : List String :=
  Id.run do
    let mut seen : Std.HashSet String := {}
    let mut nodes : Array String := #[]
    let mut outgoing : Std.HashMap String (List String) := {}
    let mut indegree : Std.HashMap String Nat := {}
    for (source, sink) in edges do
      if !seen.contains source then
        seen := seen.insert source
        nodes := nodes.push source
        indegree := indegree.insert source 0
      if !seen.contains sink then
        seen := seen.insert sink
        nodes := nodes.push sink
        indegree := indegree.insert sink 0
      outgoing := outgoing.insert source (sink :: outgoing.getD source [])
      indegree := indegree.insert sink (indegree.getD sink 0 + 1)
    let mut ready : List String := []
    for node in nodes do
      if indegree.getD node 0 == 0 then ready := node :: ready
    let mut order : Array String := #[]
    while !ready.isEmpty do
      let node := ready.head!
      ready := ready.tail!
      order := order.push node
      for sink in outgoing.getD node [] do
        let degree := indegree.getD sink 0
        let next := degree - 1
        indegree := indegree.insert sink next
        if next == 0 then ready := sink :: ready
    return order.toList

/-- No same-cycle dependency can return to its starting signal.  Optimized
proposal generation is outside the trust boundary; acceptance is exactly the
small structural certificate checker above. -/
def combinationalAcyclicB (graph : ComponentGraph) : Bool :=
  let edges := graph.dependencyEdges
  topologicalOrderCheckB edges (proposeTopologicalOrder edges)

theorem combinationalAcyclicB_sound (graph : ComponentGraph)
    (checked : graph.combinationalAcyclicB = true) :
    DependencyAcyclic graph.dependencyEdges :=
  topologicalOrderCheckB_sound checked

def Expert.connect (graph : ComponentGraph) (connection : Connection) :
    Except String ComponentGraph := do
  if !graph.connectionValidB connection then
    throw s!"connection '{connection.sourceInstance}.{connection.sourcePort}' -> '{connection.sinkInstance}.{connection.sinkPort}' does not belong to the graph"
  if graph.connections.any (fun existing =>
      existing.sinkInstance == connection.sinkInstance &&
      existing.sinkPort == connection.sinkPort) then
    throw s!"input '{connection.sinkInstance}.{connection.sinkPort}' already has a driver"
  let connected := { graph with connections := graph.connections ++ [connection] }
  if !connected.combinationalAcyclicB then
    throw s!"connection '{connection.sourceInstance}.{connection.sourcePort}' -> '{connection.sinkInstance}.{connection.sinkPort}' creates a combinational dependency cycle"
  return connected

@[deprecated ComponentGraph.Expert.connect (since := "2026-08-15")]
def connect (graph : ComponentGraph) (connection : Connection) :
    Except String ComponentGraph := Expert.connect graph connection

/-- Make one component output visible at the graph boundary. -/
def Expert.expose (graph : ComponentGraph) (instancePath portName : String) :
    Except String ComponentGraph := do
  let some inst := graph.findInstance? instancePath
    | throw s!"cannot export from unknown instance '{instancePath}'"
  let some _ := inst.findPort? .output portName
    | throw s!"instance '{instancePath}' has no output '{portName}'"
  let key := (instancePath, portName)
  if graph.exports.contains key then
    throw s!"output '{instancePath}.{portName}' is already exported"
  return { graph with exports := graph.exports ++ [key] }

@[deprecated ComponentGraph.Expert.expose (since := "2026-08-15")]
def expose (graph : ComponentGraph) (instancePath portName : String) :
    Except String ComponentGraph := Expert.expose graph instancePath portName

def pathsUniqueB (graph : ComponentGraph) : Bool :=
  Inventory.uniqueB (graph.instances.map (·.path))

def connectionsValidB (graph : ComponentGraph) : Bool :=
  graph.connections.all graph.connectionValidB &&
    let sinks := graph.connections.map fun connection =>
      (connection.sinkInstance, connection.sinkPort)
    Inventory.uniqueB sinks

def exportsValidB (graph : ComponentGraph) : Bool :=
  graph.exports.all fun exposed =>
    match graph.findInstance? exposed.1 with
    | none => false
    | some inst => (inst.findPort? .output exposed.2).isSome

def validB (graph : ComponentGraph) : Bool :=
  !graph.name.isEmpty && graph.pathsUniqueB &&
    graph.connectionsValidB && graph.exportsValidB &&
    graph.combinationalAcyclicB

private def emptyDesign (name : String) : Design where
  name := name
  regs := []
  mems := []
  rules := []
  outputs := []

private def combined (graph : ComponentGraph) : Design :=
  graph.instances.foldl (fun design inst =>
    design.par (inst.component.component.design.prefixed inst.signalPrefix))
    (emptyDesign graph.name)

private def substituteConnections {w : Nat} (connections : List Connection)
    (expression : Expr w) : Expr w :=
  connections.foldl (fun value connection =>
    Expr.substReg connection.sinkFullName connection.width
      (connection.sourceExpression.mapSignals
        (connection.sourceInstance ++ "__" ++ ·)) value) expression

private def substituteConnectionActs (connections : List Connection)
    (action : Act) : Act :=
  connections.foldl (fun value connection =>
    Act.substReg connection.sinkFullName connection.width
      (connection.sourceExpression.mapSignals
        (connection.sourceInstance ++ "__" ++ ·)) value) action

/-- A downstream replacement may introduce an upstream input. Apply
substitutions from later dependency nodes to earlier ones, so every newly
introduced input is still ahead in this single pass. The graph's accepted
topological certificate makes this independent of instance and declaration
order without the quadratic repeated-substitution fallback. -/
private def connectionSubstitutionOrder (graph : ComponentGraph) : List Connection :=
  let order := proposeTopologicalOrder graph.dependencyEdges
  graph.connections.mergeSort fun left right =>
    order.idxOf left.sinkFullName ≥ order.idxOf right.sinkFullName

private def inputConnectedB (graph : ComponentGraph) (input : InputDecl) : Bool :=
  graph.connections.any fun connection =>
    connection.sinkFullName == input.name && connection.width == input.width

/-- Batched form of `Design.connect` for a checked hierarchy. It drops exactly
the driven inputs and applies the same `Expr.substReg`/`Act.substReg`
operations, but traverses the already ordered connection inventory once per
rule or combinational output instead of re-running a heterogeneous lookup for
every input/output pair. -/
private def connectAll (connections : List Connection)
    (design : Design) : Design :=
  { design with
    inputs := design.inputs.filter fun input => !connections.any fun connection =>
      connection.sinkFullName == input.name && connection.width == input.width
    combOutputs := design.combOutputs.map fun output =>
      ⟨output.name, output.width,
        substituteConnections connections output.value⟩
    rules := design.rules.map fun rule =>
      { rule with body := substituteConnectionActs connections rule.body } }

/-- Deliberately slow specification lowering for connection substitution. It
walks the complete Design once per connection, making it unsuitable for large
hierarchies but straightforward enough to serve as the reference algorithm. -/
private def connectOneReference (connection : Connection) (design : Design) : Design :=
  { design with
    inputs := design.inputs.filter fun input =>
      !(connection.sinkFullName == input.name && connection.width == input.width)
    combOutputs := design.combOutputs.map fun output =>
      let replacement := connection.sourceExpression.mapSignals fun name =>
        connection.sourceInstance ++ "__" ++ name
      ⟨output.name, output.width,
        Expr.substReg connection.sinkFullName connection.width
          replacement output.value⟩
    rules := design.rules.map fun rule =>
      let replacement := connection.sourceExpression.mapSignals fun name =>
        connection.sourceInstance ++ "__" ++ name
      let body := Act.substReg connection.sinkFullName connection.width
        replacement rule.body
      { rule with body := body } }

private def connectAllReference : List Connection → Design → Design
  | [], design => design
  | connection :: rest, design =>
      connectAllReference rest (connectOneReference connection design)

private theorem connectAll_eq_reference (connections : List Connection)
    (design : Design) :
    connectAll connections design = connectAllReference connections design := by
  induction connections generalizing design with
  | nil =>
      cases design
      simp [connectAll, connectAllReference, substituteConnections,
        substituteConnectionActs]
  | cons connection rest ih =>
      rw [connectAllReference, ← ih]
      cases design
      simp only [connectAll, connectOneReference, substituteConnections,
        substituteConnectionActs, List.foldl_cons, List.map_map,
        List.any_cons, List.filter_filter]
      congr 1
      apply List.filter_congr
      intro input _member
      simp only [Bool.not_or, Bool.not_and]
      generalize (!connection.sinkFullName == input.name ||
        !connection.width == input.width) = current
      generalize (!rest.any fun connection =>
        connection.sinkFullName == input.name && connection.width == input.width) = later
      cases current <;> cases later <;> rfl

private def exportedStateNames (graph : ComponentGraph) : List String :=
  graph.exports.filterMap fun exposed =>
    match graph.findInstance? exposed.1 with
    | none => none
    | some inst =>
        if inst.component.component.design.exportedRegs.any
            (fun reg => reg.name == exposed.2) then
          some (inst.signalPrefix ++ exposed.2)
        else none

private def outputExported (graph : ComponentGraph) (name : String) : Bool :=
  graph.exports.any fun exposed => exposed.1 ++ "__" ++ exposed.2 == name

/-- Canonical hierarchy lowering. Prefixing and parallel composition are the
existing Design operations; batched wiring uses the same core signal
substitutions. The graph boundary is then imposed explicitly so unexported
child ports remain internal. -/
def flatten (graph : ComponentGraph) : Design :=
  let substitutions := graph.connectionSubstitutionOrder
  let connected := connectAll substitutions graph.combined
  { connected with
    name := graph.name
    outputs := graph.exportedStateNames
    combOutputs := connected.combOutputs.filter fun output =>
      graph.outputExported output.name }

/-- Slow, independently structured specification of hierarchy lowering. It
uses one whole-Design pass per ordered connection and is retained only for
proof and regression comparison. -/
def flattenReference (graph : ComponentGraph) : Design :=
  let substitutions := graph.connectionSubstitutionOrder
  let connected := connectAllReference substitutions graph.combined
  { connected with
    name := graph.name
    outputs := graph.exportedStateNames
    combOutputs := connected.combOutputs.filter fun output =>
      graph.outputExported output.name }

/-- The optimized one-pass connection lowering is exactly the deliberately
slow reference flattener for every graph. No validity, acyclicity, or source
ordering hypothesis is needed for this algorithmic equality. -/
theorem flatten_eq_reference (graph : ComponentGraph) :
    graph.flatten = graph.flattenReference := by
  simp only [flatten, flattenReference, connectAll_eq_reference]

/-- Checked entry point.  The final ordinary Design gate remains authoritative,
so hierarchy cannot accept a graph the scalar compiler would reject. -/
def flatten? (graph : ComponentGraph) : Except String Design := do
  if !graph.validB then
    throw s!"component graph '{graph.name}' is structurally invalid"
  let design := graph.flatten
  design.emitCheck
  return design

/-- A hierarchy whose canonical flattened Design carries the same complete
compiler/simulator package as a directly authored Design. -/
structure Sealed (graph : ComponentGraph) where
  graphValid : graph.validB = true
  readsOk : graph.flatten.readsOkB = true
  certified : CertifiedDesign graph.flatten

/-- Seal the graph and derive all executable/compiler evidence from its one
canonical flattening. -/
def seal? (graph : ComponentGraph) : Except String (Sealed graph) := do
  if hGraph : graph.validB = true then
    graph.flatten.emitCheck
    if hReads : graph.flatten.readsOkB = true then
      if hCompiler : Compile.designWFCheck graph.flatten = true then
        if hSimulator : graph.flatten.fastWFB = true then
          return { graphValid := hGraph
                   readsOk := hReads
                   certified := CertifiedDesign.ofChecks hCompiler hSimulator }
        else
          throw s!"component graph '{graph.name}' is not simulator-ready"
      else
        throw s!"component graph '{graph.name}' is not compiler-ready"
    else
      throw s!"component graph '{graph.name}' contains an undeclared or wrong-width read"
  else
    throw s!"component graph '{graph.name}' is structurally invalid"

/-- Component-graph behavior is intentionally the behavior of its one
canonical lowering, not a parallel simulator that could drift. -/
def toTSys (graph : ComponentGraph) : Loom.TSys := graph.flatten.toTSys

@[simp] theorem toTSys_eq_flatten (graph : ComponentGraph) :
    graph.toTSys = graph.flatten.toTSys := rfl

/-- The sealed graph's compiled artifact is definitionally the existing
compiler applied to the canonical flattening. -/
theorem Sealed.compiled_eq {graph : ComponentGraph} (sealed : Sealed graph) :
    sealed.certified.compiled = Compile.compile graph.flatten :=
  sealed.certified.compiled_eq

end ComponentGraph

/-! ## Timing-preserving synchronous hierarchy

The erased graph above is the canonical lowering representation.  Ordinary
construction uses the indexed wrappers below, so a collection of components
cannot be flattened and later assigned an unrelated island clock. -/

/-- One instance known to belong wholly to `δ`. -/
abbrev DomainComponentInstance (δ : Type v) [ClockDomain δ] :=
  HierarchyInstance (DomainComponent δ)

namespace DomainComponentInstance

def erase {δ : Type v} [ClockDomain δ]
    (inst : DomainComponentInstance δ) : ComponentInstance :=
  ⟨inst.path, inst.component.sealed⟩

def input? {δ : Type v} {α : Type u} [ClockDomain δ] [HwPacked α]
    (inst : DomainComponentInstance δ) (port : Port .input δ α) :
    Except String (InputEndpoint δ α) := inst.erase.input? port

def output? {δ : Type v} {α : Type u} [ClockDomain δ] [HwPacked α]
    (inst : DomainComponentInstance δ) (port : Port .output δ α) :
    Except String (OutputEndpoint δ α) := inst.erase.output? port

end DomainComponentInstance

/-- A component graph which can contain only components owned by `δ`.
Connections still carry erased evidence internally, but their only public
constructor is `Connection.typed`. -/
structure DomainComponentGraph (δ : Type v) [ClockDomain δ] where
  private mk ::
  raw : ComponentGraph
  instances : List (DomainComponentInstance δ)

namespace DomainComponentGraph

def empty {δ : Type v} [ClockDomain δ] (name : String) :
    DomainComponentGraph δ := ⟨ComponentGraph.Expert.empty name, []⟩

def findInstance? {δ : Type v} [ClockDomain δ] (graph : DomainComponentGraph δ)
    (path : String) : Option (DomainComponentInstance δ) :=
  graph.instances.find? (·.path == path)

def addInstance {δ : Type v} [ClockDomain δ] (graph : DomainComponentGraph δ)
    (inst : DomainComponentInstance δ) : Except String (DomainComponentGraph δ) := do
  let raw ← ComponentGraph.Expert.addInstance graph.raw inst.erase
  return ⟨raw, graph.instances ++ [inst]⟩

def connect {δ : Type v} [ClockDomain δ] (graph : DomainComponentGraph δ)
    (connection : DomainConnection δ) : Except String (DomainComponentGraph δ) := do
  return ⟨← ComponentGraph.Expert.connect graph.raw connection.raw, graph.instances⟩

def expose {δ : Type v} [ClockDomain δ] (graph : DomainComponentGraph δ)
    (instancePath portName : String) : Except String (DomainComponentGraph δ) := do
  return ⟨← ComponentGraph.Expert.expose graph.raw instancePath portName,
    graph.instances⟩

def connectionCount {δ : Type v} [ClockDomain δ]
    (graph : DomainComponentGraph δ) : Nat := graph.raw.connections.length

def exportCount {δ : Type v} [ClockDomain δ]
    (graph : DomainComponentGraph δ) : Nat := graph.raw.exports.length

def validB {δ : Type v} [ClockDomain δ] (graph : DomainComponentGraph δ) : Bool :=
  graph.raw.validB

def seal? {δ : Type v} [ClockDomain δ] (graph : DomainComponentGraph δ) :
    Except String (ComponentGraph.Sealed graph.raw) := graph.raw.seal?

/-- Timing-preserving canonical lowering. -/
def flatten? {δ : Type v} [ClockDomain δ] (graph : DomainComponentGraph δ) :
    Except String (DomainDesign δ) :=
  DomainDesign.mk <$> graph.raw.flatten?

/-- Proof/regression view of the deliberately slow hierarchy lowering. -/
def flattenReference {δ : Type v} [ClockDomain δ]
    (graph : DomainComponentGraph δ) : DomainDesign δ :=
  ⟨graph.raw.flattenReference⟩

theorem flatten_eq_reference {δ : Type v} [ClockDomain δ]
    (graph : DomainComponentGraph δ) :
    graph.raw.flatten = graph.flattenReference.design :=
  ComponentGraph.flatten_eq_reference graph.raw

end DomainComponentGraph

/-! ## Seal-once typed hierarchy construction

`DomainComponentGraph.connect` intentionally remains the diagnostic-friendly
incremental API: it rejects a cycle at the edge which creates it. Large
generated hierarchies should not pay that whole-graph check for every edge.
The batch inventory below records only already-typed values and is validated
once by `ComponentHierarchy.checkBatch?` at sealing. Lists are stored in
reverse insertion order so adding 1,000 instances or connections is linear in
the inventory size rather than quadratic in repeated append operations. -/

structure DomainComponentBatch (δ : Type v) [ClockDomain δ] where
  private mk ::
  name : String
  instancesRev : List (DomainComponentInstance δ)
  connectionsRev : List (DomainConnection δ)
  exportsRev : List (String × String)

namespace DomainComponentBatch

def empty {δ : Type v} [ClockDomain δ] (name : String) :
    DomainComponentBatch δ := ⟨name, [], [], []⟩

def addInstance {δ : Type v} [ClockDomain δ] (batch : DomainComponentBatch δ)
    (inst : DomainComponentInstance δ) : DomainComponentBatch δ :=
  { batch with instancesRev := inst :: batch.instancesRev }

def connect {δ : Type v} [ClockDomain δ] (batch : DomainComponentBatch δ)
    (connection : DomainConnection δ) : DomainComponentBatch δ :=
  { batch with connectionsRev := connection :: batch.connectionsRev }

def expose {δ : Type v} [ClockDomain δ] (batch : DomainComponentBatch δ)
    (instancePath portName : String) : DomainComponentBatch δ :=
  { batch with exportsRev := (instancePath, portName) :: batch.exportsRev }

def instanceCount {δ : Type v} [ClockDomain δ]
    (batch : DomainComponentBatch δ) : Nat := batch.instancesRev.length

def connectionCount {δ : Type v} [ClockDomain δ]
    (batch : DomainComponentBatch δ) : Nat := batch.connectionsRev.length

namespace Expert

/-- Unchecked materialization used by the compositional certificate checker.
Ordinary code should call `ComponentHierarchy.checkBatch?`, which returns the
materialized graph together with its certificate. -/
def materialize {δ : Type v} [ClockDomain δ] (batch : DomainComponentBatch δ) :
    DomainComponentGraph δ :=
  let instances := batch.instancesRev.reverse
  let raw : ComponentGraph :=
    { name := batch.name
      instances := instances.map DomainComponentInstance.erase
      connections := batch.connectionsRev.reverse.map (fun connection => connection.raw)
      exports := batch.exportsRev.reverse }
  ⟨raw, instances⟩

end Expert

end DomainComponentBatch

end Loom.Hw
