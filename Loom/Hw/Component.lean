-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.CertifiedDesign
import Loom.Hw.Compose
import Loom.Hw.EmitIO
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

/-- Port direction at a component boundary. -/
inductive PortDirection where
  | input
  | output
  deriving Repr, DecidableEq, BEq

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
  let names := interface.ports.map (·.name)
  names.eraseDups.length == names.length

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
  else pure ()
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

end Component

/-- One occurrence of a sealed component.  Paths are semantic hierarchy names;
the flattening prefix is derived from them in one place. -/
structure ComponentInstance where
  path : String
  component : Component.Sealed

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
  instancePath : String
  componentName : String
  port : Port .input δ α

/-- A typed output endpoint with its underlying component-local expression.
The expression is renamed when the instance graph is flattened. -/
structure OutputEndpoint (δ : Type v) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  instancePath : String
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

namespace Connection

/-- Construct a same-clock connection.  Different payload types cannot reach
this function; different domains are rejected instead of becoming an implicit
CDC crossing. -/
def typed {δ : Type v} {α : Type u} [ClockDomain δ] [HwPacked α]
    (source : OutputEndpoint δ α) (sink : InputEndpoint δ α) :
    Except String Connection := do
  unless source.port.semanticType == sink.port.semanticType do
    throw s!"connection semantic type name mismatch: '{source.port.semanticType}' versus '{sink.port.semanticType}'"
  return { width := HwPacked.width α
           semanticType := source.port.semanticType
           domain := ClockDomain.name δ
           sourceInstance := source.instancePath
           sourceComponent := source.componentName
           sourcePort := source.port.name
           sourceExpression := source.expression
           sinkInstance := sink.instancePath
           sinkComponent := sink.componentName
           sinkPort := sink.port.name }

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

def empty (name : String) : ComponentGraph := { name }

def findInstance? (graph : ComponentGraph) (path : String) : Option ComponentInstance :=
  graph.instances.find? (·.path == path)

def addInstance (graph : ComponentGraph) (inst : ComponentInstance) :
    Except String ComponentGraph := do
  if inst.path.isEmpty then throw "component instance path must not be empty"
  if graph.instances.any (·.path == inst.path) then
    throw s!"duplicate component instance path '{inst.path}'"
  return { graph with instances := graph.instances ++ [inst] }

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

private def combinationalEdges (graph : ComponentGraph) : List (String × String) :=
  let internal := graph.instances.flatMap fun inst =>
    inst.component.component.combinationalDependencies.map fun edge =>
      (inst.signalPrefix ++ edge.1, inst.signalPrefix ++ edge.2)
  let wiring := graph.connections.map fun connection =>
    (connection.sourceFullName, connection.sinkFullName)
  internal ++ wiring

private def pathB (edges : List (String × String))
    (fuel : Nat) (source target : String) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
      edges.any fun edge =>
        edge.1 == source &&
          (edge.2 == target || pathB edges fuel edge.2 target)

/-- No same-cycle dependency can return to its starting signal.  This is a
structural property of typed component wiring, independent of backend
heuristics. -/
def combinationalAcyclicB (graph : ComponentGraph) : Bool :=
  let edges := graph.combinationalEdges
  let nodes := (edges.flatMap fun edge => [edge.1, edge.2]).eraseDups
  nodes.all fun node => !pathB edges nodes.length node node

def connect (graph : ComponentGraph) (connection : Connection) :
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

/-- Make one component output visible at the graph boundary. -/
def expose (graph : ComponentGraph) (instancePath portName : String) :
    Except String ComponentGraph := do
  let some inst := graph.findInstance? instancePath
    | throw s!"cannot export from unknown instance '{instancePath}'"
  let some _ := inst.findPort? .output portName
    | throw s!"instance '{instancePath}' has no output '{portName}'"
  let key := (instancePath, portName)
  if graph.exports.contains key then
    throw s!"output '{instancePath}.{portName}' is already exported"
  return { graph with exports := graph.exports ++ [key] }

def pathsUniqueB (graph : ComponentGraph) : Bool :=
  let paths := graph.instances.map (·.path)
  paths.eraseDups.length == paths.length

def connectionsValidB (graph : ComponentGraph) : Bool :=
  graph.connections.all graph.connectionValidB &&
    let sinks := graph.connections.map fun connection =>
      (connection.sinkInstance, connection.sinkPort)
    sinks.eraseDups.length == sinks.length

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

private def replacement (graph : ComponentGraph)
    (name : String) (width : Nat) : Option (Expr width) :=
  graph.connections.findSome? fun connection => connection.replacement? name width

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

/-- Canonical hierarchy lowering.  Prefixing, parallel composition, and input
substitution are exactly the existing core operations.  The graph boundary is
then imposed explicitly so unexported child ports remain internal. -/
def flatten (graph : ComponentGraph) : Design :=
  let connected := graph.combined.connect graph.replacement
  { connected with
    name := graph.name
    outputs := graph.exportedStateNames
    combOutputs := connected.combOutputs.filter fun output =>
      graph.outputExported output.name }

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

end Loom.Hw
