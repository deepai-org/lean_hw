-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ComponentHierarchy
import Loom.Hw.ExternalComponent

/-!
# External leaves in typed component hierarchy

External leaves remain assumption-bound. This module makes them genuine graph
instances with typed endpoints, checked connections, exact artifact identity,
and collected release assumptions. It does not invent an executable `Design`
for external bytes.
-/

namespace Loom.Hw

universe u v

/-- A valid external contract and exact binding. -/
structure SealedExternal where
  specification : ExternalComponent
  specificationValid : specification.validB = true
  binding : ExternalBinding specification
  bindingValid : binding.validB = true

namespace SealedExternal

def check? (specification : ExternalComponent)
    (binding : ExternalBinding specification) : Except String SealedExternal := do
  if hSpec : specification.validB = true then
    if hBinding : binding.validB = true then
      return ⟨specification, hSpec, binding, hBinding⟩
    throw s!"external binding for '{specification.name}' is incomplete"
  throw s!"external component '{specification.name}' has an invalid contract"

end SealedExternal

/-- A single-domain external leaf. Multi-domain IP belongs at the System
fragment boundary rather than inside a synchronous component graph. -/
structure DomainExternal (δ : Type v) [ClockDomain δ] where
  sealed : SealedExternal
  domainOk :
    (sealed.specification.domains.length == 1 &&
      sealed.specification.domains.all (·.domain == ClockDomain.name δ) &&
      sealed.specification.interface.ports.all
        (·.domain == ClockDomain.name δ)) = true

namespace DomainExternal

def check? {δ : Type v} [ClockDomain δ] (sealed : SealedExternal) :
    Except String (DomainExternal δ) := do
  if h : (sealed.specification.domains.length == 1 &&
      sealed.specification.domains.all (·.domain == ClockDomain.name δ) &&
      sealed.specification.interface.ports.all
        (·.domain == ClockDomain.name δ)) = true then
    return ⟨sealed, h⟩
  throw s!"external component '{sealed.specification.name}' is not wholly owned by clock domain '{ClockDomain.name δ}'"

end DomainExternal

structure ExternalInstance (δ : Type v) [ClockDomain δ] where
  path : InstancePath
  component : DomainExternal δ

/-- Hierarchical endpoints intentionally omit a source expression: an external
output is a module port, not a fabricated Loom register read. -/
structure HierarchyEndpoint (direction : PortDirection) (δ : Type v) (α : Type u)
    [ClockDomain δ] [HwPacked α] : Type (max 1 u v) where
  instancePath : InstancePath
  componentName : String
  port : Port direction δ α

abbrev HierarchyOutput (δ : Type v) (α : Type u)
    [ClockDomain δ] [HwPacked α] := HierarchyEndpoint .output δ α

abbrev HierarchyInput (δ : Type v) (α : Type u)
    [ClockDomain δ] [HwPacked α] := HierarchyEndpoint .input δ α

namespace HierarchyOutput

def ofInternal {δ : Type v} {α : Type u} [ClockDomain δ] [HwPacked α]
    (endpoint : OutputEndpoint δ α) : HierarchyOutput δ α :=
  ⟨endpoint.instancePath, endpoint.componentName, endpoint.port⟩

end HierarchyOutput

namespace HierarchyInput

def ofInternal {δ : Type v} {α : Type u} [ClockDomain δ] [HwPacked α]
    (endpoint : InputEndpoint δ α) : HierarchyInput δ α :=
  ⟨endpoint.instancePath, endpoint.componentName, endpoint.port⟩

end HierarchyInput

namespace ExternalInstance

def input? {δ : Type v} {α : Type u} [ClockDomain δ] [HwPacked α]
    (inst : ExternalInstance δ) (port : Port .input δ α) :
    Except String (HierarchyInput δ α) := do
  if inst.component.sealed.specification.interface.contains port.decl then
    return ⟨inst.path, inst.component.sealed.specification.name, port⟩
  throw s!"external instance '{inst.path}' has no matching input '{port.name}'"

def output? {δ : Type v} {α : Type u} [ClockDomain δ] [HwPacked α]
    (inst : ExternalInstance δ) (port : Port .output δ α) :
    Except String (HierarchyOutput δ α) := do
  if inst.component.sealed.specification.interface.contains port.decl then
    return ⟨inst.path, inst.component.sealed.specification.name, port⟩
  throw s!"external instance '{inst.path}' has no matching output '{port.name}'"

end ExternalInstance

structure HierarchyConnection (δ : Type v) [ClockDomain δ] : Type (max 1 v) where
  private mk ::
  width : Nat
  semanticType : String
  sourceInstance : String
  sourceComponent : String
  sourcePort : String
  sinkInstance : String
  sinkComponent : String
  sinkPort : String

namespace HierarchyConnection

def typed {δ : Type v} {α : Type u} [ClockDomain δ] [HwPacked α]
    (source : HierarchyOutput δ α) (sink : HierarchyInput δ α) :
    Except String (HierarchyConnection δ) := do
  unless source.port.semanticType == sink.port.semanticType do
    throw s!"hierarchy connection semantic type mismatch: '{source.port.semanticType}' versus '{sink.port.semanticType}'"
  return ⟨HwPacked.width α, source.port.semanticType,
    source.instancePath, source.componentName, source.port.name,
    sink.instancePath, sink.componentName, sink.port.name⟩

end HierarchyConnection

/-- Mixed internal/external same-clock hierarchy. External instances retain
their exact binding and assumptions; no flattening operation is offered. -/
structure BoundComponentGraph (δ : Type v) [ClockDomain δ] where
  name : String
  internal : List (DomainComponentInstance δ) := []
  external : List (ExternalInstance δ) := []
  connections : List (HierarchyConnection δ) := []

namespace BoundComponentGraph

def empty {δ : Type v} [ClockDomain δ] (name : String) : BoundComponentGraph δ :=
  { name }

private def paths {δ : Type v} [ClockDomain δ]
    (graph : BoundComponentGraph δ) : List String :=
  graph.internal.map (·.path) ++ graph.external.map (·.path)

def addInternal {δ : Type v} [ClockDomain δ] (graph : BoundComponentGraph δ)
    (inst : DomainComponentInstance δ) : Except String (BoundComponentGraph δ) := do
  if inst.path.isEmpty then throw "component instance path must not be empty"
  if graph.paths.contains inst.path then throw s!"duplicate hierarchy path '{inst.path}'"
  return { graph with internal := graph.internal ++ [inst] }

def addExternal {δ : Type v} [ClockDomain δ] (graph : BoundComponentGraph δ)
    (inst : ExternalInstance δ) : Except String (BoundComponentGraph δ) := do
  if inst.path.isEmpty then throw "external instance path must not be empty"
  if graph.paths.contains inst.path then throw s!"duplicate hierarchy path '{inst.path}'"
  return { graph with external := graph.external ++ [inst] }

private def hasPort {δ : Type v} [ClockDomain δ] (graph : BoundComponentGraph δ)
    (path component port semanticType : String) (direction : PortDirection)
    (width : Nat) : Bool :=
  let internal := graph.internal.any fun inst =>
    inst.path == path && inst.component.sealed.component.name == component &&
      inst.component.sealed.component.interface.ports.any fun candidate =>
        candidate.name == port && candidate.semanticType == semanticType &&
          candidate.direction == direction && candidate.width == width
  let external := graph.external.any fun inst =>
    inst.path == path && inst.component.sealed.specification.name == component &&
      inst.component.sealed.specification.interface.ports.any fun candidate =>
        candidate.name == port && candidate.semanticType == semanticType &&
          candidate.direction == direction && candidate.width == width
  internal || external

def connect {δ : Type v} [ClockDomain δ] (graph : BoundComponentGraph δ)
    (connection : HierarchyConnection δ) : Except String (BoundComponentGraph δ) := do
  unless graph.hasPort connection.sourceInstance connection.sourceComponent
      connection.sourcePort connection.semanticType .output connection.width do
    throw s!"unknown hierarchy source '{connection.sourceInstance}.{connection.sourcePort}'"
  unless graph.hasPort connection.sinkInstance connection.sinkComponent
      connection.sinkPort connection.semanticType .input connection.width do
    throw s!"unknown hierarchy sink '{connection.sinkInstance}.{connection.sinkPort}'"
  if graph.connections.any fun existing =>
      existing.sinkInstance == connection.sinkInstance &&
        existing.sinkPort == connection.sinkPort then
    throw s!"hierarchy input '{connection.sinkInstance}.{connection.sinkPort}' already has a driver"
  return { graph with connections := graph.connections ++ [connection] }

/-- Exact external artifact identities which a release must carry. -/
def externalArtifacts {δ : Type v} [ClockDomain δ] (graph : BoundComponentGraph δ) :
    List Loom.Artifact.Identity :=
  graph.external.map (·.component.sealed.binding.artifact)

/-- Instance-qualified premises which remain outside Loom's kernel proof. -/
def externalAssumptions {δ : Type v} [ClockDomain δ]
    (graph : BoundComponentGraph δ) : List NamedAssumption :=
  graph.external.flatMap fun inst =>
    inst.component.sealed.binding.assumptions.map fun assumption =>
      { assumption with name := inst.path ++ "." ++ assumption.name }

private def sourceNet {δ : Type v} [ClockDomain δ]
    (connection : HierarchyConnection δ) : String :=
  connection.sourceInstance ++ "__" ++ connection.sourcePort

private def portNet {δ : Type v} [ClockDomain δ] (graph : BoundComponentGraph δ)
    (path port : String) (direction : PortDirection) : String :=
  if direction == .input then
    match graph.connections.find? fun connection =>
        connection.sinkInstance == path && connection.sinkPort == port with
    | some connection => sourceNet connection
    | none => path ++ "__" ++ port
  else path ++ "__" ++ port

private def plannedPorts {δ : Type v} [ClockDomain δ]
    (graph : BoundComponentGraph δ) (path : String)
    (interface : ComponentInterface) : List Backend.PortPlan :=
  interface.ports.map fun port =>
    ⟨port.name, graph.portNet path port.name port.direction,
      port.direction, port.width⟩

/-- Produce actual module-instantiation data. This operation does not flatten,
recompile children, or claim that external bytes satisfy their assumptions. -/
def emissionPlan {δ : Type v} [ClockDomain δ]
    (graph : BoundComponentGraph δ) :
    Backend.Plan Loom.Artifact.Identity NamedAssumption :=
  let internalInstances := graph.internal.map fun inst =>
    { path := inst.path
      moduleName := inst.component.sealed.component.design.name
      parameters := []
      ports := graph.plannedPorts inst.path inst.component.sealed.component.interface
      external := false }
  let externalInstances := graph.external.map fun inst =>
    { path := inst.path
      moduleName := inst.component.sealed.binding.moduleName
      parameters := inst.component.sealed.binding.parameters
      ports := graph.plannedPorts inst.path
        inst.component.sealed.specification.interface
      external := true }
  { topName := graph.name
    instances := internalInstances ++ externalInstances
    modules := graph.internal.map fun inst =>
      { name := inst.component.sealed.component.design.name
        text := inst.component.sealed.certified.renderedVerilog }
    externalArtifacts := graph.externalArtifacts
    assumptions := graph.externalAssumptions }

/-! ## Proved internal substitution -/

/-- Actual observable component outputs. The default is unreachable for a
sealed exact interface, but keeps `PortEnv` total outside a declared port. -/
def componentOutputEnv (component : Component) (input : InEnv) (state : St) :
    PortEnv := fun name width =>
  match component.design.exportedRegs.find? (fun reg => reg.name == name) with
  | some reg =>
      if equal : reg.width = width then
        equal ▸ state.regs reg.name reg.width
      else 0
  | none =>
      match component.design.combOutputs.find? (fun output => output.name == name) with
      | some output =>
          if equal : output.width = width then
            equal ▸ component.design.evalCombOutput input state output
          else 0
      | none => 0

/-- A register-output-only component's observations do not depend on its
input environment.  External-island contracts use this to state exact
registered behavior without inventing dummy input dependencies. -/
theorem componentOutputEnv_input_independent (component : Component)
    (noComb : component.design.combOutputs = []) (left right : InEnv)
    (state : St) :
    componentOutputEnv component left state =
      componentOutputEnv component right state := by
  funext name width
  simp [componentOutputEnv, noComb]

/-- Kernel obligation tying a real internal `Design` transition to an external
contract. Reset, active ticks, unticked holds, and observations are explicit;
the witness cannot be manufactured from matching port names alone. -/
structure DesignContractWitness {δ : Type v} [ClockDomain δ]
    (component : DomainComponent δ) (specification : ExternalComponent) where
  interfaceEq : component.sealed.component.interface = specification.interface
  abstract : St → specification.behavior.State
  init : specification.behavior.init
    (abstract component.sealed.component.design.reset)
  tick : ∀ event input state,
    event.ticks (ClockDomain.name δ) = true →
    event.resets (ClockDomain.name δ) = false →
    specification.behavior.step event input (abstract state)
      (abstract (component.sealed.component.design.cycleOpen input state))
  reset : ∀ event input state,
    event.resets (ClockDomain.name δ) = true →
    specification.behavior.step event input (abstract state)
      (abstract component.sealed.component.design.reset)
  hold : ∀ event input state,
    event.ticks (ClockDomain.name δ) = false →
    event.resets (ClockDomain.name δ) = false →
    specification.behavior.step event input (abstract state) (abstract state)
  observe : ∀ input state,
    PortEnv.AgreeOn specification.interface.outputs
      (specification.behavior.observe input (abstract state))
      (componentOutputEnv component.sealed.component input state)

structure InternalReplacement {δ : Type v} [ClockDomain δ]
    (external : ExternalInstance δ) where
  component : DomainComponent δ
  witness : DesignContractWitness component external.component.sealed.specification

structure SubstitutionResult {δ : Type v} [ClockDomain δ]
    (original : BoundComponentGraph δ) where
  graph : BoundComponentGraph δ
  replacedPath : String

private def _root_.Loom.Hw.HierarchyConnection.replaceComponent
    {δ : Type v} [ClockDomain δ]
    (connection : HierarchyConnection δ) (path componentName : String) :
    HierarchyConnection δ :=
  ⟨connection.width, connection.semanticType,
    connection.sourceInstance,
    if connection.sourceInstance == path then componentName else connection.sourceComponent,
    connection.sourcePort, connection.sinkInstance,
    if connection.sinkInstance == path then componentName else connection.sinkComponent,
    connection.sinkPort⟩

/-- Replace one contracted external leaf with a proved internal implementation.
Its artifact and assumptions disappear because the returned graph no longer
contains that external instance. -/
def substituteInternal {δ : Type v} [ClockDomain δ]
    (graph : BoundComponentGraph δ) (external : ExternalInstance δ)
    (replacement : InternalReplacement external) :
    Except String (SubstitutionResult graph) := do
  unless graph.external.any (·.path == external.path) do
    throw s!"external instance '{external.path}' does not belong to hierarchy '{graph.name}'"
  if graph.internal.any (·.path == external.path) then
    throw s!"internal instance path '{external.path}' already exists"
  let componentName := replacement.component.sealed.component.name
  let replaced : BoundComponentGraph δ :=
    { graph with
      internal := graph.internal ++ [⟨external.path, replacement.component⟩]
      external := graph.external.filter (·.path != external.path)
      connections := graph.connections.map
        (·.replaceComponent external.path componentName) }
  return ⟨replaced, external.path⟩

end BoundComponentGraph

end Loom.Hw
