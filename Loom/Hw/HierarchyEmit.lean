-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ExternalHierarchy
import Loom.Artifact

/-!
# Hierarchy-preserving backend emission

`ComponentGraph.flatten` remains the canonical semantic lowering.  This file
finishes the separate-compilation boundary: checked child module artifacts and
an exact instance/net plan render as a structural top without recompiling or
textually rewriting children.  The structural artifact is external evidence
until a refinement/equivalence result relates it to the canonical flattening.
-/

namespace Loom.Hw

universe v

namespace Backend

/-- Explicit top-level port. `port` is the external HDL name and `net` is the
logical hierarchy net; differing names produce a directional assign. -/
abbrev TopPortPlan := PortPlan

/-- Loom-emitted child modules have fixed `clk`/`rst` ports outside their
component data interface.  Clock/reset hookups are therefore explicit plan
data instead of magic renderer conventions. -/
structure InstanceClockReset where
  path : InstancePath
  clockNet : String
  resetNet : String
  deriving Repr, DecidableEq, BEq

structure HierarchyEmissionPlan (ExternalArtifact Assumption : Type) where
  design : Plan ExternalArtifact Assumption
  topPorts : List TopPortPlan
  clockReset : List InstanceClockReset := []

namespace HierarchyEmissionPlan

private def identifierStart (character : Char) : Bool :=
  character.isAlpha || character == '_'

private def identifierRest (character : Char) : Bool :=
  character.isAlphanum || character == '_' || character == '$'

private def identifierB (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest => identifierStart first && rest.all identifierRest

private structure NetUse where
  net : String
  direction : PortDirection
  width : Nat

private def uses {ExternalArtifact Assumption : Type}
    (plan : HierarchyEmissionPlan ExternalArtifact Assumption) : List NetUse :=
  let top := plan.topPorts.map fun port =>
    -- A top input drives the hierarchy; a top output consumes it.
    ⟨port.net,
      if port.direction == .input then .output else .input,
      port.width⟩
  let instances := plan.design.instances.flatMap fun inst =>
    inst.ports.map fun port => ⟨port.net, port.direction, port.width⟩
  let clocks := plan.clockReset.flatMap fun clocking =>
    [⟨clocking.clockNet, .input, 1⟩, ⟨clocking.resetNet, .input, 1⟩]
  top ++ instances ++ clocks

private def netNames {ExternalArtifact Assumption : Type}
    (plan : HierarchyEmissionPlan ExternalArtifact Assumption) : List String :=
  (plan.uses.map (·.net)).eraseDups

private def netValid {ExternalArtifact Assumption : Type}
    (plan : HierarchyEmissionPlan ExternalArtifact Assumption) (net : String) : Bool :=
  let uses := plan.uses.filter (·.net == net)
  let widths := uses.map (·.width)
  let drivers := uses.filter (·.direction == .output)
  let sinks := uses.filter (·.direction == .input)
  identifierB net && !uses.isEmpty && widths.all (· == widths.headD 0) &&
    widths.headD 0 > 0 && drivers.length == 1 && !sinks.isEmpty

def validB {ExternalArtifact Assumption : Type}
    (plan : HierarchyEmissionPlan ExternalArtifact Assumption) : Bool :=
  let instancePaths := plan.design.instances.map (·.path)
  let moduleNames := plan.design.modules.map (·.name)
  let topNames := plan.topPorts.map (·.port)
  let clockedPaths := plan.clockReset.map (·.path)
  identifierB plan.design.topName && Inventory.uniqueB instancePaths &&
    plan.design.instances.all (fun inst =>
      identifierB inst.path && identifierB inst.moduleName &&
      Inventory.uniqueB (inst.ports.map (·.port)) &&
      inst.ports.all (fun port =>
        identifierB port.port && identifierB port.net && port.width > 0) &&
      Inventory.uniqueB (inst.parameters.map (·.1)) &&
      inst.parameters.all (fun parameter => identifierB parameter.1)) &&
    Inventory.uniqueB moduleNames && moduleNames.all identifierB &&
    Inventory.uniqueB topNames && plan.topPorts.all (fun port =>
      identifierB port.port && identifierB port.net && port.width > 0) &&
    Inventory.uniqueB clockedPaths && plan.clockReset.all (fun clocking =>
      instancePaths.contains clocking.path && identifierB clocking.clockNet &&
        identifierB clocking.resetNet) &&
    plan.netNames.all plan.netValid

def check {ExternalArtifact Assumption : Type}
    (plan : HierarchyEmissionPlan ExternalArtifact Assumption) : Except String Unit := do
  unless plan.validB do
    throw s!"hierarchy emission plan '{plan.design.topName}' has an invalid identifier, duplicate inventory, width mismatch, undriven net, multiply driven net, or unconsumed net"

private def widthRange (width : Nat) : String :=
  if width == 1 then "" else s!" [{width - 1}:0]"

private def renderTopPort (port : TopPortPlan) : String :=
  let direction := if port.direction == .input then "input" else "output"
  s!"  {direction} wire{widthRange port.width} {port.port}"

private def clockingFor {ExternalArtifact Assumption : Type}
    (plan : HierarchyEmissionPlan ExternalArtifact Assumption)
    (path : String) : Option InstanceClockReset :=
  plan.clockReset.find? (·.path == path)

private def renderParameter (parameter : String × String) : String :=
  s!".{parameter.1}({parameter.2})"

private def renderConnection (port net : String) : String :=
  s!".{port}({net})"

private def renderInstance {ExternalArtifact Assumption : Type}
    (plan : HierarchyEmissionPlan ExternalArtifact Assumption)
    (inst : InstancePlan) : String :=
  let parameters := if inst.parameters.isEmpty then "" else
    " #(\n    " ++ String.intercalate ",\n    "
      (inst.parameters.map renderParameter) ++ "\n  )"
  let implicit := match plan.clockingFor inst.path with
    | none => []
    | some clocking =>
        [renderConnection "clk" clocking.clockNet,
         renderConnection "rst" clocking.resetNet]
  let ports := implicit ++ inst.ports.map fun port =>
    renderConnection port.port port.net
  s!"  {inst.moduleName}{parameters} {inst.path} (\n    " ++
    String.intercalate ",\n    " ports ++ "\n  );"

/-- Deterministic structural wrapper rendering. Validation is mandatory and
no external module bytes are interpreted or modified. -/
def renderTop? {ExternalArtifact Assumption : Type}
    (plan : HierarchyEmissionPlan ExternalArtifact Assumption) :
    Except String String := do
  plan.check
  let header := s!"module {plan.design.topName}(\n" ++
    String.intercalate ",\n" (plan.topPorts.map renderTopPort) ++ "\n);"
  let topPortNames := plan.topPorts.map (·.port)
  let internalNets := plan.netNames.filter fun net => !topPortNames.contains net
  let widths := fun net => (plan.uses.find? (·.net == net)).map (·.width) |>.getD 1
  let declarations := internalNets.map fun net =>
    s!"  wire{widthRange (widths net)} {net};"
  let bridges := plan.topPorts.filterMap fun port =>
    if port.port == port.net then none
    else if port.direction == .input then some s!"  assign {port.net} = {port.port};"
    else some s!"  assign {port.port} = {port.net};"
  let instances := plan.design.instances.map (renderInstance plan)
  return String.intercalate "\n"
    ([header] ++ declarations ++ bridges ++ instances ++ ["endmodule", ""])

structure ArtifactSet where
  top : ModuleArtifact
  modules : List ModuleArtifact

def artifacts? {ExternalArtifact Assumption : Type}
    (plan : HierarchyEmissionPlan ExternalArtifact Assumption) :
    Except String ArtifactSet := do
  return ⟨⟨plan.design.topName, ← plan.renderTop?⟩, plan.design.modules⟩

end HierarchyEmissionPlan

end Backend

namespace BoundComponentGraph

private def connectedSink {δ : Type v} [ClockDomain δ]
    (graph : BoundComponentGraph δ) (path port : String) : Bool :=
  graph.connections.any fun connection =>
    connection.sinkInstance == path && connection.sinkPort == port

private def consumedSource {δ : Type v} [ClockDomain δ]
    (graph : BoundComponentGraph δ) (path port : String) : Bool :=
  graph.connections.any fun connection =>
    connection.sourceInstance == path && connection.sourcePort == port

private def boundaryPorts {δ : Type v} [ClockDomain δ]
    (graph : BoundComponentGraph δ) : List Backend.TopPortPlan :=
  let internal := graph.internal.flatMap fun inst =>
    inst.component.sealed.component.interface.ports.filterMap fun port =>
      let exposed := (port.direction == .input &&
          !graph.connectedSink inst.path port.name) ||
        (port.direction == .output &&
          !graph.consumedSource inst.path port.name)
      if exposed then
        some ⟨inst.path ++ "__" ++ port.name,
          inst.path ++ "__" ++ port.name, port.direction, port.width⟩
      else none
  let external := graph.external.flatMap fun inst =>
    inst.component.sealed.specification.interface.ports.filterMap fun port =>
      let exposed := (port.direction == .input &&
          !graph.connectedSink inst.path port.name) ||
        (port.direction == .output &&
          !graph.consumedSource inst.path port.name)
      if exposed then
        some ⟨inst.path ++ "__" ++ port.name,
          inst.path ++ "__" ++ port.name, port.direction, port.width⟩
      else none
  internal ++ external

/-- Hierarchy-preserving companion to the existing exact `emissionPlan`.
Unconnected leaf ports become explicit boundary ports; every internal Loom
child receives explicit common clock/reset hookups. -/
def hierarchyEmissionPlan {δ : Type v} [ClockDomain δ]
    (graph : BoundComponentGraph δ) (clockNet resetNet : String) :
    Backend.HierarchyEmissionPlan Loom.Artifact.Identity NamedAssumption where
  design := graph.emissionPlan
  topPorts :=
    [⟨clockNet, clockNet, .input, 1⟩, ⟨resetNet, resetNet, .input, 1⟩] ++
      graph.boundaryPorts
  clockReset := graph.internal.map fun inst =>
    ⟨inst.path, clockNet, resetNet⟩

end BoundComponentGraph

end Loom.Hw
