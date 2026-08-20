-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ImportIR
import Loom.Hw.HierarchyEmit

/-!
# Checked hierarchy package lowering

Each source module becomes a structural wrapper around one Loom-generated
body plus its source child instances. Child-input expressions are body
outputs; child-output symbolic nets are body inputs. This keeps arbitrary
slices/concatenations/logic in the checked expression lowering while the
wrapper remains purely structural.
-/

namespace Loom.Hw.ImportIR

open Loom.Hw.Backend

private def failAtHere {α : Type} (source : SourceLocation)
    (message : String) : Except String α :=
  throw s!"{source.render}: {message}"

private def Package.findModuleByName? (package : Package)
    (name : String) : Option Module :=
  package.modules.find? (·.name == name)

private def identifierStart (character : Char) : Bool :=
  character.isAlpha || character == '_'

private def identifierRest (character : Char) : Bool :=
  character.isAlphanum || character == '_' || character == '$'

private def identifierB (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest => identifierStart first && rest.all identifierRest

private def encodedIdentifier (name : String) : String :=
  "_loom_u" ++ String.intercalate "_"
    (name.toUTF8.data.toList.map fun byte => toString byte.toNat)

private def instanceName (name : String) : String :=
  "u" ++ encodedIdentifier name

private def Package.moduleName (package : Package) (module : Module) : String :=
  if module.name == package.top && identifierB module.name then module.name
  else encodedIdentifier module.name

private def Package.bodyName (package : Package) (module : Module) : String :=
  package.moduleName module ++ "__loom_body"

private def clockOrResetSignal (module : Module) (expression : Expr) :
    Option String :=
  match expression with
  | .signal 1 name _ =>
      if module.domains.any fun domain =>
          name == domain.clockPort || domain.reset.port.any (· == name) then
        some name
      else none
  | _ => none

private def directConnectionNet? (module : Module)
    (connection : InstanceConnection) : Option String :=
  match connection.direction, connection.value with
  | .input, some value => clockOrResetSignal module value
  | _, _ => none

private def bodyConnections (module : Module) : List InstanceConnection :=
  module.instances.flatMap fun inst =>
    inst.connections.filter fun connection =>
      (directConnectionNet? module connection).isNone

private def hierarchyBody (package : Package) (module : Module) : Module :=
  let connections := bodyConnections module
  let hiddenPorts := connections.map fun connection =>
    { name := connection.signal
      direction := if connection.direction == .input then .output else .input
      width := connection.width
      semanticType := "bits"
      source := connection.source }
  let hiddenOutputs := connections.filterMap fun connection =>
    match connection.direction, connection.value with
    | .input, some value =>
        some ({ name := connection.signal
                width := connection.width
                value := value
                source := connection.source } : Output)
    | _, _ => none
  { module with
    name := package.bodyName module
    ports := module.ports ++ hiddenPorts
    outputs := module.outputs ++ hiddenOutputs
    instances := [] }

private def bodyArtifact? (package : Package) (module : Module) :
    Except String ModuleArtifact := do
  let body := hierarchyBody package module
  match ← body.lowerAny? with
  | .stateless lowered =>
      return ⟨body.name, lowered.implementation.renderedVerilog⟩
  | .clocked lowered =>
      let compiled ← match lowered.reset.kind with
        | .resetless => pure <| Compile.compileResetless lowered.design lowered.edge "clk"
        | .synchronous =>
            let some _resetName := lowered.reset.port
              | failAtHere module.source "checked hierarchy body lost its reset port"
            pure <| Compile.compileForClockReset lowered.design lowered.edge
              "clk" "rst" lowered.reset.activeHigh
        | _ => failAtHere module.source "unsupported reset survived checked lowering"
      return ⟨body.name, Loom.Emit.MicroVerilog.Print.print compiled⟩

private def dataPorts (module : Module) : List Port :=
  match module.domains with
  | [] => module.ports
  | domain :: _ => module.ports.filter fun port =>
      port.name != domain.clockPort && domain.reset.port.all (· != port.name)

private def toBackendDirection : PortDirection → Loom.Hw.PortDirection
  | .input => .input
  | .output => .output
  | .inout => .input

private def wrapperPlan? (package : Package) (module : Module) :
    Except String (HierarchyEmissionPlan Unit Unit) := do
  let bodyArtifact ← bodyArtifact? package module
  let bodyPorts := (dataPorts module).map fun port =>
    ⟨port.name, port.name, toBackendDirection port.direction, port.width⟩
  let hiddenBodyPorts := (bodyConnections module).map fun connection =>
    ⟨connection.signal, connection.signal,
      if connection.direction == .input then
        Loom.Hw.PortDirection.output else Loom.Hw.PortDirection.input,
      connection.width⟩
  let bodyInstance : InstancePlan :=
    { path := "u_loom_body", moduleName := bodyArtifact.name,
      parameters := [], ports := bodyPorts ++ hiddenBodyPorts, external := false }
  let childInstances := module.instances.map fun inst =>
    { path := instanceName inst.name
      moduleName := match package.findModuleByName? inst.moduleName with
        | some child => package.moduleName child
        | none => encodedIdentifier inst.moduleName
      parameters := []
      ports := inst.connections.map fun connection =>
        ⟨connection.port,
          (directConnectionNet? module connection).getD connection.signal,
          toBackendDirection connection.direction, connection.width⟩
      external := false }
  let clockReset := match module.domains with
    | [] => []
    | domain :: _ =>
        [⟨"u_loom_body", domain.clockPort, domain.reset.port⟩]
  return {
    design :=
      { topName := package.moduleName module
        instances := bodyInstance :: childInstances
        modules := [bodyArtifact]
        externalArtifacts := []
        assumptions := [] }
    topPorts := module.ports.map fun port =>
      ⟨port.name, port.name, toBackendDirection port.direction, port.width⟩
    clockReset }

/-- All wrapper/body artifacts in deterministic package order. The package
must first pass the trusted structural checker; each body then passes the
ordinary clocked/stateless Loom lowering and each wrapper emission check. -/
def Package.artifacts? (package : Package) : Except String (List ModuleArtifact) := do
  let package ← package.check?
  let names := package.modules.map (package.moduleName ·)
  unless Inventory.uniqueB names do
    failAtHere package.source "source module names collide after HDL identifier encoding"
  let mut artifacts : List ModuleArtifact := []
  for module in package.modules do
    let plan ← wrapperPlan? package module
    let wrapper ← plan.renderTop?
    artifacts := artifacts ++ [⟨plan.design.topName, wrapper⟩] ++ plan.design.modules
  unless Inventory.uniqueB (artifacts.map (·.name)) do
    failAtHere package.source
      "wrapper/body module names collide after HDL identifier encoding"
  return artifacts

end Loom.Hw.ImportIR
