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
  if identifierB name && !name.startsWith "u_loom_" then name
  else "u" ++ encodedIdentifier name

private def Package.moduleName (_package : Package) (module : Module) : String :=
  if identifierB module.name && !module.name.endsWith "__loom_body" then module.name
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

private def lowerBodyArtifact? (source : SourceLocation) (body : Module) :
    Except String ModuleArtifact := do
  match ← body.lowerAny? with
  | .stateless lowered =>
      return ⟨body.name, lowered.implementation.renderedVerilog⟩
  | .clocked lowered =>
      let compiled ← match lowered.reset.kind with
        | .resetless => pure <| Compile.compileResetless lowered.design lowered.edge "clk"
        | .synchronous =>
            let some _resetName := lowered.reset.port
              | failAtHere source "checked hierarchy body lost its reset port"
            pure <| Compile.compileForClockReset lowered.design lowered.edge
              "clk" "rst" lowered.reset.activeHigh
        | _ => failAtHere source "unsupported reset survived checked lowering"
      return ⟨body.name, Loom.Emit.MicroVerilog.Print.print compiled⟩

private def bodyArtifact? (package : Package) (module : Module) :
    Except String ModuleArtifact :=
  lowerBodyArtifact? module.source (hierarchyBody package module)

private def dataPorts (module : Module) : List Port :=
  module.ports.filter fun port => module.domains.all fun domain =>
    port.name != domain.clockPort && domain.reset.port.all (· != port.name)

private def registerInputPort (register : Register) : Port :=
  { name := register.name, direction := .input, width := register.width,
    semanticType := "bits", source := register.source }

private def childOutputPorts (module : Module) : List Port :=
  (bodyConnections module).filterMap fun connection =>
    if connection.direction == .output then
      some { name := connection.signal, direction := .input,
             width := connection.width, semanticType := "bits",
             source := connection.source }
    else none

private def domainBodyName (package : Package) (module : Module)
    (domain : ClockDomain) : String :=
  package.bodyName module ++ "__domain" ++ encodedIdentifier domain.name

private def combBodyName (package : Package) (module : Module) : String :=
  package.bodyName module ++ "__comb"

private def combOutputName (name : String) : String :=
  "__loom_top_output" ++ encodedIdentifier name

private def stateNetName (name : String) : String :=
  "__loom_state" ++ encodedIdentifier name

private def domainBody? (package : Package) (module : Module)
    (domain : ClockDomain) : Except String Module := do
  let registers := module.registers.filter (·.domain == some domain.name)
  if registers.isEmpty then
    failAtHere domain.source s!"multi-domain import domain '{domain.name}' owns no registers"
  let some clockPort := module.ports.find? fun port =>
      port.name == domain.clockPort && port.direction == .input && port.width == 1
    | failAtHere domain.source s!"multi-domain clock port '{domain.clockPort}' is missing"
  -- Only the owning clock is structural metadata for this body.  Foreign
  -- clocks (and resets) remain ordinary data dependencies if the source D
  -- cone reads them; the owning reset must also remain present for checked
  -- synchronous-reset lowering.
  let dataInputs := module.ports.filter fun port =>
    port.direction == .input && port.name != domain.clockPort
  let foreignRegisters := module.registers.filter (·.domain != some domain.name)
  return {
    name := domainBodyName package module domain
    ports := clockPort :: dataInputs ++ foreignRegisters.map registerInputPort ++
      childOutputPorts module
    domains := [domain]
    registers
    memories := []
    outputs := registers.map fun register =>
      { name := "o_" ++ register.name, width := register.width,
        value := .signal register.width register.name register.source,
        source := register.source }
    instances := []
    unsupported := []
    source := module.source }

private def combinationalBody (package : Package) (module : Module) : Module :=
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
        some ({ name := connection.signal, width := connection.width,
                value, source := connection.source } : Output)
    | _, _ => none
  { module with
    name := combBodyName package module
    -- Combinational source cones may legitimately observe a clock pin (for
    -- example while deriving an SDRAM clock output), so retain every original
    -- port here.  State ownership, not port deletion, separates the domains.
    ports := module.ports.map (fun port =>
      if port.direction == .output then { port with name := combOutputName port.name }
      else port) ++ hiddenPorts ++ module.registers.map registerInputPort
    domains := []
    registers := []
    memories := []
    outputs := module.outputs.map (fun output =>
      { output with name := combOutputName output.name }) ++ hiddenOutputs
    instances := [] }

private def toBackendDirection : PortDirection → Loom.Hw.PortDirection
  | .input => .input
  | .output => .output
  | .inout => .input

private def wrapperPlan? (package : Package) (module : Module) :
    Except String (HierarchyEmissionPlan Unit Unit) := do
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
  let mut bodyArtifacts : List ModuleArtifact := []
  let mut bodyInstances : List InstancePlan := []
  let mut clockReset : List InstanceClockReset := []
  if module.domains.length > 1 then
    unless module.memories.isEmpty do
      failAtHere module.source
        "multi-domain modules with memories require explicit memory-domain ownership"
    unless module.registers.all (fun register => register.domain.any fun name =>
        module.domains.any (·.name == name)) do
      failAtHere module.source
        "every multi-domain register must name exactly one declared domain"
    let combBody := combinationalBody package module
    let combArtifact ← lowerBodyArtifact? module.source combBody
    bodyArtifacts := bodyArtifacts ++ [combArtifact]
    bodyInstances := bodyInstances ++ [{
      path := "u_loom_comb", moduleName := combArtifact.name,
      parameters := [], external := false,
      ports := combBody.ports.map fun port =>
        let net := match module.registers.find? (·.name == port.name) with
          | some register => stateNetName register.name
          | none => match module.ports.find? fun original =>
            original.direction == .output && combOutputName original.name == port.name with
            | some original => original.name
            | none => port.name
        ⟨port.name, net, toBackendDirection port.direction, port.width⟩ }]
    for index in List.range module.domains.length do
      let some domain := module.domains[index]?
        | failAtHere module.source "multi-domain inventory changed during emission"
      let domainBody ← domainBody? package module domain
      let artifact ← lowerBodyArtifact? module.source domainBody
      let path := s!"u_loom_domain_{index}"
      let inputPorts := domainBody.ports.filter (·.name != domain.clockPort)
      let owned := module.registers.filter (·.domain == some domain.name)
      bodyArtifacts := bodyArtifacts ++ [artifact]
      bodyInstances := bodyInstances ++ [{
        path, moduleName := artifact.name, parameters := [], external := false,
        ports := inputPorts.map (fun port =>
          let net := if module.registers.any (·.name == port.name) then
            stateNetName port.name else port.name
          ⟨port.name, net, Loom.Hw.PortDirection.input, port.width⟩) ++
          owned.map (fun register =>
            ⟨"o_" ++ register.name, stateNetName register.name,
              Loom.Hw.PortDirection.output, register.width⟩) }]
      clockReset := clockReset ++ [⟨path, domain.clockPort, domain.reset.port⟩]
  else
    let bodyArtifact ← bodyArtifact? package module
    let bodyPorts := (dataPorts module).map fun port =>
      ⟨port.name, port.name, toBackendDirection port.direction, port.width⟩
    let hiddenBodyPorts := (bodyConnections module).map fun connection =>
      ⟨connection.signal, connection.signal,
        if connection.direction == .input then
          Loom.Hw.PortDirection.output else Loom.Hw.PortDirection.input,
        connection.width⟩
    bodyArtifacts := [bodyArtifact]
    bodyInstances := [{
      path := "u_loom_body", moduleName := bodyArtifact.name,
      parameters := [], ports := bodyPorts ++ hiddenBodyPorts, external := false }]
    clockReset := match module.domains with
      | [] => []
      | domain :: _ => [⟨"u_loom_body", domain.clockPort, domain.reset.port⟩]
  return {
    design :=
      { topName := package.moduleName module
        instances := bodyInstances ++ childInstances
        modules := bodyArtifacts
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
