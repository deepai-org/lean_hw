-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ExternalHierarchy
import Loom.Hw.Multiclock

/-!
# Contract-bound external System islands

Loom's semantic and proof layers continue to use an ordinary certified
`Design` for every island.  This optional release layer permits the exact RTL
module for one island to be replaced by external Verilog bytes.  Construction
requires a typed contract witness for the reference `Design`; the emitted
artifact retains the external byte identity and every named assumption.

This is deliberately technology-neutral.  FPGA primitives, ASIC macros,
vendor tools, and physical evidence belong in the supplied binding rather
than in `System` or its schedule semantics.  The external bytes remain an
explicit assumption boundary: Loom does not claim that matching interfaces
prove their behavior.
-/

namespace Loom.Hw

universe u v

/-- Erased release data produced only after checking a typed reference island
against a contract-bound external component.  The constructor is private so a
caller cannot bypass the membership, interface, domain, format, and exact-byte
checks performed by `check?`. -/
structure ExternalIslandSubstitution (system : System) where
  private mk ::
  islandName : String
  moduleName : String
  contractName : String
  contractVersion : String
  moduleText : String
  artifact : Loom.Artifact.Identity
  assumptions : List NamedAssumption
  evidence : ExternalEvidence

namespace ExternalIslandSubstitution

/-- Bind an external implementation to the exact certified reference island.

`witness` proves the reference `Design` implements the behavioral contract.
`islandFound` and `designEq` prevent a contract proved about a cousin design
from authorizing replacement of the emitted island.  Exact external bytes are
decoded and round-tripped before they enter the release object. -/
def check? {δ : Type v} [ClockDomain δ] {system : System}
    (owner : DomainIslandHandle δ)
    (reference : DomainComponent δ)
    (external : DomainExternal δ)
    (_witness : BoundComponentGraph.DesignContractWitness
      reference external.sealed.specification)
    (islandFound : system.findIsland? owner.name = some owner.toSystemIsland)
    (designEq : owner.design.design = reference.implementation.design) :
    Except String (ExternalIslandSubstitution system) := do
  let _ := islandFound
  let _ := designEq
  let specification := external.sealed.specification
  let binding := external.sealed.binding
  unless binding.format == .verilog do
    throw s!"external island '{owner.name}' must use Verilog bytes"
  unless binding.parameters.isEmpty do
    throw s!"external island '{owner.name}' cannot use unrendered parameters"
  unless binding.moduleName == owner.design.design.name do
    throw s!"external island '{owner.name}' must retain emitted module name '{owner.design.design.name}'"
  unless specification.domains ==
      [⟨ClockDomain.name δ, .rising, .synchronous true⟩] do
    throw s!"external island '{owner.name}' must match Loom's rising-edge synchronous-reset island convention"
  let some text := String.fromUTF8? binding.artifact.bytes
    | throw s!"external island '{owner.name}' artifact is not valid UTF-8 Verilog"
  unless text.toUTF8 == binding.artifact.bytes do
    throw s!"external island '{owner.name}' artifact did not round-trip to its exact recorded bytes"
  return .mk owner.name binding.moduleName specification.name
    specification.version text binding.artifact binding.assumptions binding.evidence

end ExternalIslandSubstitution

/-- A certified System application with an optional, exact, assumption-bound
replacement for selected island modules.  Simulation and proofs continue to
use `base`; only the explicitly named release modules are substituted. -/
structure ExternalApplication (system : System) where
  private mk ::
  base : System.Application system
  substitutions : List (ExternalIslandSubstitution system)

namespace ExternalApplication

private def substitutionNames {system : System}
    (substitutions : List (ExternalIslandSubstitution system)) : List String :=
  substitutions.map (·.islandName)

/-- Collect independently checked substitutions, rejecting duplicate island
or module ownership before any artifact can be rendered. -/
def check? {system : System} (base : System.Application system)
    (substitutions : List (ExternalIslandSubstitution system)) :
    Except String (ExternalApplication system) := do
  unless Inventory.uniqueB (substitutionNames substitutions) do
    throw "external System application contains duplicate island substitutions"
  unless Inventory.uniqueB (substitutions.map (·.moduleName)) do
    throw "external System application contains duplicate module substitutions"
  return .mk base substitutions

private def replaceIslandModule {system : System}
    (application : ExternalApplication system)
    (module : Backend.ModuleArtifact) : String :=
  match application.substitutions.find? (·.moduleName == module.name) with
  | some replacement => replacement.moduleText
  | none => module.text

private def insertModule (modules : List (String × String))
    (candidate : String × String) : List (String × String) :=
  if modules.any (fun module => module.1 = candidate.1) then modules
  else modules ++ [candidate]

private def uniqueModules (modules : List (String × String)) :
    List (String × String) := modules.foldl insertModule []

/-- Exact RTL selected by the external-island release path.  The top-level,
channel controllers, constraints, and all unsubstituted islands remain the
same structured values as the certified base application. -/
def renderedVerilog {system : System}
    (application : ExternalApplication system) : String :=
  let artifact := application.base.artifact
  let physical := artifact.realized.artifacts
  let components := uniqueModules
    (artifact.bindings.flatMap (·.componentModules))
  String.intercalate "\n\n" <|
    physical.islandModules.map application.replaceIslandModule ++
    components.map (·.2) ++
    physical.instances.map (·.moduleText) ++
    [physical.topModule.render]

def renderedUTF8 {system : System}
    (application : ExternalApplication system) : ByteArray :=
  application.renderedVerilog.toUTF8

theorem renderedUTF8_eq {system : System}
    (application : ExternalApplication system) :
    application.renderedUTF8 = application.renderedVerilog.toUTF8 := rfl

/-- Collision-free identities for every external byte tree selected by this
release.  Integrations may derive hashes, but these exact bytes are the
authoritative identity inside Loom. -/
def externalArtifacts {system : System}
    (application : ExternalApplication system) : List Loom.Artifact.Identity :=
  application.substitutions.map (·.artifact)

private def evidenceText : ExternalEvidence → String
  | .assumptionOnly => "assumption only"
  | .toolReport tool version result =>
      s!"tool report: {tool} {version}: {result}"

private def substitutionReport {system : System}
    (replacement : ExternalIslandSubstitution system) : String :=
  String.intercalate "\n" <|
    [s!"## `{replacement.islandName}`",
     "",
     s!"- Module: `{replacement.moduleName}`",
     s!"- Contract: `{replacement.contractName}` version `{replacement.contractVersion}`",
     s!"- Exact artifact bytes retained: {replacement.artifact.byteCount}",
     s!"- Evidence: {evidenceText replacement.evidence}",
     "",
     "Named assumptions:"] ++
    (if replacement.assumptions.isEmpty then ["- None"] else
      replacement.assumptions.map fun assumption =>
        s!"- `{assumption.name}`: {assumption.statement}")

/-- Human-readable view of the exact machine-retained substitution boundary.
This is a Markdown release artifact, not a CSV/TSV interface required from an
ordinary application author. -/
def report {system : System} (application : ExternalApplication system) : String :=
  String.intercalate "\n\n" <|
    ["# External System islands",
     "",
     "These modules replace certified reference islands only at emission. " ++
       "Their behavioral equivalence to the named contracts is an explicit " ++
       "external assumption, not a Loom kernel theorem."] ++
    application.substitutions.map substitutionReport

/-- Recheck both the certified base artifact and the substitution inventory.
Every selected module must occur exactly once in the base island-module list,
and its stored text must still be the exact recorded byte identity. -/
def emissionCheck {system : System}
    (application : ExternalApplication system) : Except String Unit := do
  application.base.artifact.emissionCheck
  let modules := application.base.artifact.realized.artifacts.islandModules
  for replacement in application.substitutions do
    unless replacement.moduleText.toUTF8 == replacement.artifact.bytes do
      throw s!"external island '{replacement.islandName}' no longer matches its exact artifact identity"
    unless (modules.filter (·.name == replacement.moduleName)).length == 1 do
      throw s!"external island '{replacement.islandName}' does not identify exactly one emitted island module"

/-- Exact release files.  Existing physical/crossing reports are unchanged;
one additional Markdown inventory records the external byte and assumption
boundary. -/
def emissionArtifacts {system : System}
    (application : ExternalApplication system) : List System.EmissionArtifact :=
  let base := application.base.artifact.emissionArtifacts.map fun emitted =>
    if emitted.kind = .rtl then { emitted with text := application.renderedVerilog }
    else emitted
  base ++ [{ kind := .inventory
             relativePath := "external_islands.md"
             text := application.report
             crossingKeys := system.connections.map SystemConnection.key }]

def emit {system : System} (application : ExternalApplication system)
    (directory : System.FilePath) : IO Unit := do
  match application.emissionCheck with
  | .ok _ => pure ()
  | .error message => throw <| IO.userError message
  for emitted in application.emissionArtifacts do
    let path := directory / emitted.relativePath
    let changed ← Loom.Artifact.writeText path emitted.text
    IO.println s!"{path} {if changed then "written" else "unchanged"}"

end ExternalApplication

end Loom.Hw
