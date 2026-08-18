-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.TypedSoCTile.Design
import Loom.Hw.ExternalSystem

set_option maxHeartbeats 10000000

namespace Tools.TypedSoCTileEvidence

open Loom.Hw
open Machines.Multiclock.TypedSoCTile

private def write (directory : System.FilePath) (name text : String) : IO Unit := do
  discard <| Loom.Artifact.writeText (directory / name) text

private def sha256 (path : System.FilePath) : IO String := do
  let output ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
  if output.exitCode != 0 then throw <| IO.userError output.stderr
  match output.stdout.trimAscii.toString.splitOn " " with
  | digest :: _ => pure digest
  | [] => throw <| IO.userError s!"sha256sum returned no digest for {path}"

private def axiomAudit : IO String := do
  let root := (← IO.getEnv "LOOM_ROOT").getD "."
  let output ← IO.Process.output
    { cmd := "lake", args := #["env", "lean", "Tools/TypedSoCTileAxiomAudit.lean"],
      cwd := root }
  if output.exitCode != 0 then
    throw <| IO.userError s!"typed SoC tile axiom audit failed:\n{output.stderr}"
  if output.stdout.contains "sorryAx" || output.stdout.contains "Lean.trustCompiler" ||
      output.stdout.contains "Lean.ofReduceBool" then
    throw <| IO.userError "typed SoC tile axiom audit contains a forbidden dependency"
  pure output.stdout

private def memoryInterface (design : Design) : ComponentInterface :=
  let domain := ClockDomain.name MemoryDomain
  let inputs := design.inputs.map fun input =>
    ⟨input.name, .input, input.width, s!"BitVec[{input.width}]", domain⟩
  let outputs := design.exportedRegs.map fun output =>
    ⟨output.name, .output, output.width, s!"BitVec[{output.width}]", domain⟩
  let combOutputs := design.combOutputs.map fun output =>
    ⟨output.name, .output, output.width, s!"BitVec[{output.width}]", domain⟩
  ⟨inputs ++ outputs ++ combOutputs⟩

private def zeroPorts : PortEnv := fun _ width => 0#width

/-- Exact ordinary-Design transition contract used for the physical memory
island.  The existential input forgets undeclared environment coordinates,
but retains exact agreement on the sealed component interface. -/
def tileMemoryBehavior (reference : DomainComponent MemoryDomain)
    (_noComb : reference.implementation.design.combOutputs = []) :
    ComponentContract reference.sealed.component.interface where
  State := St
  init := fun state => state = reference.implementation.design.reset
  step := fun event input before after =>
    if event.resets (ClockDomain.name MemoryDomain) then
      after = reference.implementation.design.reset
    else if event.ticks (ClockDomain.name MemoryDomain) then
      ∃ actual, PortEnv.AgreeOn reference.sealed.component.interface.inputs
        input actual ∧
        after = reference.implementation.design.cycleOpen actual before
    else after = before
  observe := fun _ state =>
    BoundComponentGraph.componentOutputEnv reference.sealed.component
      zeroPorts state
  step_input_congr := by
    intro event state next left right agree
    split
    · rfl
    · split
      · constructor
        · rintro ⟨actual, leftActual, transition⟩
          exact ⟨actual,
            PortEnv.agreeOn_trans (PortEnv.agreeOn_symm agree) leftActual,
            transition⟩
        · rintro ⟨actual, rightActual, transition⟩
          exact ⟨actual, PortEnv.agreeOn_trans agree rightActual, transition⟩
      · rfl
  observe_input_congr := by
    intro state left right agree
    exact PortEnv.agreeOn_refl _ _

def tileMemorySpecification (reference : DomainComponent MemoryDomain)
    (noComb : reference.implementation.design.combOutputs = []) :
    ExternalComponent where
  name := "typed_soc_tile_memory_contract"
  version := "1"
  interface := reference.sealed.component.interface
  behavior := tileMemoryBehavior reference noComb
  domains := [⟨ClockDomain.name MemoryDomain, .rising, .synchronous true⟩]
  combinational := []
  latency := []

def tileMemoryWitness (reference : DomainComponent MemoryDomain)
    (noComb : reference.implementation.design.combOutputs = []) :
    BoundComponentGraph.DesignContractWitness reference
      (tileMemorySpecification reference noComb) where
  interfaceEq := rfl
  abstract := id
  init := by
    simp [tileMemorySpecification, tileMemoryBehavior, reference.implementationEq]
  tick := by
    intro event input state ticks reset
    have ticks' : event.ticks "tile_memory_clk" = true := by simpa using ticks
    have reset' : event.resets "tile_memory_clk" = false := by simpa using reset
    rw [reference.implementationEq]
    simp [tileMemorySpecification, tileMemoryBehavior, memoryDomain_name, reset', ticks',
      PortEnv.AgreeOn]
    exact ⟨input, by intros; rfl, rfl⟩
  reset := by
    intro event input state reset
    have reset' : event.resets "tile_memory_clk" = true := by simpa using reset
    rw [reference.implementationEq]
    simp [tileMemorySpecification, tileMemoryBehavior, memoryDomain_name, reset']
  hold := by
    intro event input state ticks reset
    have ticks' : event.ticks "tile_memory_clk" = false := by simpa using ticks
    have reset' : event.resets "tile_memory_clk" = false := by simpa using reset
    simp [tileMemorySpecification, tileMemoryBehavior, memoryDomain_name, reset', ticks']
  observe := by
    intro input state port member
    have independent := BoundComponentGraph.componentOutputEnv_input_independent
      reference.sealed.component
      (by simpa [reference.implementationEq] using noComb)
      input zeroPorts state
    exact congrFun (congrFun independent.symm port.name) port.width

private def selectedMemoryModule? (built : BuiltTile) : Except String String := do
  let moduleName := "typed_soc_tile_memory_contract"
  let modules := built.application.artifact.realized.artifacts.islandModules.filter
    (fun module => module.name == moduleName)
  unless modules.length == 1 do
    throw s!"expected exactly one emitted '{moduleName}' module, found {modules.length}"
  let some module := modules[0]?
    | throw "contract memory module selection failed after exact-count check"
  let declaration := "  reg [31:0] contract_memory [0:511];"
  unless (module.text.splitOn declaration).length == 2 do
    throw "contract memory reference module did not contain exactly one 512x32 declaration"
  let selected :=
    "  (* ram_style = \"block\" *) reg [31:0] contract_memory [0:511];"
  pure <| module.text.replace declaration selected

private def physicalApplication? (built : BuiltTile) :
    Except String (ExternalApplication built.system) := do
  let islandName := "tile_memory_contract"
  match found : built.system.findIsland? islandName with
  | none => throw s!"checked tile omitted '{islandName}'"
  | some island =>
    unless island.clock == ClockDomain.name MemoryDomain do
      throw s!"'{islandName}' moved from the memory clock domain"
    let component : Component :=
      { name := "typed_soc_tile_memory_reference"
        interface := memoryInterface island.design
        design := island.design }
    if interfaceOk : component.interfaceOkB = true then
      if readsOk : component.design.readsOkB = true then
        if domainOk : component.interface.ports.all
            (fun port => port.domain == ClockDomain.name MemoryDomain) = true then
          if noComb : island.design.combOutputs = [] then
            let reference : DomainComponent MemoryDomain :=
              { implementation := DomainDesign.Expert.ofDesign island.design
                sealed :=
                  { component
                    interfaceOk
                    readsOk
                    certified := built.application.certified.certificateFor found }
                implementationEq := rfl
                domainOk }
            let specification := tileMemorySpecification reference noComb
            match selectedMemoryModule? built with
            | .error message => throw message
            | .ok moduleText =>
              let binding : ExternalBinding specification :=
                { format := .verilog
                  moduleName := island.design.name
                  parameters := []
                  artifact := Loom.Artifact.Identity.ofText moduleText
                  evidence := .toolReport "openXC7" "0.8.2 / Yosys 0.38"
                    "512x32 single-clock RAM inferred, routed, and passed the retained silicon campaign"
                  assumptions :=
                    [⟨"tile_memory_rtl_contract",
                      "the exact selected module bytes implement typed_soc_tile_memory_contract v1"⟩,
                     ⟨"tile_memory_physical_ram",
                      "the inferred Xilinx 7-series block RAM implements the reference synchronous-read, byte-masked-write memory"⟩] }
              if specificationValid : specification.validB = true then
                if bindingValid : binding.validB = true then
                  let external : DomainExternal MemoryDomain :=
                    { sealed := { specification, specificationValid, binding, bindingValid }
                      domainOk := by
                        apply Bool.and_eq_true_iff.mpr
                        exact ⟨Bool.and_eq_true_iff.mpr ⟨rfl, rfl⟩, domainOk⟩ }
                  match ExternalIslandSubstitution.checkEmittedReference?
                      islandName reference external (tileMemoryWitness reference noComb) with
                  | .error message => throw message
                  | .ok substitution =>
                      ExternalApplication.check? built.application [substitution]
                else throw "typed SoC tile external memory binding is incomplete"
              else throw "typed SoC tile external memory contract is invalid"
          else throw "typed SoC tile contract memory unexpectedly gained combinational outputs"
        else throw "typed SoC tile contract memory interface left its clock domain"
      else throw "typed SoC tile contract memory reads an undeclared input"
    else throw "typed SoC tile contract memory interface no longer matches its Design"

private def manifest (rtlSha : String) (physical : Bool) : String :=
  "{\n" ++
  "  \"schema\": 1,\n" ++
  "  \"artifact\": \"typed-soc-composition-tile\",\n" ++
  "  \"plugin_profile\": {\"pipeline_depth\": 3, \"flushable_stage\": 1, \"arbiter\": \"round_robin\"},\n" ++
  "  \"plugin_resolution\": \"PASS\",\n" ++
  "  \"reset_policy\": \"coordinated\",\n" ++
  "  \"clock_relation\": \"asynchronous\",\n" ++
  "  \"core_clock\": \"tile_core_clk\",\n" ++
  "  \"memory_clock\": \"tile_memory_clk\",\n" ++
  "  \"request_width\": 66,\n" ++
  "  \"response_width\": 62,\n" ++
  "  \"fifo_depth\": 8,\n" ++
  "  \"logical_memory_lanes\": [\"internal\", \"contract_reference\"],\n" ++
  s!"  \"physical_contract_binding\": \"{if physical then "external_application" else "not_selected_in_neutral_artifact"}\",\n" ++
  s!"  \"rtl_sha256\": \"{rtlSha}\"\n" ++
  "}\n"

private def runBuilt (built : BuiltTile) (directory : System.FilePath)
    (physical : Bool) : IO Unit := do
  let artifact := built.application.artifact
  match artifact.emissionCheck with
  | .error message => throw <| IO.userError message
  | .ok _ => pure ()
  IO.FS.createDirAll directory
  if physical then
    match physicalApplication? built with
    | .ok application => application.emit directory
    | .error message => throw <| IO.userError message
  else artifact.emit directory
  let rtlSha ← sha256 (directory / "system.v")
  write directory "tile-manifest.json" (manifest rtlSha physical)
  write directory "theorem-axioms.txt" (← axiomAudit)
  let names : Array System.FilePath :=
    if physical then #["system.v", "crossings.md", "clock_constraints.md",
      "external_islands.md", "tile-manifest.json", "theorem-axioms.txt"]
    else #["system.v", "crossings.md", "clock_constraints.md",
      "tile-manifest.json", "theorem-axioms.txt"]
  let hashes ← names.mapM fun name => do
    pure s!"{← sha256 (directory / name)}  {name}"
  write directory "SHA256SUMS" (String.intercalate "\n" hashes.toList ++ "\n")
  IO.println s!"TYPED_SOC_TILE_EVIDENCE_OK directory={directory} rtl_sha256={rtlSha}"

def run (directory : System.FilePath) (physical : Bool := false) : IO Unit := do
  unless pluginSelectionMatches do
    throw <| IO.userError "typed SoC tile plugin resolution differs from the certified release profile"
  match buildCertifiedArtifact with
  | .ok built => runBuilt built directory physical
  | .error message => throw <| IO.userError message

end Tools.TypedSoCTileEvidence

def main (args : List String) : IO Unit := do
  match args with
  | [directory] => Tools.TypedSoCTileEvidence.run directory
  | ["--physical", directory] => Tools.TypedSoCTileEvidence.run directory true
  | _ => throw (IO.userError
      "usage: typedSoCTileEvidence [--physical] OUTPUT_DIRECTORY")
