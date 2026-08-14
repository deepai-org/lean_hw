-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.ClockGauntlet.Artifact
import Tools.ClockGauntletCampaign

/-!
# Clock Gauntlet evidence producer

This is the sole supported writer for the portable evidence files.  It takes
one output directory, rejects an uncertifiable artifact or failed campaign,
and never substitutes a second RTL renderer.
-/

namespace Tools.ClockGauntletEvidence

open Loom.Hw
open Machines.Multiclock.ClockGauntlet

private def jsonString (value : String) : String :=
  "\"" ++ ((value.replace "\\" "\\\\").replace "\"" "\\\"") ++ "\""

private def optionJson : Option String → String
  | some value => jsonString value
  | none => "null"

private def policyJson : FullCoTickPolicy → String
  | .refusePush => "\"refuse_push\""
  | .exchange => "\"exchange\""

private def inventoryRow (info : System.CrossingInfo) : String :=
  "{" ++ s!"\"channel\":{jsonString info.channel},\"width\":{info.width}," ++
  s!"\"depth\":{info.depth},\"policy\":{policyJson info.policy}," ++
  s!"\"source\":{jsonString info.source},\"source_clock\":{optionJson info.sourceClock}," ++
  s!"\"sink\":{jsonString info.sink},\"sink_clock\":{optionJson info.sinkClock}" ++ "}"

private def inventoryJson : String :=
  let rows := system.crossingInventory.map inventoryRow
  "{\n  \"schema\":1,\n  \"crossings\":[\n    " ++
    String.intercalate ",\n    " rows ++ "\n  ]\n}\n"

private def generatedXdc : String :=
  let rows := system.crossingInventory.filterMap fun info => do
    let sourceClock ← info.sourceClock
    let sinkClock ← info.sinkClock
    if sourceClock = sinkClock then none else
      some <| "set_clock_groups -asynchronous " ++
        s!"-group [get_clocks {sourceClock}] -group [get_clocks {sinkClock}]"
  "# Generated from the checked Clock Gauntlet crossing inventory.\n" ++
    String.intercalate "\n" rows ++ "\n" ++
    "# Compiler-produced two-stage Gray-pointer synchronizers.\n" ++
    "set_property ASYNC_REG TRUE [get_cells -hier -regexp {.*(read_gray_sync|write_gray_sync)[01].*}]\n"

private def write (directory : System.FilePath) (name text : String) : IO Unit := do
  let path := directory / name
  let _ ← Loom.Artifact.writeText path text

private def sha256 (path : System.FilePath) : IO String := do
  let output ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
  if output.exitCode != 0 then
    throw <| IO.userError s!"sha256sum failed: {output.stderr}"
  match output.stdout.trimAscii.toString.splitOn " " with
  | digest :: _ => pure digest
  | [] => throw <| IO.userError "sha256sum returned no digest"

private def axiomAudit : IO String := do
  let root := (← IO.getEnv "LOOM_ROOT").getD "."
  let output ← IO.Process.output
    { cmd := "lake", args := #["env", "lean", "Tools/ClockGauntletAxiomAudit.lean"],
      cwd := root }
  if output.exitCode != 0 then
    throw <| IO.userError s!"Clock Gauntlet axiom audit failed:\n{output.stderr}"
  pure output.stdout

def run (directory : System.FilePath) : IO Unit := do
  match certifiedArtifact.emissionCheck with
  | .ok _ => pure ()
  | .error message => throw <| IO.userError message
  IO.FS.createDirAll directory
  write directory "system.v" certifiedArtifact.rtlArtifact.text
  let digest ← sha256 (directory / "system.v")
  write directory "system.v.sha256" s!"{digest}  system.v\n"
  write directory "crossing-inventory.json" inventoryJson
  write directory "generated-constraints.xdc" generatedXdc
  write directory "axiom-audit.txt" (← axiomAudit)
  let (campaignsPassed, simulationJson) :=
    Tools.ClockGauntletCampaign.evidenceResultJson
  write directory "simulation-result.json" simulationJson
  if !campaignsPassed then
    throw <| IO.userError "certified Clock Gauntlet campaign failed"
  IO.println s!"CLOCK_GAUNTLET_EVIDENCE_OK directory={directory} sha256={digest}"

end Tools.ClockGauntletEvidence

def main (args : List String) : IO Unit := do
  match args with
  | [directory] => Tools.ClockGauntletEvidence.run directory
  | _ => throw <| IO.userError "usage: clockGauntletEvidence OUTPUT_DIRECTORY"
