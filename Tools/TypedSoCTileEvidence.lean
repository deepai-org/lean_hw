-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.TypedSoCTile.Design

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

private def manifest (rtlSha : String) : String :=
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
  "  \"physical_contract_binding\": \"not_selected_in_neutral_artifact\",\n" ++
  s!"  \"rtl_sha256\": \"{rtlSha}\"\n" ++
  "}\n"

private def runBuilt (built : BuiltTile) (directory : System.FilePath) : IO Unit := do
  let artifact := built.application.artifact
  match artifact.emissionCheck with
  | .error message => throw <| IO.userError message
  | .ok _ => pure ()
  IO.FS.createDirAll directory
  artifact.emit directory
  let rtlSha ← sha256 (directory / "system.v")
  write directory "tile-manifest.json" (manifest rtlSha)
  write directory "theorem-axioms.txt" (← axiomAudit)
  let names : Array System.FilePath := #["system.v", "crossings.md",
    "clock_constraints.md", "tile-manifest.json", "theorem-axioms.txt"]
  let hashes ← names.mapM fun name => do
    pure s!"{← sha256 (directory / name)}  {name}"
  write directory "SHA256SUMS" (String.intercalate "\n" hashes.toList ++ "\n")
  IO.println s!"TYPED_SOC_TILE_EVIDENCE_OK directory={directory} rtl_sha256={rtlSha}"

def run (directory : System.FilePath) : IO Unit := do
  unless pluginSelectionMatches do
    throw <| IO.userError "typed SoC tile plugin resolution differs from the certified release profile"
  match buildCertifiedArtifact with
  | .ok built => runBuilt built directory
  | .error message => throw <| IO.userError message

end Tools.TypedSoCTileEvidence

def main (args : List String) : IO Unit := do
  match args with
  | [directory] => Tools.TypedSoCTileEvidence.run directory
  | _ => throw <| IO.userError "usage: typedSoCTileEvidence OUTPUT_DIRECTORY"
