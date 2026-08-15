-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SurfaceMatrix.Design

/-!
# Deterministic producer for the multiclock surface matrix

This writes the theorem-bound RTL and neutral physical intent before any
target flow runs.  Target-specific scripts add routed/signoff/silicon records
without modifying this directory's canonical inputs.
-/

namespace Tools.SurfaceMatrixEvidence

open Loom.Hw
open Machines.Multiclock.SurfaceMatrix

private def jsonString (value : String) : String :=
  "\"" ++ ((value.replace "\\" "\\\\").replace "\"" "\\\"") ++ "\""

private def write (directory : System.FilePath) (name text : String) : IO Unit := do
  discard <| Loom.Artifact.writeText (directory / name) text

private def sha256 (path : System.FilePath) : IO String := do
  let output ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
  if output.exitCode != 0 then throw <| IO.userError output.stderr
  match output.stdout.trimAscii.toString.splitOn " " with
  | digest :: _ => pure digest
  | [] => throw <| IO.userError s!"sha256sum returned no digest for {path}"

private def modeJson : EndpointMode → String
  | .ordinary => "\"ordinary\""
  | .fullRate => "\"full_rate\""

private def laneJson (spec : LaneSpec) : String :=
  let source := "source_" ++ spec.label
  let sink := "sink_" ++ spec.label
  let sourceRunLimit := jsonString (source ++ "__run_limit")
  let sourceEnable := jsonString (source ++ "__source_enable")
  let sinkRunLimit := jsonString (sink ++ "__run_limit")
  let sinkEnable := jsonString (sink ++ "__sink_enable")
  let offered := jsonString (source ++ "__o_offered")
  let accepted := jsonString (source ++ "__o_accepted")
  let sourceBackpressure := jsonString (source ++ "__o_backpressure")
  let delivered := jsonString (sink ++ "__o_delivered")
  let expectedSequence := jsonString (sink ++ "__o_expected_sequence")
  let digest := jsonString (sink ++ "__o_digest")
  let stickyDataError := jsonString (sink ++ "__o_sticky_data_error")
  let stickyGapError := jsonString (sink ++ "__o_sticky_gap_error")
  let supplyGaps := jsonString (sink ++ "__o_supply_gaps")
  let sinkBackpressure := jsonString (sink ++ "__o_backpressure_ticks")
  let sinkTicks := jsonString (sink ++ "__o_ticks")
  "{" ++
    s!"\"label\":{jsonString spec.label}," ++
    s!"\"channel\":{jsonString spec.channel.name}," ++
    s!"\"depth\":{spec.depth},\"endpoint\":{modeJson spec.mode}," ++
    s!"\"bubble_free_saturation_required\":{if spec.expectsBubbleFree then "true" else "false"}," ++
    s!"\"source_island\":{jsonString source},\"sink_island\":{jsonString sink}," ++
    "\"ports\":{" ++
      s!"\"run_limit_source\":{sourceRunLimit}," ++
      s!"\"source_enable\":{sourceEnable}," ++
      s!"\"run_limit_sink\":{sinkRunLimit}," ++
      s!"\"sink_enable\":{sinkEnable}," ++
      s!"\"offered\":{offered}," ++
      s!"\"accepted\":{accepted}," ++
      s!"\"source_backpressure\":{sourceBackpressure}," ++
      s!"\"delivered\":{delivered}," ++
      s!"\"expected_sequence\":{expectedSequence}," ++
      s!"\"digest\":{digest}," ++
      s!"\"sticky_data_error\":{stickyDataError}," ++
      s!"\"sticky_gap_error\":{stickyGapError}," ++
      s!"\"supply_gaps\":{supplyGaps}," ++
      s!"\"sink_backpressure_ticks\":{sinkBackpressure}," ++
      s!"\"sink_ticks\":{sinkTicks}" ++
    "}}"

private def manifest : String :=
  "{\n" ++
  "  \"schema\": 1,\n" ++
  "  \"artifact\": \"multiclock-surface-matrix\",\n" ++
  "  \"reset_policy\": \"coordinated\",\n" ++
  "  \"clock_relation\": \"asynchronous\",\n" ++
  "  \"source_clock\": \"surface_source_clk\",\n" ++
  "  \"sink_clock\": \"surface_sink_clk\",\n" ++
  "  \"payload_width\": 32,\n" ++
  "  \"digest\": \"xor of delivered sequence values\",\n" ++
  "  \"lanes\": [\n    " ++
    String.intercalate ",\n    " (laneSpecs.map laneJson) ++ "\n  ]\n}\n"

private def axiomAudit : IO String := do
  let root := (← IO.getEnv "LOOM_ROOT").getD "."
  let output ← IO.Process.output
    { cmd := "lake", args := #["env", "lean", "Tools/SurfaceMatrixAxiomAudit.lean"],
      cwd := root }
  if output.exitCode != 0 then
    throw <| IO.userError s!"surface-matrix axiom audit failed:\n{output.stderr}"
  if output.stdout.contains "sorryAx" || output.stdout.contains "Lean.trustCompiler" ||
      output.stdout.contains "Lean.ofReduceBool" then
    throw <| IO.userError "surface-matrix axiom audit contains a forbidden dependency"
  pure output.stdout

def run (directory : System.FilePath) : IO Unit := do
  match certifiedArtifact.emissionCheck with
  | .error message => throw <| IO.userError message
  | .ok _ => pure ()
  IO.FS.createDirAll directory
  certifiedArtifact.emit directory
  write directory "matrix-manifest.json" manifest
  write directory "theorem-axioms.txt" (← axiomAudit)
  let names : Array System.FilePath := #["system.v", "crossings.md",
    "clock_constraints.md", "matrix-manifest.json", "theorem-axioms.txt"]
  let hashes ← names.mapM fun name => do
    pure s!"{← sha256 (directory / name)}  {name}"
  write directory "SHA256SUMS" (String.intercalate "\n" hashes.toList ++ "\n")
  IO.println (s!"SURFACE_MATRIX_EVIDENCE_OK directory={directory} " ++
    s!"rtl_sha256={← sha256 (directory / "system.v")}")

end Tools.SurfaceMatrixEvidence

def main (args : List String) : IO Unit := do
  match args with
  | [directory] => Tools.SurfaceMatrixEvidence.run directory
  | _ => throw <| IO.userError "usage: surfaceMatrixEvidence OUTPUT_DIRECTORY"
