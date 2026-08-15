-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SurfaceMatrix.RegisteredBram

namespace Tools.SurfaceRegisteredBramEvidence

open Loom.Hw
open Machines.Multiclock.SurfaceMatrix.RegisteredBram

private def write (directory : System.FilePath) (name text : String) : IO Unit := do
  discard <| Loom.Artifact.writeText (directory / name) text

private def sha256 (path : System.FilePath) : IO String := do
  let output ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
  if output.exitCode != 0 then throw <| IO.userError output.stderr
  match output.stdout.trimAscii.toString.splitOn " " with
  | digest :: _ => pure digest
  | [] => throw <| IO.userError "sha256sum returned no digest"

def run (directory : System.FilePath) : IO Unit := do
  match certifiedArtifact.emissionCheck with
  | .error message => throw <| IO.userError message
  | .ok _ => pure ()
  IO.FS.createDirAll directory
  certifiedArtifact.emit directory
  write directory "storage-profile.md" <| String.intercalate "\n" [
    "# Registered-BRAM storage profile", "",
    "- target family: Xilinx 7-series",
    "- logical channel: surface_ordinary_d4",
    "- width: 32", "- depth: 4", "- read latency: 1",
    "- presentation: registered", "- clock relationship: independent", "",
    System.renderExternalAssumptions
      certifiedArtifact.realized.artifacts.externalAssumptions]
  let names : Array System.FilePath := #["system.v", "crossings.md",
    "clock_constraints.md", "storage-profile.md"]
  let hashes ← names.mapM fun name => do
    pure s!"{← sha256 (directory / name)}  {name}"
  write directory "SHA256SUMS" (String.intercalate "\n" hashes.toList ++ "\n")
  IO.println s!"SURFACE_REGISTERED_BRAM_EVIDENCE_OK directory={directory} rtl_sha256={← sha256 (directory / "system.v")}"

end Tools.SurfaceRegisteredBramEvidence

def main (args : List String) : IO Unit := do
  match args with
  | [directory] => Tools.SurfaceRegisteredBramEvidence.run directory
  | _ => throw <| IO.userError "usage: surfaceRegisteredBramEvidence OUTPUT_DIRECTORY"
