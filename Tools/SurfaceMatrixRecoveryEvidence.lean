-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SurfaceMatrix.Recovery

namespace Tools.SurfaceMatrixRecoveryEvidence

open Loom.Hw
open Machines.Multiclock.SurfaceMatrix.Recovery

private def sha256 (path : System.FilePath) : IO String := do
  let output ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
  if output.exitCode != 0 then throw <| IO.userError output.stderr
  pure ((output.stdout.trimAscii.toString.splitOn " ").head!)

def run (directory : System.FilePath) : IO Unit := do
  match certifiedArtifact.emissionCheck with
  | .error message => throw <| IO.userError message
  | .ok _ => pure ()
  IO.FS.createDirAll directory
  certifiedArtifact.emit directory
  let digest ← sha256 (directory / "system.v")
  discard <| Loom.Artifact.writeText (directory / "system.v.sha256")
    s!"{digest}  system.v\n"
  IO.println s!"SURFACE_MATRIX_RECOVERY_EVIDENCE_OK directory={directory} rtl_sha256={digest}"

end Tools.SurfaceMatrixRecoveryEvidence

def main (args : List String) : IO Unit := do
  match args with
  | [directory] => Tools.SurfaceMatrixRecoveryEvidence.run directory
  | _ => throw (IO.userError
      "usage: surfaceMatrixRecoveryEvidence OUTPUT_DIRECTORY")
