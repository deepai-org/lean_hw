-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SoCFabricGauntlet.StorageNeutrality

namespace Tools.SoCFabricStorageNeutralityEmit

open Machines.Multiclock.SoCFabricGauntlet
open Machines.Multiclock.SoCFabricGauntlet.StorageNeutrality

def runUnqualifiedEvidence
    (neutralDirectory bramDirectory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll neutralDirectory
  IO.FS.createDirAll bramDirectory
  certifiedArtifact.emit neutralDirectory
  bramArtifact.emit bramDirectory

end Tools.SoCFabricStorageNeutralityEmit

def main (args : List String) : IO Unit := do
  match args with
  | [neutral, bram, "--reproduce-known-bad-openxc7"] =>
      Tools.SoCFabricStorageNeutralityEmit.runUnqualifiedEvidence neutral bram
  | [_, _] => throw (IO.userError <| String.intercalate "\n" <|
      ["refusing to emit the unqualified openXC7 registered-storage artifact:"] ++
      Machines.Multiclock.SoCFabricGauntlet.StorageNeutrality.openXc7TargetPolicyFailures ++
      ["pass --reproduce-known-bad-openxc7 only to reproduce the recorded failing evidence"])
  | _ => throw (IO.userError
      "usage: socFabricStorageNeutralityEmit NEUTRAL_DIRECTORY BRAM_DIRECTORY --reproduce-known-bad-openxc7")
