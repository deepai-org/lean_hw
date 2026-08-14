-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SoCFabricGauntlet.StorageNeutrality

namespace Tools.SoCFabricStorageNeutralityEmit

open Machines.Multiclock.SoCFabricGauntlet
open Machines.Multiclock.SoCFabricGauntlet.StorageNeutrality

def run (neutralDirectory bramDirectory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll neutralDirectory
  IO.FS.createDirAll bramDirectory
  certifiedArtifact.emit neutralDirectory
  bramArtifact.emit bramDirectory

end Tools.SoCFabricStorageNeutralityEmit

def main (args : List String) : IO Unit := do
  match args with
  | [neutral, bram] =>
      Tools.SoCFabricStorageNeutralityEmit.run neutral bram
  | _ => throw (IO.userError
      "usage: socFabricStorageNeutralityEmit NEUTRAL_DIRECTORY BRAM_DIRECTORY")
