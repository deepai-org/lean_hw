-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SoCFabricGauntlet.Recovery

namespace Tools.SoCFabricRecoveryEmit

open Machines.Multiclock.SoCFabricGauntlet.Recovery

def run (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  recoveryFabric.application.artifact.emit directory

end Tools.SoCFabricRecoveryEmit

def main (args : List String) : IO Unit := do
  match args with
  | [directory] => Tools.SoCFabricRecoveryEmit.run directory
  | _ => throw (IO.userError "usage: socFabricRecoveryEmit DIRECTORY")
