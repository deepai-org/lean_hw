-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
-- Release gate: the parsed LNP64-u witness equals the verified compiler's
-- own output, `Design.toProgram`. Run via `lake env lean --run` after
-- GeneratedRelease/Lnp64u/ProgramData is compiled.
import Loom.Release.ToProgram
import GeneratedRelease.Lnp64u.ProgramData
import Machines.Lnp64u.Hw.Core
import Machines.Lnp64u.Hw.Demo

open Loom.Release.SSA

def main : IO Unit := do
  let design := Machines.Lnp64u.Hw.core Machines.Lnp64u.Demo.sysManifest
  if design.toProgram == Loom.GeneratedRelease.Lnp64u.program then
    IO.println "LNP64-u toProgram parity: witness = compiler output"
  else
    throw (IO.userError
      "LNP64-u witness differs from Design.toProgram: the shipped program is not the verified compiler's output")
