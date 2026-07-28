-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
-- Release gate: the parsed Acc8 witness equals the verified compiler's own
-- output, `Design.toProgram`. Run via `lake env lean --run` after
-- GeneratedRelease/Acc8/ProgramData is compiled.
import Loom.Release.ToProgram
import GeneratedRelease.Acc8.ProgramData
import Machines.Acc8.Core
import Machines.Acc8.Iss

open Loom.Release.SSA

def main : IO Unit := do
  let design := Machines.Acc8.Core.design
    (Machines.Acc8.loadProg Machines.Acc8.golden)
  if design.toProgram == Loom.GeneratedRelease.Acc8.program then
    IO.println "Acc8 toProgram parity: witness = compiler output"
  else
    throw (IO.userError
      "Acc8 witness differs from Design.toProgram: the shipped program is not the verified compiler's output")
