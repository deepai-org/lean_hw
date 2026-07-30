-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ToProgram
import GeneratedRelease.Acc8.ProgramData
import Machines.Acc8.Core
import Machines.Acc8.Iss

/-!
# `lake exe parityGateAcc8` — the Acc8 "toProgram parity gate", compiled

Release gate: the parsed Acc8 witness (`GeneratedRelease.Acc8.ProgramData`)
equals the verified compiler's own output, `Design.toProgram`.  This is the
compiled replacement for `lake env lean --run scripts/check_toprogram_acc8.lean`
(`Design.toProgram` has a pointer-memoized compiled twin, so the native run is
fast where the interpreter was slow).  The check and its messages are
byte-identical to that script.  One exe per machine: the witness sources are
generated per release target, so a combined exe could never build on a clean
single-target release.
-/

open Loom.Release.SSA

def main : IO Unit := do
  let design := Machines.Acc8.Core.design
    (Machines.Acc8.loadProg Machines.Acc8.golden)
  if design.toProgram == Loom.GeneratedRelease.Acc8.program then
    IO.println "Acc8 toProgram parity: witness = compiler output"
  else
    throw (IO.userError
      "Acc8 witness differs from Design.toProgram: the shipped program is not the verified compiler's output")
