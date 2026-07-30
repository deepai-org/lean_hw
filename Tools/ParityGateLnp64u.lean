-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ToProgram
import GeneratedRelease.Lnp64u.ProgramData
import Machines.Lnp64u.Hw.Core
import Machines.Lnp64u.Hw.Demo

/-!
# `lake exe parityGateLnp64u` — the LNP64-u "toProgram parity gate", compiled

Release gate: the parsed LNP64-u witness (`GeneratedRelease.Lnp64u.ProgramData`)
equals the verified compiler's own output, `Design.toProgram`.  This is the
compiled replacement for `lake env lean --run
scripts/check_toprogram_lnp64u.lean` (the interpreter made this comparison take
minutes; `Design.toProgram` has a pointer-memoized compiled twin, so the native
run is fast).  The check and its messages are byte-identical to that script.
One exe per machine: the witness sources are generated per release target, so a
combined exe could never build on a clean single-target release.
-/

open Loom.Release.SSA

def main : IO Unit := do
  let design := Machines.Lnp64u.Hw.core Machines.Lnp64u.Demo.sysManifest
  if design.toProgram == Loom.GeneratedRelease.Lnp64u.program then
    IO.println "LNP64-u toProgram parity: witness = compiler output"
  else
    throw (IO.userError
      "LNP64-u witness differs from Design.toProgram: the shipped program is not the verified compiler's output")
