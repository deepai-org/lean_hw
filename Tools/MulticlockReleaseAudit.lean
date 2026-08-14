-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Lean

/-! Low-cost exact axiom audit for the independently packaged System release. -/

open Lean

private def expectedAxioms : Array Name :=
  #[`Classical.choice, `Quot.sound, `propext]

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Tools.MulticlockRelease }] {}
  let headline := `Loom.Release.Theorems.verifiedMulticlockRelease
  let (_, closure) :=
    ((Lean.CollectAxioms.collect headline).run env).run
      ({} : Lean.CollectAxioms.State)
  let actual := closure.axioms
  let exact := actual.size == expectedAxioms.size &&
    expectedAxioms.all actual.contains
  if exact then
    IO.println s!"multiclock release audit passed: axioms {actual}"
    return 0
  else
    IO.eprintln s!"multiclock release audit failed: axiom closure {actual}"
    return 1
