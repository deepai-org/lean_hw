-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Lean

/-!
# Final release audit

This executable checks the axiom closure of the publication-facing theorem.
-/

open Lean

private structure AxiomCache where
  done : NameMap (Array Name) := {}
  visiting : NameSet := {}

private def unionAxioms (left right : Array Name) : Array Name :=
  right.foldl (fun result name =>
    if result.contains name then result else result.push name) left

private def collectForMemo (env : Environment) : Nat → Name →
    StateM AxiomCache (Array Name)
  | 0, _ => pure #[]
  | fuel + 1, name => do
      if let some result := (← get).done.find? name then return result
      if (← get).visiting.contains name then return #[]
      modify fun state =>
        { state with visiting := state.visiting.insert name }
      let mut result := #[]
      if let some info := env.constants.find? name then
        for dependency in info.getUsedConstantsAsSet.toArray do
          result := unionAxioms result
            (← collectForMemo env fuel dependency)
        if let .axiomInfo _ := info then
          result := unionAxioms result #[name]
      modify fun state =>
        { done := state.done.insert name result
          visiting := state.visiting.erase name }
      return result

private def expectedAxioms : Array Name :=
  #[`Classical.choice, `Quot.sound, `propext]

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Tools.VerifiedRelease }] {}
  let fuel := env.constants.toList.length + 1
  let (actual, _) := (collectForMemo env fuel
    `Loom.Release.Theorems.verifiedReleases).run {}
  let exact := actual.size == expectedAxioms.size &&
    expectedAxioms.all actual.contains
  if exact then
    IO.println "release audit passed: verifiedReleases uses exactly the three standard axioms"
    return 0
  else
    IO.eprintln s!"release audit failed: unexpected axiom closure {actual}"
    return 1
