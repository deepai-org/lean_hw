-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Lean

/-!
# Final release audit

This executable checks the axiom closure of the publication-facing byte and
simulator theorems.
-/

open Lean

private def expectedAxioms : Array Name :=
  #[`Classical.choice, `Quot.sound, `propext]

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Tools.VerifiedRelease }] {}
  let headlines := #[
    `Loom.Release.Theorems.verifiedMulticlockRelease,
    `Loom.Release.Theorems.verifiedReleases,
    `Loom.Release.Theorems.formalSubstance,
    `Loom.Hw.DagEval.VerifiedSimulator.compiledCycleOpen_eq,
    `Loom.Hw.DagEval.VerifiedSimulator.compiledRunOpen_eq,
    `Loom.Hw.DagEval.prepareSimulator?_complete,
    `Loom.Hw.CertifiedDesign.renderedUTF8_eq,
    `Loom.Hw.CertifiedDesign.cycleOpen_eq,
    `Loom.Hw.CertifiedDesign.runOpen_eq,
    `Loom.Hw.CertifiedSystem.RegView.read_eq,
    `Loom.Hw.CertifiedSystem.renderedIslandUTF8_eq,
    `Loom.Hw.CertifiedSystem.runPrefix_semantic_eq,
    `Loom.Hw.System.CertifiedRealizedSystem.renderedUTF8_eq,
    `Loom.Hw.System.CertifiedRealizedSystem.rtlArtifact_mem,
    `Loom.Hw.System.CertifiedRealizedSystem.rtlArtifact_exact,
    `Loom.Hw.System.CertifiedRealizedSystem.emittedRTL_exact,
    `Machines.Substrate.TwoClock.certifiedArtifact_bytes,
    `Machines.Lnp64mini.Multiclock.certifiedArtifact_bytes,
    `Loom.Hw.Cdc.AsyncFifo.WithStorage.rep_step,
    `Loom.Hw.Cdc.AsyncQueueStorage.DepthTwo.rep_step,
    `Loom.Hw.Cdc.AsyncQueueStorage.DepthTwo.implementation,
    `Loom.Hw.Cdc.AsyncFifoDesign.source_writeGray_cycle,
    `Loom.Hw.Cdc.AsyncFifoDesign.source_sync_cycle,
    `Loom.Hw.Cdc.AsyncFifoDesign.sink_readGray_cycle,
    `Loom.Hw.Cdc.AsyncFifoDesign.sink_sync_cycle,
    `Loom.Hw.Cdc.AsyncFifoDesign.toGray_pointerWord,
    `Loom.Hw.Cdc.AsyncFifoDesign.fromGray_grayWord,
    `Loom.Hw.Cdc.AsyncFifoDesign.controlRep_reset,
    `Loom.Hw.Cdc.AsyncFifoDesign.controlRep_step,
    `Loom.Hw.Cdc.AsyncFifoDesign.Compiled.rep_step,
    `Loom.Hw.Cdc.AsyncFifoDesign.writeTake_eq_accepted,
    `Loom.Hw.Cdc.AsyncFifoDesign.readTake_eq_delivered]
  let mut failed := false
  for headline in headlines do
    let (_, closure) :=
      ((Lean.CollectAxioms.collect headline).run env).run
        ({} : Lean.CollectAxioms.State)
    let actual := closure.axioms
    let allowed := actual.all expectedAxioms.contains
    let exactRequired :=
      headline == `Loom.Release.Theorems.verifiedMulticlockRelease ||
      headline == `Loom.Release.Theorems.verifiedReleases ||
      headline == `Loom.Release.Theorems.formalSubstance
    let exact := actual.size == expectedAxioms.size &&
      expectedAxioms.all actual.contains
    if allowed && (!exactRequired || exact) then
      IO.println s!"release audit passed: {headline} axioms {actual}"
    else
      failed := true
      IO.eprintln s!"release audit failed: {headline} has unexpected axiom closure {actual}"
  return if failed then 1 else 0
