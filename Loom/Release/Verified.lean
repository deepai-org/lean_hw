-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.NamedCertificate
import Loom.Hw.CompileCorrect

/-!
# Publication-facing verified release claim

This file composes exact rendering, translation validation, compiler
correctness, and processor refinement into one kernel-checkable object.  The
concrete transition system is restricted only in the refinement field; the
restriction has exactly the same powered-on reachable states, so every ISS
invariant transports to the full elaborated module.
-/

namespace Loom.Release

open Loom Loom.Hw Loom.Emit.MicroVerilog

/-- Everything the kernel certifies about one shipped artifact. `spec` is the
fully proved processor model (the ISS transition system for the release).

The external file-binding step has only to compare the concatenation denoted
by `disk.flattenBytes` with the shipped file. -/
structure VerifiedArtifact (spec : TSys) (design : Design)
    (program : SSA.Program) (disk : Rope (List String)) where
  /-- The structural elaboration of the concrete SSA witness. -/
  module : Module
  /-- Exact bytes produced by the verified renderer. -/
  exactBytes : program.renderTree.flattenBytes = disk.flattenBytes
  /-- The witness elaborates structurally, without parsing its rendered text. -/
  elaborates : program.elaborate = some module
  /-- Its transition system is exactly the reference compiler's result. -/
  compilerBehavior : module.toTSys = (Compile.compile design).toTSys
  /-- On the powered-on state space, the exact elaborated artifact refines the
  fully proved processor model. -/
  refinement : Simulation spec module.toTSys.reachablePart
  /-- Every proved model invariant, including invariant-form security
  properties, holds in every reachable state of this exact artifact. -/
  invariants : ∀ {P : spec.S → Prop}, spec.Invariant P →
    module.toTSys.Invariant (fun state => P (refinement.abs state))

/-- Every invariant of the fully proved model holds, through the certified
abstraction function, in every reachable state of the elaborated artifact. -/
theorem VerifiedArtifact.invariant_pullback
    {spec : TSys} {design : Design} {program : SSA.Program}
    {disk : Rope (List String)}
    (artifact : VerifiedArtifact spec design program disk)
    {P : spec.S → Prop} (invariant : spec.Invariant P) :
    artifact.module.toTSys.Invariant
      (fun state => P (artifact.refinement.abs state)) :=
  artifact.invariants invariant

/-- Compose an accepted name certificate with exact rendering, compiler
correctness, and an existing source-level processor refinement. -/
theorem verifiedArtifact_of_named
    (spec : TSys) (design : Design) (program : SSA.Program)
    (disk renderedLines : Rope (List String))
    (cert : Named.ModuleCert design)
    (wf : Compile.DesignWF design)
    (sourceRefinement : Simulation spec design.toTSys.reachablePart)
    (hrender : renderedLines = program.renderTree)
    (hdisk : renderedLines = disk)
    (accepted : ssaNamedMatches design program cert = true) :
    Nonempty (VerifiedArtifact spec design program disk) := by
  obtain ⟨exactBytes, module, elaborates, behavior⟩ :=
    exactRenderingAndNamedCompilation design program disk cert renderedLines
      hrender hdisk accepted
  let compilerRefinement : Simulation design.toTSys module.toTSys := by
    rw [behavior]
    exact Compile.simulation design wf
  let refinement := sourceRefinement.comp compilerRefinement.reachablePart
  exact ⟨
    { module
      exactBytes
      elaborates
      compilerBehavior := behavior
      refinement
      invariants := fun invariant =>
        refinement.invariant_pullback_reachablePart invariant }⟩

end Loom.Release
