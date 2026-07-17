-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.SymbolicSound

/-!
# Publication-facing symbolic release claim

This packages the exact structural renderer, the certificate-free concrete
SSA denotation theorem, and the processor refinement into one kernel object.
The concrete transition system is the proved reference compilation.  The
`ModuleBehavior` field establishes that every state-bearing and observable
piece of the rendered SSA program denotes that compilation.
-/

namespace Loom.Release

open Loom Loom.Hw Loom.Emit.MicroVerilog

/-- Everything certified about one structurally rendered release artifact.

The external binding step only compares `disk.flattenBytes` with the shipped
file. Security properties proved as invariants of `spec` are covered by the
`invariants` field alongside ordinary functional invariants. -/
structure VerifiedSymbolicArtifact (spec : TSys) (design : Design)
    (program : SSA.Program) (disk : Rope (List String))
    (indexeds : Rope (List Symbolic.IndexedWire)) (table : Symbolic.WireTable)
    (registers : Rope (List Symbolic.RegisterRoot))
    (memories : List Symbolic.MemoryRoot) (outputs : Rope (List Nat)) where
  /-- The certified renderer produces exactly the externally bound bytes. -/
  exactBytes : program.renderTree.flattenBytes = disk.flattenBytes
  /-- The arbitrary concrete witness denotes the reference compilation at
  every wire, state element, write port, initialization cell, and output. -/
  denotation : Symbolic.ModuleBehavior design program indexeds table registers
    memories outputs
  /-- The fully proved processor model is simulated by the powered-on exact
  reference compilation denoted by the concrete witness. -/
  refinement : Simulation spec (Compile.compile design).toTSys.reachablePart
  /-- Every model invariant, including invariant-form security theorems,
  transports to every reachable state of the denoted compiled artifact. -/
  invariants : ∀ {P : spec.S → Prop}, spec.Invariant P →
    (Compile.compile design).toTSys.Invariant
      (fun state => P (refinement.abs state))

/-- Package exact rendering, concrete denotation, and a processor refinement.
No property of the untrusted witness or certificate generator is assumed. -/
theorem verifiedSymbolicArtifact_of_checks
    (spec : TSys) (design : Design) (program : SSA.Program)
    (disk : Rope (List String))
    (indexeds : Rope (List Symbolic.IndexedWire)) (table : Symbolic.WireTable)
    (registers : Rope (List Symbolic.RegisterRoot))
    (memories : List Symbolic.MemoryRoot) (outputs : Rope (List Nat))
    (exactBytes : program.renderTree.flattenBytes = disk.flattenBytes)
    (denotation : Symbolic.ModuleBehavior design program indexeds table
      registers memories outputs)
    (refinement : Simulation spec (Compile.compile design).toTSys.reachablePart) :
    Nonempty (VerifiedSymbolicArtifact spec design program disk indexeds table
      registers memories outputs) :=
  ⟨VerifiedSymbolicArtifact.mk exactBytes denotation refinement
    (fun invariant =>
      refinement.invariant_pullback_reachablePart invariant)⟩

theorem VerifiedSymbolicArtifact.invariant_pullback
    {spec : TSys} {design : Design} {program : SSA.Program}
    {disk : Rope (List String)}
    {indexeds : Rope (List Symbolic.IndexedWire)} {table : Symbolic.WireTable}
    {registers : Rope (List Symbolic.RegisterRoot)}
    {memories : List Symbolic.MemoryRoot} {outputs : Rope (List Nat)}
    (artifact : VerifiedSymbolicArtifact spec design program disk indexeds table
      registers memories outputs)
    {P : spec.S → Prop} (invariant : spec.Invariant P) :
    (Compile.compile design).toTSys.Invariant
      (fun state => P (artifact.refinement.abs state)) :=
  artifact.invariants invariant

end Loom.Release
