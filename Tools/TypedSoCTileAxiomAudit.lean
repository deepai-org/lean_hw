-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.TypedSoCTile.Design
import Tools.TypedSoCTileEvidence
import Lean.Util.CollectAxioms

open Machines.Multiclock.TypedSoCTile

#print axioms coreGraph
#print axioms buildTileFragment
#print axioms monitorFragment
#print axioms buildCertifiedArtifact
#print axioms Tools.TypedSoCTileEvidence.tileMemoryWitness
#print axioms Loom.Hw.ExternalIslandSubstitution.checkEmittedReference?

private def auditedDeclarations : List Lean.Name :=
  [``coreGraph,
   ``buildTileFragment,
   ``monitorFragment,
   ``buildCertifiedArtifact,
   ``Tools.TypedSoCTileEvidence.tileMemoryWitness,
   ``Loom.Hw.ExternalIslandSubstitution.checkEmittedReference?]

private def permittedAxioms : List Lean.Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-! Keep the readable reports above, but also make the exact claimed closure an
enforcing gate. Any newly introduced axiom fails this tool during elaboration. -/
run_cmd do
  for declaration in auditedDeclarations do
    let closure ← Lean.collectAxioms declaration
    let unexpected := closure.filter fun dependency =>
      !permittedAxioms.contains dependency
    unless unexpected.isEmpty do
      throwError
        "typed SoC tile axiom audit failed for {declaration}: unexpected {unexpected.toList}"
