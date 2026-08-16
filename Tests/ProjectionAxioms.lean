-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Tests.ProjectionProgress
import Tests.SiblingProjection
import Lean.Util.CollectAxioms

#print axioms Loom.Hw.System.ExecutionProjection.runObservedFrom_project
#print axioms Loom.Hw.System.ExecutionProjection.comp
#print axioms Loom.Hw.System.StandardEmbedding.toExecutionProjection
#print axioms Loom.Hw.System.SystemFragment.standardProjection
#print axioms Loom.Hw.System.ExecutionProjection.projectedTrace_valid
#print axioms Loom.Hw.System.ExecutionProjection.liftFiniteTraceTheorem
#print axioms Loom.Hw.System.SystemFragment.liftFragmentTheorem
#print axioms Loom.Hw.SystemBuilder.FragmentPlacement.toStandardEmbedding
#print axioms Tests.SystemProjection.fragmentOrderingNoLoss
#print axioms Tests.SystemProjection.fragmentBoundedResponse
#print axioms Tests.SystemProjection.asynchronousResponseUnderContract
#print axioms Tests.SystemProjection.monitoredResponseUnderContract
#print axioms Tests.SystemProjection.fragmentPredicateBoundedResponseTheorem
#print axioms Tests.SystemProjection.asynchronousResponseUnderPredicates
#print axioms Tests.SystemProjection.monitoredResponseUnderPredicates
#print axioms Tests.SiblingProjection.serviceTheoremInServiceObserver
#print axioms Tests.SiblingProjection.observerTheoremInServiceObserver
#print axioms Tests.SiblingProjection.serviceTheoremInObserverService
#print axioms Tests.SiblingProjection.observerTheoremInObserverService

private def auditedDeclarations : List Lean.Name :=
  [``Loom.Hw.System.ExecutionProjection.runObservedFrom_project,
   ``Loom.Hw.System.ExecutionProjection.comp,
   ``Loom.Hw.System.StandardEmbedding.toExecutionProjection,
   ``Loom.Hw.System.SystemFragment.standardProjection,
   ``Loom.Hw.System.ExecutionProjection.projectedTrace_valid,
   ``Loom.Hw.System.ExecutionProjection.liftFiniteTraceTheorem,
   ``Loom.Hw.System.SystemFragment.liftFragmentTheorem,
   ``Loom.Hw.SystemBuilder.FragmentPlacement.toStandardEmbedding,
   ``Tests.SystemProjection.fragmentOrderingNoLoss,
   ``Tests.SystemProjection.fragmentBoundedResponse,
   ``Tests.SystemProjection.asynchronousResponseUnderContract,
   ``Tests.SystemProjection.monitoredResponseUnderContract,
   ``Tests.SystemProjection.fragmentPredicateBoundedResponseTheorem,
   ``Tests.SystemProjection.asynchronousResponseUnderPredicates,
   ``Tests.SystemProjection.monitoredResponseUnderPredicates,
   ``Tests.SiblingProjection.serviceTheoremInServiceObserver,
   ``Tests.SiblingProjection.observerTheoremInServiceObserver,
   ``Tests.SiblingProjection.serviceTheoremInObserverService,
   ``Tests.SiblingProjection.observerTheoremInObserverService]

private def permittedAxioms : List Lean.Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-! The reports above are readable evidence. This command is the enforcing,
fail-closed gate: adding any dependency outside the exact whitelist makes the
test fail during elaboration. -/
run_cmd do
  for declaration in auditedDeclarations do
    let closure ← Lean.collectAxioms declaration
    let unexpected := closure.filter fun dependency =>
      !permittedAxioms.contains dependency
    unless unexpected.isEmpty do
      throwError "projection axiom audit failed for {declaration}: unexpected {unexpected.toList}"
