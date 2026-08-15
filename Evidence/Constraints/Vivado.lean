-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.SystemRealize

/-!
# Vivado routed-signoff observation adapter

The Tcl implementation flow is external; this evidence-layer value is the
typed ingestion boundary for its machine-readable results.  A requirement is
credited only when the exact neutral item appears in `covered`, every generated
object resolves, the relevant routed check passes, and the routed database is
bound to exact RTL/constraint inputs.
-/

namespace Loom.Evidence.Constraints.Vivado

open Loom.Hw.System

structure Observation where
  run : PhysicalBackendRun
  artifacts : PhysicalArtifactIdentity
  /-- Exact neutral requirements for which the generated constraint/review
  directive was found in the implementation run. -/
  covered : List PhysicalRequirement
  resolutions : List PhysicalObjectResolution
  /-- The named clocks were resolved to distinct physical roots and the
  implementation flow treated their crossings as asynchronous. This does not
  require `set_clock_groups`: Vivado gives that exception priority over the
  Gray-bus `set_max_delay -datapath_only` requirements. -/
  asynchronousRelationshipPassed : Bool
  synchronizerAttributesPassed : Bool
  synchronizerStructurePassed : Bool
  noForbiddenSynchronizerFanout : Bool
  grayBusSkewPassed : Bool
  grayBusDatapathPassed : Bool
  ordinaryTimingPassed : Bool
  resetDeliveryPassed : Bool
  deriving Repr

def resolutionsFor (observation : Observation)
    (requirement : PhysicalRequirement) : List PhysicalObjectResolution :=
  requirement.objects.filterMap fun logical =>
    observation.resolutions.find? (fun resolution => resolution.logical == logical)

private def objectsResolved (observation : Observation)
    (requirement : PhysicalRequirement) : Bool :=
  let resolutions := resolutionsFor observation requirement
  resolutions.map (fun resolution => resolution.logical) == requirement.objects &&
    resolutions.all (fun resolution => !resolution.resolved.isEmpty)

private def classify (observation : Observation)
    (requirement : PhysicalRequirement) : PhysicalCheckStatus × String :=
  if !observation.run.complete then
    (.fail, "target run identity is incomplete")
  else if !observation.artifacts.complete then
    (.fail, "routed database is not bound to exact RTL and constraint inputs")
  else if !observation.covered.contains requirement then
    (.fail, "neutral requirement is absent from the applied target constraints/review")
  else if !objectsResolved observation requirement then
    (.fail, "one or more generated physical objects did not resolve exactly")
  else
    match requirement with
    | .timing timing =>
        match timing.intent with
        | .asynchronousClocks .. =>
            if observation.asynchronousRelationshipPassed then
              (.pass, "distinct physical roots and asynchronous relationship reported")
            else (.fail, "asynchronous clock relationship was not honored")
        | .synchronizerChain .. =>
            if observation.synchronizerAttributesPassed &&
                observation.synchronizerStructurePassed &&
                observation.noForbiddenSynchronizerFanout then
              (.pass, "synchronizer attributes, ordered stages, and fanout passed")
            else (.fail, "synchronizer attribute, structure, or fanout audit failed")
        | .coherentBus .. =>
            if observation.grayBusSkewPassed && observation.grayBusDatapathPassed then
              (.pass, "Gray-bus skew and datapath bounds passed")
            else (.fail, "Gray-bus skew or datapath bound failed")
        | .maxDelay .. | .falsePath .. =>
            if observation.ordinaryTimingPassed then
              (.pass, "timing exception applied and checked")
            else (.fail, "timing exception was not checked")
    | .reset _ =>
        if observation.resetDeliveryPassed then
          (.pass, "target reset delivery passed review")
        else (.fail, "target reset delivery did not pass review")

def check (artifacts : PhysicalArtifacts) (observation : Observation) :
    PhysicalCheckReport artifacts where
  backend := "Vivado routed physical-intent adapter"
  run := observation.run
  artifactIdentity := observation.artifacts
  results := artifacts.requirements.map fun requirement =>
    let verdict := classify observation requirement
    { requirement
      status := verdict.1
      detail := verdict.2
      run := observation.run
      artifacts := observation.artifacts
      resolutions := resolutionsFor observation requirement }
  coverage := by simp [Function.comp_def]

end Loom.Evidence.Constraints.Vivado
