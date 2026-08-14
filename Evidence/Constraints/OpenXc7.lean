-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.SystemRealize

/-!
# Optional openXC7 physical-signoff adapter

This module is intentionally outside `Loom.Hw`: openXC7 is one evidence
backend, not part of multiclock semantics or certified emission.

The adapter consumes routed observations already tied to exact input hashes.
It can discharge the structural synchronizer-chain and reset-review portions
of Loom's neutral manifest.  openXC7 0.8.2 does not implement asynchronous
clock groups, generated-object `ASYNC_REG`, period-relative coherent-bus
delay, or bus-skew constraints, so those requirements remain explicitly
`UNCONSTRAINED`. Consequently this adapter correctly refuses to report full
signoff for the stock asynchronous FIFO today.
-/

namespace Loom.Evidence.Constraints.OpenXc7

open Loom.Hw.System

/-- Machine-readable observations produced after synthesis and routing.
`resolutions` contains exact logical-to-routed names recovered from the
post-route database rather than guessed source-name regexes. -/
structure Observation where
  run : PhysicalBackendRun
  artifacts : PhysicalArtifactIdentity
  theoremBoundRtlMatched : Bool
  intentManifestMatched : Bool
  resolutions : List PhysicalObjectResolution
  routedSynchronizerAuditPassed : Bool
  resetContractReviewed : Bool
  deriving Repr

def resolutionsFor (observation : Observation)
    (requirement : PhysicalRequirement) : List PhysicalObjectResolution :=
  requirement.objects.filterMap fun logical =>
    observation.resolutions.find? (fun resolution => resolution.logical == logical)

private def allObjectsResolved (observation : Observation)
    (requirement : PhysicalRequirement) : Bool :=
  let resolutions := resolutionsFor observation requirement
  resolutions.map (fun resolution => resolution.logical) == requirement.objects &&
    resolutions.all (fun resolution => !resolution.resolved.isEmpty)

private def classify (observation : Observation)
    (requirement : PhysicalRequirement) : PhysicalCheckStatus × String :=
  if !observation.theoremBoundRtlMatched then
    (.fail, "input RTL bytes do not match the theorem-bound artifact")
  else if !observation.intentManifestMatched then
    (.fail, "physical-intent bytes do not match the typed Loom manifest")
  else
  match requirement with
  | .timing timing =>
      match timing.intent with
      | .synchronizerChain .. =>
          if observation.routedSynchronizerAuditPassed &&
              allObjectsResolved observation requirement then
            (.pass, "routed stage order, direct fanout, placement, and object resolution checked")
          else
            (.fail, "routed synchronizer structure or exact object resolution failed")
      | .asynchronousClocks .. =>
          (.unconstrained,
            "openXC7 0.8.2 does not consume asynchronous clock-group intent")
      | .coherentBus .. =>
          (.unconstrained,
            "openXC7 0.8.2 cannot discharge period-relative Gray-bus delay/skew intent")
      | .maxDelay .. =>
          (.unconstrained, "openXC7 adapter has no checked max-delay lowering")
      | .falsePath .. =>
          (.unconstrained, "openXC7 adapter has no checked false-path lowering")
  | .reset _ =>
      if observation.resetContractReviewed then
        (.pass, "target wrapper reset delivery reviewed against Loom ResetIntent")
      else
        (.unconstrained, "target reset delivery was not checked against ResetIntent")

/-- Exact-coverage target report. Even a fully successful routed structural
audit does not turn unsupported timing intent into PASS. -/
def check (artifacts : PhysicalArtifacts) (observation : Observation) :
    PhysicalCheckReport artifacts where
  backend := "openXC7 routed physical-intent adapter"
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

/-- Supported target output is intentionally a review directive, not a
fabricated XDC success. Base-clock and package-pin constraints remain owned
by the board wrapper; unsupported Loom requirements are preserved verbatim in
the report returned by `check`. -/
def renderSupportedConstraints (_artifacts : PhysicalArtifacts) : String :=
  String.intercalate "\n" [
    "# openXC7 target adapter",
    "# Board-owned base-clock and package-pin constraints are passed through.",
    "# Loom asynchronous-group, coherent-bus, and ASYNC_REG intent is not",
    "# supported by openXC7 0.8.2 and remains UNCONSTRAINED in signoff."]

end Loom.Evidence.Constraints.OpenXc7
