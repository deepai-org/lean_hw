-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Evidence.Constraints.Vivado
import Machines.Multiclock.SurfaceMatrix.RegisteredBram
import Machines.Multiclock.SurfaceMatrix.Recovery

/-!
# Typed Vivado signoff ingestion for the multiclock surface matrix

The Vivado Tcl flow emits exact logical-object resolutions, routed audit rows,
run identity, and route-input hashes. This tool binds those files back to the
same certified artifact and constructs Loom's fail-closed physical report.
-/

namespace Tools.SurfaceMatrixVivadoSignoff

open Loom.Hw
open Loom.Hw.System
open Loom.Evidence.Constraints.Vivado

private def sha256 (path : System.FilePath) : IO String := do
  let output ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
  if output.exitCode != 0 then
    throw <| IO.userError s!"sha256sum failed for {path}: {output.stderr}"
  match output.stdout.trimAscii.toString.splitOn " " with
  | digest :: _ => pure digest
  | [] => throw <| IO.userError "sha256sum returned no digest"

private def rows (text : String) : List (List String) :=
  text.splitOn "\n" |>.filterMap fun line =>
    let columns := line.splitOn "\t"
    if columns.length ≥ 2 then some columns else none

private def value? (table : List (List String)) (key : String) : Option String :=
  (table.find? fun row => row.getD 0 "" == key).map fun row => row.getD 1 ""

private def auditPassed (table : List (List String)) (key : String) : Bool :=
  (table.find? fun row => row.getD 0 "" == key).any fun row =>
    row.getD 1 "" == "PASS"

private def resolution? (table : List (List String))
    (logical : PhysicalObject) : Option PhysicalObjectResolution := do
  let row ← table.find? fun row => row.getD 0 "" == logical.render
  let resolved := row.getD 1 ""
  if resolved.isEmpty then none else some { logical, resolved }

private def allResolutions (artifacts : PhysicalArtifacts)
    (table : List (List String)) : List PhysicalObjectResolution :=
  artifacts.requirements.flatMap fun requirement =>
    requirement.objects.filterMap (resolution? table)

private def expectedIntent {system : System} {certified : CertifiedSystem system}
    (artifact : System.CertifiedRealizedSystem system certified) : String :=
  (artifact.emissionArtifacts.find?
    (fun artifact => artifact.relativePath.toString = "clock_constraints.md")).map
      (·.text) |>.getD ""

private def write (path : System.FilePath) (contents : String) : IO Unit := do
  discard <| Loom.Artifact.writeText path contents

private def runFor {system : System} {certified : CertifiedSystem system}
    (artifact : System.CertifiedRealizedSystem system certified)
    (variant bitstreamName : String) (evidenceDir routeDir : System.FilePath)
    (runId : String) (seed : Nat) : IO Unit := do
  let rtlPath := evidenceDir / "system.v"
  let intentPath := evidenceDir / "clock_constraints.md"
  let inputManifestPath := routeDir / "route-inputs.sha256"
  let routedPath := routeDir / "routed.dcp"
  let bitstreamPath := routeDir / bitstreamName
  let resolutionTable := rows (← IO.FS.readFile (routeDir / "object-resolutions.tsv"))
  let auditTable := rows (← IO.FS.readFile (routeDir / "physical-audit.tsv"))
  let statusTable := rows (← IO.FS.readFile (routeDir / "route-status.tsv"))
  let rtl ← IO.FS.readFile rtlPath
  let intent ← IO.FS.readFile intentPath
  let rtlDigest ← sha256 rtlPath
  let inputDigest ← sha256 inputManifestPath
  let statusRtl := value? statusTable "rtl_sha256"
  let statusInputs := value? statusTable "route_inputs_sha256"
  let statusSeed := value? statusTable "seed"
  let statusVersion := value? statusTable "vivado_version"
  let statusDirective := value? statusTable "place_directive"
  let artifacts := artifact.realized.artifacts
  let allAuditPassed :=
    ["asynchronous_relationship", "report_cdc_critical",
      "report_cdc_warnings_reviewed", "synchronizer_attributes",
      "synchronizer_structure_fanout", "synchronizer_placement",
      "gray_datapath", "gray_bus_skew",
      "ordinary_timing", "reset_delivery"].all (auditPassed auditTable)
  let exactInputs := rtl == artifact.rtlArtifact.text &&
    intent == expectedIntent artifact && statusRtl == some rtlDigest &&
    statusInputs == some inputDigest && statusSeed == some (toString seed) &&
    statusDirective.any (fun directive => !directive.isEmpty) &&
    value? statusTable "variant" == some variant &&
    value? statusTable "status" == some "PASS"
  let runIdentity : PhysicalBackendRun :=
    { scope := .targetImplementation
      adapter := "loom.vivado.surface-matrix." ++ variant
      target := "xc7z020clg484-1"
      tool := "Vivado"
      version := statusVersion.getD ""
      runId
      implementationVariant := "place_design -directive " ++ statusDirective.getD ""
      seed := some seed }
  let identity : PhysicalArtifactIdentity :=
    { rtlSha256 := rtlDigest
      intentSha256 := ← sha256 intentPath
      constraintsSha256 := some inputDigest
      synthesizedSha256 := some (← sha256 (routeDir / "post_synth.dcp"))
      implementationRtlSha256 := statusRtl
      implementationConstraintsSha256 := statusInputs
      routedSha256 := some (← sha256 routedPath)
      bitstreamSha256 := some (← sha256 bitstreamPath) }
  let observation : Observation :=
    { run := runIdentity
      artifacts := identity
      covered := if exactInputs && allAuditPassed then artifacts.requirements else []
      resolutions := allResolutions artifacts resolutionTable
      asynchronousRelationshipPassed := auditPassed auditTable "asynchronous_relationship"
      synchronizerAttributesPassed := auditPassed auditTable "synchronizer_attributes"
      synchronizerStructurePassed := auditPassed auditTable "synchronizer_structure_fanout"
      noForbiddenSynchronizerFanout := auditPassed auditTable "synchronizer_structure_fanout"
      grayBusSkewPassed := auditPassed auditTable "gray_bus_skew"
      grayBusDatapathPassed := auditPassed auditTable "gray_datapath"
      ordinaryTimingPassed := auditPassed auditTable "ordinary_timing"
      resetDeliveryPassed := auditPassed auditTable "reset_delivery" }
  let report := check artifacts observation
  write (routeDir / "vivado-signoff.md") report.render
  if !report.passed then
    throw <| IO.userError
      "Vivado surface-matrix signoff failed; see vivado-signoff.md"
  IO.println s!"SURFACE_MATRIX_VIVADO_SIGNOFF_PASS variant={variant} run={runId} seed={seed}"

def run (variant : String) (evidenceDir routeDir : System.FilePath)
    (runId : String) (seed : Nat) : IO Unit :=
  match variant with
  | "matrix" => runFor Machines.Multiclock.SurfaceMatrix.certifiedArtifact
      "matrix" "surface_matrix.bit" evidenceDir routeDir runId seed
  | "registered-bram" =>
      runFor Machines.Multiclock.SurfaceMatrix.RegisteredBram.certifiedArtifact
        "registered-bram" "surface_registered_bram.bit"
        evidenceDir routeDir runId seed
  | "recovery" =>
      runFor Machines.Multiclock.SurfaceMatrix.Recovery.certifiedArtifact
        "recovery" "surface_recovery.bit" evidenceDir routeDir runId seed
  | _ => throw <| IO.userError s!"unknown surface signoff variant: {variant}"

end Tools.SurfaceMatrixVivadoSignoff

def main (args : List String) : IO Unit := do
  match args with
  | [evidenceDir, routeDir, runId, seed] =>
      match seed.toNat? with
      | some value => Tools.SurfaceMatrixVivadoSignoff.run "matrix" evidenceDir routeDir runId value
      | none => throw <| IO.userError "SEED must be a natural number"
  | [variant, evidenceDir, routeDir, runId, seed] =>
      match seed.toNat? with
      | some value => Tools.SurfaceMatrixVivadoSignoff.run variant evidenceDir routeDir runId value
      | none => throw <| IO.userError "SEED must be a natural number"
  | _ => throw <| IO.userError "usage: surfaceMatrixVivadoSignoff [VARIANT] EVIDENCE_DIRECTORY ROUTE_DIRECTORY RUN_ID SEED"
