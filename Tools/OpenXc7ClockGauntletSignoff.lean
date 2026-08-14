-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Evidence.Constraints.OpenXc7
import Machines.Multiclock.ClockGauntlet.Artifact

/-!
# openXC7 Clock-Gauntlet signoff adapter

This optional evidence tool consumes actual generated/routed files, resolves
the stock synchronizer objects from the routed-audit rows, binds the run to
exact RTL/intent hashes, and constructs Loom's fail-closed typed report.
The routed audit must record `INPUT_RTL_SHA256`,
`INPUT_CONSTRAINTS_SHA256`, and `ROUTED_JSON_SHA256`; missing or stale input
identity makes every structural result fail.

The current openXC7 backend cannot discharge every neutral timing
requirement, so a correct invocation writes the report and exits nonzero with
`UNCONSTRAINED` entries. That is intentional: routed/silicon success is not
silently promoted to physical CDC signoff.
-/

namespace Tools.OpenXc7ClockGauntletSignoff

open Loom.Hw
open Loom.Hw.System
open Machines.Multiclock.ClockGauntlet
open Loom.Evidence.Constraints.OpenXc7

private def sha256 (path : System.FilePath) : IO String := do
  let output ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
  if output.exitCode != 0 then
    throw <| IO.userError s!"sha256sum failed for {path}: {output.stderr}"
  match output.stdout.trimAscii.toString.splitOn " " with
  | digest :: _ => pure digest
  | [] => throw <| IO.userError "sha256sum returned no digest"

private def expectedIntent : String :=
  (certifiedArtifact.emissionArtifacts.find?
    (fun artifact => artifact.relativePath.toString = "clock_constraints.md")).map
      (·.text) |>.getD ""

private def auditRows (text : String) : List (List String) :=
  text.splitOn "\n" |>.filterMap fun line =>
    let columns := line.splitOn "\t"
    if columns.length = 7 && line.startsWith "u_gauntlet." then some columns else none

private def auditDigest (text marker : String) : Option String :=
  (text.splitOn "\n").find? (fun line => line.startsWith marker)
    |>.map (fun line => (line.drop marker.length).toString.trimAscii.toString)

private def replaceFinalOneWithZero (signal : String) : String :=
  if signal.endsWith "1" then (signal.dropEnd 1).toString ++ "0" else signal

private def resolveObject (rows : List (List String))
    (logical : PhysicalObject) : Option PhysicalObjectResolution := do
  let instanceName ← logical.path.head?
  let signal ← logical.path.getLast?
  let auditSignal := replaceFinalOneWithZero signal
  let needle := "." ++ instanceName ++ "." ++ auditSignal ++ "["
  let matchingRows := rows.filter fun row => (row.getD 0 "").contains needle
  if matchingRows.isEmpty then none else
  let column := if signal.endsWith "1" then 4 else 2
  let cells := (matchingRows.map fun row => row.getD column "").filter
    (fun cell => !cell.isEmpty)
  if cells.length != matchingRows.length then none else
    some { logical, resolved := String.intercalate "," cells }

private def allResolutions (artifacts : PhysicalArtifacts)
    (rows : List (List String)) : List PhysicalObjectResolution :=
  artifacts.requirements.flatMap fun requirement =>
    requirement.objects.filterMap (resolveObject rows)

private def write (path : System.FilePath) (text : String) : IO Unit := do
  let _ ← Loom.Artifact.writeText path text

def run (evidenceDir : System.FilePath) (runId toolVersion : String)
    (seed : Nat) : IO Unit := do
  let rtlPath := evidenceDir / "system.v"
  let intentPath := evidenceDir / "physical-intent.md"
  let auditPath := evidenceDir / "cdc-routed-audit.txt"
  let rtl ← IO.FS.readFile rtlPath
  let intent ← IO.FS.readFile intentPath
  let audit ← IO.FS.readFile auditPath
  let rows := auditRows audit
  let artifacts := certifiedArtifact.realized.artifacts
  let supportedConstraints := renderSupportedConstraints artifacts ++ "\n"
  let supportedConstraintsPath := evidenceDir / "openxc7-supported-constraints.xdc"
  write supportedConstraintsPath supportedConstraints
  let routedDigest := auditDigest audit "ROUTED_JSON_SHA256: "
  let implementationRtlDigest := auditDigest audit "INPUT_RTL_SHA256: "
  let implementationConstraintDigest :=
    auditDigest audit "INPUT_CONSTRAINTS_SHA256: "
  let runIdentity : PhysicalBackendRun :=
    { scope := .targetImplementation
      adapter := "loom.openxc7.clock-gauntlet"
      target := "xc7z020clg484-1"
      tool := "nextpnr-xilinx"
      version := toolVersion
      runId
      seed := some seed }
  let artifactIdentity : PhysicalArtifactIdentity :=
    { rtlSha256 := ← sha256 rtlPath
      intentSha256 := ← sha256 intentPath
      constraintsSha256 := some (← sha256 supportedConstraintsPath)
      implementationRtlSha256 := implementationRtlDigest
      implementationConstraintsSha256 := implementationConstraintDigest
      routedSha256 := routedDigest }
  let observation : Observation :=
    { run := runIdentity
      artifacts := artifactIdentity
      theoremBoundRtlMatched := rtl == certifiedArtifact.rtlArtifact.text
      intentManifestMatched := intent == expectedIntent
      resolutions := allResolutions artifacts rows
      routedSynchronizerAuditPassed := audit.contains "STATUS: PASS" &&
        artifactIdentity.complete
      resetContractReviewed := false }
  let report := check artifacts observation
  write (evidenceDir / "openxc7-signoff.md") report.render
  if !report.passed then
    throw (IO.userError
      "openXC7 physical signoff is incomplete; see openxc7-signoff.md (expected while required timing intent is unsupported)")

end Tools.OpenXc7ClockGauntletSignoff

def main (args : List String) : IO Unit := do
  match args with
  | [directory, runId, seed, toolVersion] =>
      match seed.toNat? with
      | some value =>
          Tools.OpenXc7ClockGauntletSignoff.run directory runId toolVersion value
      | none => throw (IO.userError "SEED must be a natural number")
  | _ => throw (IO.userError
      "usage: OpenXc7ClockGauntletSignoff EVIDENCE_DIRECTORY RUN_ID SEED TOOL_VERSION")
