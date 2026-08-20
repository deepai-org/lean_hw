-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Signoff

/-! # Fail-closed signoff evidence regressions -/

namespace Tests.Signoff

open Loom.Hw.Signoff

private def digest := String.ofList (List.replicate 64 'b')

private def original : Artifact := ⟨"original", "rtl/original.v", digest⟩
private def emitted : Artifact := ⟨"emitted", "rtl/emitted.v", digest⟩
private def log : Artifact := ⟨"log", "evidence/equivalence.log", digest⟩

private def assumption : Assumption :=
  ⟨"reset", "reset is asserted before observations are compared"⟩

private def requirement : Requirement where
  id := "fixture.original_to_loom_rtl"
  stage := .originalToLoomRtl
  description := "fixture equivalence"
  inputs := ["original", "emitted"]
  outputs := ["log"]

private def plan : Plan where
  name := "fixture.rtl_equivalence"
  artifacts := [original, emitted, log]
  requirements := [requirement]
  assumptions := [assumption]

private def generatedPlan : Plan :=
  rtlEquivalencePlan "fixture" original emitted log [assumption]

#guard plan.validB
#guard generatedPlan.validB

private def run : ToolRun where
  adapter := "fixture-adapter"
  tool := "fixture-tool"
  version := "1"
  runId := "run-1"
  invocation := ["fixture-tool", "equivalence.ys"]

private def passedResult : Result where
  requirement := requirement
  status := .pass
  detail := "all equivalence points proved"
  run := run
  artifacts := plan.artifacts
  assumptions := plan.assumptions

private def passedReport : Report plan where
  results := [passedResult]
  coverage := rfl

#guard passedReport.complete
#guard passedReport.passed

private def skippedResult : Result := { passedResult with status := .skip }

private def skippedReport : Report plan where
  results := [skippedResult]
  coverage := rfl

#guard !skippedReport.complete

private def staleResult : Result :=
  { passedResult with artifacts := [{ original with sha256 := String.ofList (List.replicate 64 'a') }] ++
      plan.artifacts.tail }

private def staleReport : Report plan where
  results := [staleResult]
  coverage := rfl

#guard !staleReport.complete

end Tests.Signoff
