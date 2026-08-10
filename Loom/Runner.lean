-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0

/-!
# Generic differential-run control and diagnostics

Machines own their state and the meaning of one step.  This module owns the
otherwise-repeated control plane: bounded iteration, mismatch/coverage events,
immediate output flushing, event limits, and structured final results.

No input-port, CPU, memory-system, or reference-model shape appears here.  A
client supplies one opaque state and one callback returning the next state and
the observations made on that step.
-/

namespace Loom.Runner

/-- A stable, machine-readable outcome vocabulary for gates and wrappers. -/
inductive Verdict where
  | pass
  | fail
  | skip
  deriving Repr, BEq

def Verdict.render : Verdict → String
  | .pass => "PASS"
  | .fail => "FAIL"
  | .skip => "SKIP"

/-- One named disagreement.  Values are strings so the runner remains usable
for state that is not numeric. -/
structure Event where
  kind     : String := "mismatch"
  subject  : String
  actual   : Option String := none
  expected : Option String := none
  detail   : String := ""
  deriving Repr, BEq

def Event.render (step : Nat) (e : Event) : String :=
  let values := match e.actual, e.expected with
    | some actual, some expected => s!" actual={actual} expected={expected}"
    | some actual, none => s!" actual={actual}"
    | none, some expected => s!" expected={expected}"
    | none, none => ""
  let detail := if e.detail.isEmpty then "" else s!" — {e.detail}"
  s!"{e.kind} step {step} {e.subject}{values}{detail}"

/-- Observations from one client-defined step.  `coverageGaps` are failures,
not warnings. `excluded` records the closed, named part of the state which the
oracle deliberately does not model. -/
structure Sample where
  mismatches   : List Event := []
  coverageGaps : List String := []
  excluded     : List String := []
  deriving Repr

/-- Options shared by all differential runs. -/
structure Config where
  label         : String
  steps         : Nat
  maxEvents     : Nat := 8
  stopOnFailure : Bool := false
  deriving Repr

/-- Complete result of a run.  Counts are never truncated; only the retained
diagnostic event list is bounded by `Config.maxEvents`. -/
structure Result where
  label          : String
  verdict        : Verdict
  stepsCompleted : Nat
  mismatchCount  : Nat := 0
  coverageGaps   : List String := []
  excluded       : List String := []
  events         : List (Nat × Event) := []
  reason         : String := ""
  deriving Repr

def Result.failureCount (r : Result) : Nat :=
  r.mismatchCount + r.coverageGaps.length

def Result.render (r : Result) : String :=
  let counts := match r.verdict with
    | .skip => ""
    | _ => s!" steps={r.stepsCompleted} mismatches={r.mismatchCount} coverage_gaps={r.coverageGaps.length} excluded={r.excluded.length}"
  let reason := if r.reason.isEmpty then "" else s!" reason={r.reason}"
  s!"{r.label}: RESULT {r.verdict.render}{counts}{reason}"

/-- Print and flush the final structured result. -/
def Result.report (r : Result) : IO Unit := do
  IO.println r.render
  (← IO.getStdout).flush

/-- Report a result and make failure non-zero at an executable/test boundary. -/
def Result.requirePass (r : Result) : IO Unit := do
  r.report
  if r.verdict != .pass then
    throw <| IO.userError r.render

def Result.skipped (label reason : String) : Result :=
  { label, verdict := .skip, stepsCompleted := 0, reason }

def Result.fromFailureCount (label : String) (steps failures : Nat)
    (reason : String := "") : Result :=
  { label
    verdict := if failures = 0 then .pass else .fail
    stepsCompleted := steps
    mismatchCount := failures
    reason := if failures = 0 then "" else reason }

def Result.fromBool (label : String) (steps : Nat) (ok : Bool)
    (reason : String := "") : Result :=
  Result.fromFailureCount label steps (if ok then 0 else 1) reason

private def addUnique (xs ys : List String) : List String :=
  ys.foldl (fun acc y => if acc.contains y then acc else acc ++ [y]) xs

private def finish (cfg : Config) (steps bad : Nat) (gaps excluded : List String)
    (events : List (Nat × Event)) : Result :=
  { label := cfg.label
    verdict := if bad = 0 && gaps.isEmpty then .pass else .fail
    stepsCompleted := steps
    mismatchCount := bad
    coverageGaps := gaps
    excluded := excluded
    events := events }

/-- Pure control kernel, useful when the result itself participates in a
build-time proposition.  `run` below has the same state transition and result
contract and adds immediate diagnostics. -/
def evaluate {State : Type} (cfg : Config) (initial : State)
    (step : Nat → State → State × Sample) : Result := Id.run do
  let mut state := initial
  let mut completed := 0
  let mut bad := 0
  let mut gaps : List String := []
  let mut excluded : List String := []
  let mut events : List (Nat × Event) := []
  for k in List.range cfg.steps do
    let (next, sample) := step k state
    state := next
    completed := completed + 1
    bad := bad + sample.mismatches.length
    gaps := addUnique gaps sample.coverageGaps
    excluded := addUnique excluded sample.excluded
    for event in sample.mismatches do
      if events.length < cfg.maxEvents then events := events ++ [(k, event)]
    for gap in sample.coverageGaps do
      if events.length < cfg.maxEvents then
        events := events ++ [(k, { kind := "coverage-gap", subject := gap })]
    if cfg.stopOnFailure && (!sample.mismatches.isEmpty || !sample.coverageGaps.isEmpty) then
      break
  return finish cfg completed bad gaps excluded events

/-- The executable runner. Diagnostics are printed at the step where they are
observed and stdout is flushed after every line, so a slow failing run cannot
look like a hang. -/
def run {State : Type} (cfg : Config) (initial : State)
    (step : Nat → State → IO (State × Sample)) : IO Result := do
  let mut state := initial
  let mut completed := 0
  let mut bad := 0
  let mut gaps : List String := []
  let mut excluded : List String := []
  let mut events : List (Nat × Event) := []
  for k in List.range cfg.steps do
    let (next, sample) ← step k state
    state := next
    completed := completed + 1
    bad := bad + sample.mismatches.length
    gaps := addUnique gaps sample.coverageGaps
    excluded := addUnique excluded sample.excluded
    for event in sample.mismatches do
      if events.length < cfg.maxEvents then
        IO.println s!"  {event.render k}"
        (← IO.getStdout).flush
        events := events ++ [(k, event)]
    for gap in sample.coverageGaps do
      if events.length < cfg.maxEvents then
        let event : Event := { kind := "coverage-gap", subject := gap }
        IO.println s!"  {event.render k}"
        (← IO.getStdout).flush
        events := events ++ [(k, event)]
    if cfg.stopOnFailure && (!sample.mismatches.isEmpty || !sample.coverageGaps.isEmpty) then
      break
  return finish cfg completed bad gaps excluded events

end Loom.Runner
