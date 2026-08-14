-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.ClockGauntlet.Execution

/-! Executable, replayable schedule campaigns for Clock Gauntlet. -/

namespace Tools.ClockGauntletCampaign

open Loom.Hw
open Machines.Multiclock.ClockGauntlet
open Machines.Multiclock.ClockGauntlet.Execution

private def firstUnsafeFrom : Nat → FastState → List NamedClockEvent →
    Option (List NamedClockEvent × Metrics)
  | 0, _, _ => none
  | depth + 1, state, reversePrefix =>
      (List.range 8).findSome? fun mask =>
        let nextEvent := event mask
        let next := advance nextEvent state
        let observed := metrics next
        if safe observed then
          firstUnsafeFrom depth next (nextEvent :: reversePrefix)
        else some ((nextEvent :: reversePrefix).reverse, observed)

private def firstUnsafe (depth : Nat) : Option (List NamedClockEvent × Metrics) :=
  firstUnsafeFrom depth reset []

private def lcg (state : Nat) : Nat :=
  (1664525 * state + 1013904223) % 4294967296

private def seededEventsFrom (state : Nat) : Nat → List NamedClockEvent
  | 0 => []
  | count + 1 =>
      let next := lcg state
      event (next % 8) :: seededEventsFrom next count

private def seededEvents (seed count : Nat) : List NamedClockEvent :=
  seededEventsFrom seed count

private structure Campaign where
  name : String
  seed : Nat
  schedule : List NamedClockEvent
  requireSourceBackpressure : Bool := false
  requireTransformBackpressure : Bool := false

private def campaigns : List Campaign := [
  { name := "source_much_faster", seed := 0,
    schedule := repeatPattern 2048 [1, 1, 1, 1, 2, 4] ++ drain,
    requireSourceBackpressure := true },
  { name := "consumer_much_faster", seed := 0,
    schedule := repeatPattern 2048 [1, 2, 4, 4, 4, 4] ++ drain },
  { name := "starve_source", seed := 0,
    schedule := repeatPattern 256 [6] ++ repeatPattern 2048 [1, 2, 4] ++ drain },
  { name := "starve_transform", seed := 0,
    schedule := repeatPattern 256 [1, 4] ++ repeatPattern 2048 [1, 2, 4] ++ drain,
    requireSourceBackpressure := true },
  { name := "starve_checker", seed := 0,
    schedule := repeatPattern 256 [1, 2] ++ repeatPattern 2048 [1, 2, 4] ++ drain,
    requireSourceBackpressure := true,
    requireTransformBackpressure := true },
  { name := "pause_source_at_empty_restart", seed := 0,
    schedule := repeatPattern 256 [6] ++ repeatPattern 3072 [1, 2, 4] ++ drain },
  { name := "pause_transform_at_full_restart", seed := 0,
    schedule := repeatPattern 128 [1] ++ repeatPattern 3072 [1, 2, 4] ++ drain,
    requireSourceBackpressure := true },
  { name := "pause_checker_at_full_restart", seed := 0,
    schedule := repeatPattern 128 [1, 2] ++ repeatPattern 3072 [1, 2, 4] ++ drain,
    requireSourceBackpressure := true,
    requireTransformBackpressure := true },
  { name := "pause_checker_partial_restart", seed := 0,
    schedule := [event 1, event 1, event 2, event 2, event 2] ++
      repeatPattern 128 [1, 2] ++ repeatPattern 3072 [1, 2, 4] ++ drain,
    requireSourceBackpressure := true,
    requireTransformBackpressure := true },
  { name := "reset_release_skew_source_first", seed := 0,
    schedule := repeatPattern 128 [1] ++ repeatPattern 64 [3] ++
      repeatPattern 3072 [1, 2, 4] ++ drain,
    requireSourceBackpressure := true },
  { name := "reset_release_skew_checker_first", seed := 0,
    schedule := repeatPattern 128 [4] ++ repeatPattern 64 [6] ++
      repeatPattern 3072 [1, 2, 4] ++ drain },
  { name := "bursty_alternating_coincident", seed := 0,
    schedule := repeatPattern 4096 [0, 1, 3, 2, 6, 4, 7, 5] ++ drain },
  { name := "seeded_12648430", seed := 12648430,
    schedule := seededEvents 12648430 4096 ++ drain },
  { name := "seeded_3735928559", seed := 3735928559,
    schedule := seededEvents 3735928559 4096 ++ drain }]

private def runCampaign (campaign : Campaign) : IO Bool := do
  let observed := metrics (run campaign.schedule)
  let passed := complete observed &&
    (!campaign.requireSourceBackpressure || observed.sourceBackpressure > 0) &&
    (!campaign.requireTransformBackpressure || observed.transformBackpressure > 0)
  IO.println s!"campaign={campaign.name} seed={campaign.seed} events={campaign.schedule.length} passed={passed} metrics={repr observed}"
  pure passed

private def metricsJson (observed : Metrics) : String :=
  "{" ++ s!"\"offered\":{observed.offered},\"accepted\":{observed.accepted}," ++
  s!"\"transformed\":{observed.transformed},\"forwarded\":{observed.forwarded}," ++
  s!"\"delivered\":{observed.delivered},\"digest\":{observed.digest}," ++
  s!"\"sticky_error\":{observed.stickyError}," ++
  s!"\"source_backpressure\":{observed.sourceBackpressure}," ++
  s!"\"transform_backpressure\":{observed.transformBackpressure}," ++
  s!"\"source_write_wraps\":{observed.sourceWriteWraps}," ++
  s!"\"transform_read_wraps\":{observed.transformReadWraps}," ++
  s!"\"transform_write_wraps\":{observed.transformWriteWraps}," ++
  s!"\"checker_read_wraps\":{observed.checkerReadWraps}," ++
  s!"\"source_progress\":{observed.sourceProgress}," ++
  s!"\"transform_progress\":{observed.transformProgress}," ++
  s!"\"checker_progress\":{observed.checkerProgress}" ++ "}"

private def campaignJson (campaign : Campaign) : Bool × String :=
  let observed := metrics (run campaign.schedule)
  let passed := complete observed &&
    (!campaign.requireSourceBackpressure || observed.sourceBackpressure > 0) &&
    (!campaign.requireTransformBackpressure || observed.transformBackpressure > 0)
  (passed, "{" ++ s!"\"name\":\"{campaign.name}\",\"seed\":{campaign.seed}," ++
    s!"\"events\":{campaign.schedule.length},\"passed\":{passed}," ++
    s!"\"metrics\":{metricsJson observed}" ++ "}")

/-- Machine-readable result for the fail-closed evidence producer.  Every
campaign is run here regardless of the interactive replay selector. -/
def evidenceResultJson : Bool × String :=
  let exhaustivePassed := (firstUnsafe 4).isNone
  let results := campaigns.map campaignJson
  let passed := exhaustivePassed && results.all (·.1)
  let body := String.intercalate ",\n    " (results.map (·.2))
  (passed, "{\n  \"schema\":1,\n  \"certified_semantics\":\"System.runEventsFrom\"," ++
    "\n  \"semantic_bridge\":true,\n  \"exhaustive_depth\":4," ++
    s!"\n  \"exhaustive_schedules\":4096,\n  \"exhaustive_passed\":{exhaustivePassed}," ++
    "\n  \"campaigns\":[\n    " ++ body ++
    s!"\n  ],\n  \"passed\":{passed}\n" ++ "}\n")

def runMain : IO UInt32 := do
  IO.println "clock-gauntlet campaign runner initialized"
  match firstUnsafe 4 with
  | some (schedule, observed) =>
      IO.eprintln s!"exhaustive depth=4 failed schedule={repr schedule} metrics={repr observed}"
      return 1
  | none => IO.println "exhaustive depth=4 schedules=4096 passed=true"
  let selected ← match ← IO.getEnv "CLOCK_GAUNTLET_ONLY" with
    | none => pure campaigns
    | some name =>
        let chosen := campaigns.filter (fun campaign => campaign.name = name)
        if chosen.isEmpty then
          throw <| IO.userError s!"unknown CLOCK_GAUNTLET_ONLY campaign: {name}"
        pure chosen
  let results ← selected.mapM runCampaign
  if results.all id then
    IO.println "CLOCK_GAUNTLET_CERTIFIED_CAMPAIGNS_OK"
    return 0
  else
    IO.eprintln "CLOCK_GAUNTLET_CERTIFIED_CAMPAIGNS_FAILED"
    return 1

end Tools.ClockGauntletCampaign
