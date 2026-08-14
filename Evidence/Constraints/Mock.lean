-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.SystemRealize

/-!
# Reference physical-intent backend

This deliberately simple backend validates Loom's extension boundary. It
consumes the complete typed requirement list and emits one readable record per
requirement. `PASS` means only that this reference backend recognized and
serialized the requirement; it is not evidence about a placed FPGA or ASIC.

A real XDC, SDC, Quartus, or ASIC adapter has the same fail-closed obligation:
return a result for every requirement, in order, with no silent omissions.
-/

namespace Loom.Evidence.Constraints.Mock

open Loom.Hw.System

def renderObject (object : PhysicalObject) : String := object.render

def renderPeriod (bound : PeriodBound) : String :=
  s!"{bound.numerator}/{bound.denominator}*{bound.reference.describe}"

def renderTiming : TimingConstraint → String
  | .asynchronousClocks left right => s!"async_clocks {left} {right}"
  | .maxDelay fromClock toClock ns => s!"max_delay {fromClock} {toClock} {ns}ns"
  | .falsePath fromClock toClock => s!"false_path {fromClock} {toClock}"
  | .synchronizerChain clock stages =>
      s!"synchronizer {clock} " ++ String.intercalate " -> " (stages.map renderObject)
  | .coherentBus source sink launch capture width skew delay =>
      s!"coherent_bus {source} {sink} width={width} " ++
        s!"{launch.render} -> {capture.render} " ++
        s!"skew<={renderPeriod skew} delay<={renderPeriod delay}"

def renderReset (intent : ResetIntent) : String :=
  let polarity := match intent.polarity with
    | .activeHigh => "active_high"
    | .activeLow => "active_low"
  let assertion := match intent.assertion with
    | .synchronous => "synchronous"
    | .asynchronous => "asynchronous"
  let release := match intent.release with
    | .sampledIndependently => "sampled_independently"
    | .synchronized stages =>
        "synchronized:" ++ String.intercalate "->" (stages.map renderObject)
  s!"reset {intent.clock} source={intent.source} polarity={polarity} " ++
    s!"assertion={assertion} release={release} " ++
    s!"clock_required={intent.requiresClockWhileAsserted}"

def renderRequirement : PhysicalRequirement → String
  | .timing requirement =>
      s!"channel={requirement.key.channel} " ++ renderTiming requirement.intent
  | .reset intent => renderReset intent

def check (artifacts : PhysicalArtifacts) : PhysicalCheckReport artifacts where
  backend := "loom.reference.physical-intent"
  results := artifacts.requirements.map fun requirement =>
    { requirement
      status := .pass
      detail := renderRequirement requirement }
  coverage := by simp [Function.comp_def]

def render (artifacts : PhysicalArtifacts) : String :=
  String.intercalate "\n" <|
    (check artifacts).results.map fun result =>
      result.status.render ++ " " ++ result.detail

end Loom.Evidence.Constraints.Mock
