-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Diff
import Machines.Acc8.Core

/-! Generic runner/result and fail-closed coverage regressions. -/

namespace Tests.Runner

open Loom.Hw

private def emptyProgram : BitVec 8 → BitVec 16 := fun _ => 0

#eval do
  let d := Machines.Acc8.Core.design emptyProgram
  let sample := d.sampleAgainstOracle 1 d.reset { read := fun _ => none }
  unless sample.coverageGaps.contains "acc" do
    throw <| IO.userError s!"missing register was not named: {sample.coverageGaps}"
  unless sample.coverageGaps.contains "prog[0]" do
    throw <| IO.userError s!"missing memory cell was not named: {sample.coverageGaps}"

  let result := Loom.Runner.evaluate
    { label := "runner-negative", steps := 4, maxEvents := 2,
      stopOnFailure := true }
    () fun _ state => (state, { coverageGaps := ["new_coordinate"] })
  unless result.verdict == Loom.Runner.Verdict.fail && result.stepsCompleted == 1 &&
      result.coverageGaps == ["new_coordinate"] && result.events.length == 1 do
    throw <| IO.userError s!"fail-closed runner result wrong: {repr result}"

  let skipped := Loom.Runner.Result.skipped "optional-tool" "tool unavailable"
  unless skipped.render == "optional-tool: RESULT SKIP reason=tool unavailable" do
    throw <| IO.userError s!"structured skip result wrong: {skipped.render}"

  IO.println "generic runner negative coverage/result tests passed"

end Tests.Runner
