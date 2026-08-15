-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Pipeline

/-! # Elastic pipeline regressions -/

namespace Tests.Pipeline

open Loom.Hw
open Loom.Hw.Pipeline

private inductive CoreClock
private instance : ClockDomain CoreClock where name := "core"

private def initial : State 3 Nat := State.empty 3
private def first := initial.step (some 10) true
private def second := first.state.step (some 20) true
private def third := second.state.step none true
private def fourth := third.state.step none true

#guard first.inputReady && first.output.isNone
#guard second.inputReady && second.output.isNone
#guard third.inputReady && third.output.isNone
#guard fourth.output == some 10

example : occupancy (advance [some 1, some 2, none] (some 3) true).1 +
    outputAccepted [some 1, some 2, none] (some 3) true =
      occupancy [some 1, some 2, none] +
        accepted (some 3) (advance [some 1, some 2, none] (some 3) true).2 :=
  advance_conservation _ _ _

private def graph : Except String ComponentGraph :=
  componentGraph? (δ := CoreClock) (α := BitVec 16) "pipe" "Word" 3

#guard match graph with
  | .error _ => false
  | .ok graph =>
      graph.instances.length == 3 && graph.connections.length == 6 &&
      graph.exports.length == 3 && graph.validB

#guard match graph with
  | .error _ => false
  | .ok graph =>
      match graph.seal? with
      | .error _ => false
      | .ok _ => true

end Tests.Pipeline
