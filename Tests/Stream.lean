-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Stream

/-! # Same-clock ready/valid stream regressions -/

namespace Tests.Stream

open Loom.Hw

private inductive CoreClock
private instance : ClockDomain CoreClock where name := "core"

private def slice : Except String Component.Sealed :=
  Loom.Hw.Stream.registerSlice? (δ := CoreClock) (α := BitVec 8)
    "byte_slice" "Byte"

#guard match slice with
  | .error _ => false
  | .ok sealed =>
      sealed.component.interface.ports.length == 6 &&
      sealed.component.design.inputs.length == 3 &&
      sealed.component.design.combOutputs.length == 3

/- A stream connection is one typed operation but exactly three scalar graph
connections.  The shared `CoreClock` and `BitVec 8` parameters are the proof
that this is neither an implicit CDC crossing nor a width conversion. -/
private def connectedSlices : Except String ComponentGraph := do
  let first ← slice
  let second ← slice
  let firstInstance : ComponentInstance := ⟨"first", first⟩
  let secondInstance : ComponentInstance := ⟨"second", second⟩
  let ports := Loom.Hw.Stream.registerSlicePorts
    (δ := CoreClock) (α := BitVec 8) "Byte"
  let source ← ports.output.resolve firstInstance
  let sink ← ports.input.resolve secondInstance
  let graph ← (ComponentGraph.empty "stream_pair").addInstance firstInstance
  let graph ← graph.addInstance secondInstance
  Loom.Hw.Stream.connect graph source sink

#guard match connectedSlices with
  | .error _ => false
  | .ok graph => graph.connections.length == 3 && graph.validB

/- Protocol observation forgets stalled cycles but retains accepted payloads
in order. -/
example : Loom.Hw.Stream.transactions
    [{ valid := true, ready := false, payload := 1 },
     { valid := true, ready := true, payload := 1 },
     { valid := false, ready := true, payload := 2 },
     { valid := true, ready := true, payload := 3 }] = [1, 3] := by
  decide

example : Loom.Hw.Stream.Valid
    [{ valid := true, ready := false, payload := 7 },
     { valid := true, ready := true, payload := 7 }] := by
  simp [Loom.Hw.Stream.Valid, Loom.Hw.Stream.Stable]

example : Loom.Hw.Stream.registerStep (some 4) true 9 true = some 9 := by
  exact Loom.Hw.Stream.registerStep_replace 4 9

end Tests.Stream
