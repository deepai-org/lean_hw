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

example : Loom.Hw.Stream.transactions
    (Loom.Hw.Stream.mapSamples (· + 10)
      [{ valid := true, ready := true, payload := 1 },
       { valid := true, ready := false, payload := 2 },
       { valid := true, ready := true, payload := 2 }]) = [11, 12] := by
  decide

private def incrementMapper : Except String Component.Sealed :=
  Loom.Hw.Stream.mapper? (δ := CoreClock) (α := BitVec 8) (β := BitVec 8)
    "increment" "Byte" "Byte" fun value =>
      ⟨.add value.bits (.lit 1#8)⟩

#guard match incrementMapper with
  | .error _ => false
  | .ok sealed =>
      sealed.component.design.regs.isEmpty &&
      sealed.component.design.rules.isEmpty &&
      sealed.component.design.combOutputs.length == 3

/- A mapper connected back to itself would be a zero-delay valid, payload,
and ready loop. The graph rejects the first cyclic edge at construction. -/
#guard match do
    let mapper ← incrementMapper
    let inst : ComponentInstance := ⟨"loop", mapper⟩
    let ports := Loom.Hw.Stream.mapperPorts
      (δ := CoreClock) (α := BitVec 8) (β := BitVec 8) "Byte" "Byte"
    let source ← ports.output.resolve inst
    let sink ← ports.input.resolve inst
    let graph ← (ComponentGraph.empty "bad_loop").addInstance inst
    Loom.Hw.Stream.connect graph source sink with
  | .error _ => true
  | .ok _ => false

end Tests.Stream
