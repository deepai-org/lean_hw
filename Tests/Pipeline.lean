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
#guard fourth.acceptedOutput == some 10

private def stalledBypass := (State.empty 0 : State 0 Nat).step (some 7) false
#guard stalledBypass.output == some 7 && stalledBypass.acceptedOutput.isNone &&
  !stalledBypass.inputReady

private def fullState : State 3 Nat := ⟨[some 1, none, some 2], rfl⟩
private def flushed := fullState.stepWithFlush (some 3) true true
#guard flushed.state.slots == [none, none, none] && !flushed.inputReady &&
  flushed.output.isNone && flushed.discarded == 2

example : occupancy
      (State.advanceWithFlush [some 1, none, some 2] (some 3) true true).1 +
      State.outputAcceptedWithFlush [some 1, none, some 2] (some 3) true true +
      State.discardedByFlush [some 1, none, some 2] true =
    occupancy [some 1, none, some 2] +
      accepted (some 3)
        (State.advanceWithFlush [some 1, none, some 2] (some 3) true true).2 :=
  State.advanceWithFlush_conservation _ _ _ _

example : occupancy (advance [some 1, some 2, none] (some 3) true).1 +
    outputAccepted [some 1, some 2, none] (some 3) true =
      occupancy [some 1, some 2, none] +
        accepted (some 3) (advance [some 1, some 2, none] (some 3) true).2 :=
  advance_conservation _ _ _

private def graph : Except String (DomainComponentGraph CoreClock) :=
  componentGraph? (δ := CoreClock) (α := BitVec 16) "pipe" "Word" 3

#guard match graph with
  | .error _ => false
  | .ok graph =>
      graph.instances.length == 3 && graph.connectionCount == 6 &&
      graph.exportCount == 3 && graph.validB

#guard match graph with
  | .error _ => false
  | .ok graph =>
      match graph.seal? with
      | .error _ => false
      | .ok _ => true

private def pipelineComponent : Except String (DomainComponent CoreClock) :=
  component? (δ := CoreClock) (α := BitVec 16) "pipe" "Word" 3

#guard match pipelineComponent with
  | .error _ => false
  | .ok component =>
      component.sealed.component.interface.ports.map (fun port =>
        (port.name, port.direction)) ==
        [("stage0__in_valid", .input), ("stage0__in_payload", .input),
         ("stage0__in_ready", .output), ("stage2__out_valid", .output),
         ("stage2__out_payload", .output), ("stage2__out_ready", .input)]

#guard match component? (δ := CoreClock) (α := BitVec 16)
    "bad" "Word" 0 with
  | .error _ => true
  | .ok _ => false

private def linkInput (valid payload ready flush : Nat) : InEnv :=
  fun name width => BitVec.ofNat width <|
    if name == "in_valid" then valid
    else if name == "in_payload" then payload
    else if name == "out_ready" then ready
    else if name == "flush" then flush
    else 0

private def combNat (design : Design) (inputs : InEnv) (state : St)
    (name : String) : Nat :=
  match design.combOutputs.find? (fun output => output.name == name) with
  | none => 0
  | some output => (design.evalCombOutput inputs state output).toNat

private def bypass : Except String (DomainComponent CoreClock) :=
  bypassComponent? (δ := CoreClock) (α := BitVec 16) "bypass" "Word"

#guard match bypass with
  | .error _ => false
  | .ok component =>
      let design := component.implementation.design
      combNat design (linkInput 1 0xCAFE 0 0) design.reset "out_valid" == 1 &&
      combNat design (linkInput 1 0xCAFE 0 0) design.reset "out_payload" == 0xCAFE &&
      combNat design (linkInput 1 0xCAFE 0 0) design.reset "in_ready" == 0

private def flushable : Except String (DomainComponent CoreClock) :=
  flushableComponent? (δ := CoreClock) (α := BitVec 16)
    "flushable" "Word"

#guard match flushable with
  | .error _ => false
  | .ok component =>
      let design := component.implementation.design
      let buffered := design.cycleOpen (linkInput 1 0xBEEF 0 0) design.reset
      let flushed := design.cycleOpen (linkInput 0 0 1 1) buffered
      buffered.regs "full" 1 == 1#1 &&
      buffered.regs "payload" 16 == 0xBEEF#16 &&
      combNat design (linkInput 0 0 1 1) buffered "out_valid" == 0 &&
      flushed.regs "full" 1 == 0#1

private def mixedGraph : Except String (DomainComponentGraph CoreClock) := do
  let first ← Stream.registerSlice? (δ := CoreClock) (α := BitVec 16)
    "first" "Word"
  let middle ← flushable
  let last ← bypass
  componentGraphOf? (δ := CoreClock) (α := BitVec 16)
    "mixed" "Word" [first, middle, last]

#guard match mixedGraph with
  | .error _ => false
  | .ok graph =>
      graph.instances.length == 3 && graph.connectionCount == 6 &&
      match graph.flatten? with
      | .error _ => false
      | .ok implementation =>
          implementation.design.inputs.any
            (fun input => input.name == "stage1__flush")

end Tests.Pipeline
