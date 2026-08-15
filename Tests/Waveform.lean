-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Waveform

/-! # Replayable waveform regressions -/

namespace Tests.Waveform

open Loom.Hw

private def count : Reg 8 := ⟨"count"⟩
private def enable : Reg 1 := ⟨"enable"⟩

private def design : Design where
  name := "wave_counter"
  regs := [count.decl 0]
  mems := []
  inputs := [enable.input]
  rules := [⟨"tick", .ite enable.rd (count.set (.add count.rd (.lit 1))) .skip⟩]
  outputs := [count.name]

private def stimulus (enabled reset : Bool) :
    Except String (Waveform.ValidatedStimulus design) :=
  Waveform.ValidatedStimulus.checked design
    { reset
      drives := [Waveform.Drive.ofInput enable.input (if enabled then 1#1 else 0#1)] }

private def trace? : Except String Waveform.Trace := do
  let reset ← stimulus false true
  let tick ← stimulus true false
  let hold ← stimulus false false
  return Waveform.record design (Loom.Artifact.Identity.ofText "exact RTL")
    [reset, tick, hold]

#guard match trace? with
  | .error _ => false
  | .ok trace =>
      match stimulus false true, stimulus true false, stimulus false false with
      | .ok reset, .ok tick, .ok hold =>
          Waveform.replayB design (Loom.Artifact.Identity.ofText "exact RTL")
            [reset, tick, hold] trace
      | _, _, _ => false

#guard match trace? with
  | .error _ => false
  | .ok trace =>
      match Waveform.renderVcd trace with
      | .error _ => false
      | .ok text =>
          (text.splitOn "$var wire 8").length > 1 &&
          (text.splitOn "state.count").length > 1 &&
          (text.splitOn "#5").length > 1

#guard match Waveform.ValidatedStimulus.checked design
    { reset := false, drives := [] } with
  | .error _ => true
  | .ok _ => false

end Tests.Waveform
