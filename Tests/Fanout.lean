-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Fanout
import Loom.Hw.FastEval

/-!
# Verified fan-out duplication regression

One consumer is moved to a fresh replica while a second consumer remains on
the source. The producer write is mirrored, establishing the coherence
invariant used by the generic refinement theorem.
-/

namespace Tests.Fanout

open Loom Loom.Hw

def source : Design where
  name := "fanout_source"
  regs := [⟨"source", 8, 0⟩, ⟨"left", 8, 0⟩, ⟨"right", 8, 0⟩]
  outputs := ["source", "left", "right"]
  mems := []
  rules :=
    [ ⟨"producer", .write 8 "source" (.add (.reg 8 "source") (.lit 1))⟩
    , ⟨"left_reader", .write 8 "left" (.reg 8 "source")⟩
    , ⟨"right_reader", .write 8 "right" (.reg 8 "source")⟩ ]

def sourceReg : Reg 8 := ⟨"source"⟩

def transformed : Design :=
  duplicateFanoutReg source sourceReg "source__dup" ["left_reader"]

example : duplicateFanoutOkB source "source" 8 "source__dup" = true := by
  native_decide

example : duplicateFanoutRegOkB source sourceReg "source__dup" = true := by
  native_decide

example : transformed.fastWFB = true := by native_decide

/-- Negative control: a replica may not collide with an existing register. -/
example : duplicateFanoutOkB source "source" 8 "left" = false := by
  native_decide

/-- Negative control: source and replica must be distinct. -/
example : duplicateFanoutOkB source "source" 8 "source" = false := by
  native_decide

def duplicateSourceNames : Design :=
  { source with regs := source.regs ++ [⟨"source", 8, 0⟩] }

/-- Negative control: the executable guard rejects an ambiguous source
declaration instead of choosing one reset value and proving another. -/
example : duplicateFanoutOkB duplicateSourceNames "source" 8 "source__dup" = false := by
  native_decide

theorem legal : FanoutLegal source "source" 8 "source__dup" :=
  duplicateFanoutRegOkB_sound source sourceReg "source__dup" (by native_decide)

/-- The selected reader moved to the replica. -/
example : transformed.rules[1]?.map (·.body) =
    some (.write 8 "left" (.reg 8 "source__dup")) := by rfl

/-- The unselected reader remains on the source. -/
example : transformed.rules[2]?.map (·.body) =
    some (.write 8 "right" (.reg 8 "source")) := by rfl

/-- The producer now writes both coherent copies. -/
example : transformed.rules[0]?.map (·.body) = some
    (.seq
      (.write 8 "source" (.add (.reg 8 "source") (.lit 1)))
      (.write 8 "source__dup" (.add (.reg 8 "source") (.lit 1)))) := by
  rfl

theorem coherence : transformed.toTSys.Invariant
    (FanoutCoherent "source" "source__dup") :=
  duplicateFanout_coherent_invariant source "source" 8 "source__dup"
    ["left_reader"] legal

def observationsAgree (state : St) : Prop :=
  state.regs "left" 8 = state.regs "right" 8

theorem source_observations_agree : source.toTSys.Invariant observationsAgree := by
  apply TSys.Inductive.invariant
  constructor
  · intro state initial
    subst state
    rfl
  · intro state next _ step
    subst next
    rfl

/-- A nontrivial source invariant transports through the duplication pass. -/
theorem transformed_observations_agree : transformed.toTSys.Invariant
    (fun state => observationsAgree (fanoutAbs "source__dup" state)) :=
  duplicateFanout_invariant_pullback source "source" 8 "source__dup"
    ["left_reader"] legal source_observations_agree

end Tests.Fanout
