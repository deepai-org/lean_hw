-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Retime

/-!
# Multi-pass transformation-chain regression

Two independent write-only observation registers are retimed in sequence.
The first pass contributes its strict simulation and the second its
stuttering simulation; their composition transports any source invariant to
the twice-transformed design in one step.
-/

namespace Tests.TransformChain

open Loom Loom.Hw

def source : Design where
  name := "transform_chain_source"
  regs := [⟨"left", 8, 0⟩, ⟨"right", 8, 0⟩]
  mems := []
  outputs := ["left", "right"]
  rules :=
    [ ⟨"set_left", .write 8 "left" (.lit 3)⟩
    , ⟨"set_right", .write 8 "right" (.lit 5)⟩ ]

def afterLeft : Design := retimeReg source "left" 8

def afterBoth : Design := retimeReg afterLeft "right" 8

def cuts : List RetimeCut :=
  [⟨"left", 8⟩, ⟨"right", 8⟩]

example : retimePlan source cuts = afterBoth := rfl

example : retimePlanOkB source cuts = true := by native_decide

/-- Negative control: the second cut is checked against the intermediate
design, where `left__pre` already exists, so reusing the same cut is refused. -/
example : retimePlanOkB source [⟨"left", 8⟩, ⟨"left", 8⟩] = false := by
  native_decide

theorem left_legal : RetimeLegal source "left" 8 := by
  constructor <;>
    simp [source, retimeRegInit, Design.readsReg, Design.writesReg,
      Act.readsReg, Act.writesReg, Expr.readsReg, preName]

theorem right_legal : RetimeLegal afterLeft "right" 8 := by
  constructor <;>
    simp [afterLeft, source, retimeReg, retimeRegInit, Design.readsReg,
      Design.writesReg, Act.readsReg, Act.writesReg, Act.redirectWrite,
      Expr.readsReg, preName]

def planLegal : RetimePlanLegal source cuts :=
  .cons left_legal (.cons right_legal (.nil afterBoth))

/-- The library-level batch pass returns the same composed refinement as the
two manually named intermediate transforms. -/
def plannedChain : StutterSimulation source.toTSys afterBoth.toTSys :=
  retimePlan_stutter source cuts planLegal

/-- The complete proof-carrying transform chain, ordered source to result. -/
def chain : StutterSimulation source.toTSys afterBoth.toTSys :=
  StutterSimulation.ofSimulationComp
    (retimeReg_simulation source "left" 8 left_legal)
    (retimeReg_stutter afterLeft "right" 8 right_legal)

/-- A source invariant reaches the twice-retimed implementation directly. -/
theorem invariant_after_two_passes {P : St → Prop}
    (hP : source.toTSys.Invariant P) :
    afterBoth.toTSys.Invariant (fun state => P (chain.abs state)) :=
  chain.invariant_pullback hP

theorem invariant_after_plan {P : St → Prop}
    (hP : source.toTSys.Invariant P) :
    afterBoth.toTSys.Invariant (fun state => P (plannedChain.abs state)) :=
  plannedChain.invariant_pullback hP

example (state : St) :
    chain.abs state = retimeAbs "left" (retimeAbs "right" state) := rfl

example (state : St) :
    plannedChain.abs state = retimePlanAbs cuts state := by
  simp [plannedChain]

end Tests.TransformChain
