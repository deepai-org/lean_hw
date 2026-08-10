-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.DebugTap
import Machines.Lnp64mini.DebugMapCheck

namespace Tests.DebugTap

open Loom.Hw

def sampleDesign : Design :=
  { name := "debug_sample"
    regs := [⟨"c0_probe", 8, 0⟩, ⟨"c1_probe", 8, 0⟩]
    mems := [], rules := [], inputs := []
    outputs := ["c0_probe", "c1_probe"] }

def probeReg : Reg 8 := ⟨"probe"⟩

def exprDesign : Design :=
  { sampleDesign with
      regs := sampleDesign.regs ++ [⟨"c0_flag", 1, 0⟩, ⟨"c1_flag", 1, 0⟩]
      outputs := sampleDesign.outputs ++ ["c0_flag", "c1_flag"] }

def flagReg : Reg 1 := ⟨"flag"⟩

def impossible : Expr 1 :=
  .and flagReg.rd (.eq probeReg.rd (.lit (BitVec.ofNat 8 0x5a)))

def sampleMap : DebugMap :=
  { name := "sample"
    taps :=
      [ DebugTap.ofDualReg 70 probeReg
      , DebugTap.stickyRaw 71 "first_bad_pc" 32
          "bad0" "pc0" "bad1" "pc1" ] }

def exprMap : DebugMap :=
  { name := "expr_sample"
    taps := [DebugTap.stickyOfDualPredicate 72 "flag_at_5a" impossible
      (haltOnTrigger := true)] }

example : sampleMap.okB sampleDesign = true := by native_decide
example : ({ sampleMap with taps := sampleMap.taps ++
    [DebugTap.raw 70 "collision" 1 "a" "b"] }).okB sampleDesign = false := by
  native_decide
example : ({ sampleMap with taps := [DebugTap.ofDualReg 70 (⟨"missing"⟩ : Reg 8)] }).okB
    sampleDesign = false := by native_decide
example : ({ sampleMap with taps := [DebugTap.raw 70 "zero" 0 "a" "b"] }).okB
    sampleDesign = false := by native_decide
example : exprMap.okB exprDesign = true := by native_decide
example : ({ exprMap with taps := [DebugTap.ofDualExpr 72 "constant" (.lit 1#1)] }).okB
    exprDesign = true := by native_decide
example : ({ exprMap with taps :=
    [DebugTap.ofDualExpr 72 "memory_read" (.memRead 8 "m" (.lit 0#1))] }).okB
    exprDesign = false := by native_decide
example : ({ exprMap with existingPorts := [{ name := "flag", width := 8 }] }).okB
    exprDesign = false := by native_decide
example : ({ exprMap with taps :=
    [{ DebugTap.ofDualReg 72 probeReg with haltOnTrigger := true }] }).okB
    exprDesign = false := by native_decide

def contains (text fragment : String) : Bool := (text.splitOn fragment).length > 1

example : contains sampleMap.render ".o_c0_probe(loom_debug_source_0_p0_c0)" = true := by
  native_decide
example : contains sampleMap.render "always @(posedge sysclk)" = true := by native_decide
example : contains sampleMap.render "if (!loom_debug_valid_1_c0 && (bad0))" = true := by
  native_decide
example : contains sampleMap.render "7'd71: loom_debug_read" = true := by native_decide
example : contains exprMap.render ".o_c0_flag(loom_debug_source_0_p0_c0)" = true := by
  native_decide
example : contains exprMap.render ".o_c0_probe(loom_debug_source_0_p1_c0)" = true := by
  native_decide
example : contains exprMap.render "wire [0:0] loom_debug_expr_0_c0_n1" = true := by
  native_decide
example : contains exprMap.render
    "if (!loom_debug_valid_0_c0 && (loom_debug_expr_0_c0_n" = true := by
  native_decide
example : contains exprMap.render
    "wire loom_debug_halt_request_c0 = loom_debug_valid_0_c0;" = true := by
  native_decide
example : contains exprMap.render
    "wire loom_debug_halt_request_c1 = loom_debug_valid_0_c1;" = true := by
  native_decide

def duplicatePortMap : DebugMap :=
  { name := "duplicate_source"
    taps := [DebugTap.ofDualReg 74 probeReg,
      { DebugTap.ofDualReg 75 probeReg with name := "probe_again" }] }

example : duplicatePortMap.okB sampleDesign = true := by native_decide
example : (duplicatePortMap.render.splitOn ".o_c0_probe(").length = 2 := by native_decide
example : contains duplicatePortMap.render
    "loom_debug_source_1_p0_c0 = loom_debug_source_0_p0_c0" = true := by
  native_decide

end Tests.DebugTap
