-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Temporal

/-! # Temporal semantics and SVA bridge regressions -/

namespace Tests.Temporal

open Loom.Hw
open Loom.Hw.Temporal

private def flag : Reg 1 := ⟨"flag"⟩
private def data : Reg 8 := ⟨"data"⟩

private def state (flagValue : Bool) (dataValue : Nat) : St where
  regs := fun name width =>
    if name == flag.name then
      (if flagValue then 1#1 else 0#1).setWidth width
    else if name == data.name then (BitVec.ofNat 8 dataValue).setWidth width
    else 0#width
  mems := fun _ _ width => 0#width

private def trace : List St :=
  [state false 3, state true 3, state true 4]

example : Property.holdsAt trace 1 (.rose flag.rd) = true := by native_decide
example : Property.holdsAt trace 2 (.fell flag.rd) = false := by native_decide
example : Property.holdsAt trace 0 (.stable (.ofExpr data.rd)) = true := by native_decide
example : Property.holdsAt trace 1 (.stable (.ofExpr data.rd)) = true := by native_decide
example : Property.holdsAt trace 2 (.stable (.ofExpr data.rd)) = false := by native_decide
example : Property.holds trace (.eventuallyWithin 2 (.atom flag.rd)) = true := by native_decide
example : Property.holds trace (.next (.atom flag.rd)) = true := by native_decide

private def rendered : Except String String :=
  Property.toSva
    { name := "flag_rises"
      property := .always (.implies (.atom flag.rd) (.stable (.ofExpr data.rd))) }

#guard match rendered with
  | .error _ => false
  | .ok text =>
      (text.splitOn "loom_history_valid").length > 1 &&
      (text.splitOn "assert property").length > 1 &&
      (text.splitOn "$stable").length > 1

#guard match Property.toSva { name := "", property := .atom flag.rd } with
  | .error _ => true
  | .ok _ => false

private def sby := SymbiYosysPlan.checked "counter" "counter.sv"
  "counter_properties.sv" .prove 40

#guard match sby with
  | .error _ => false
  | .ok plan =>
      let text := plan.render
      (text.splitOn "mode prove").length > 1 &&
      (text.splitOn "depth 40").length > 1 &&
      (text.splitOn "prep -top counter").length > 1

#guard match SymbiYosysPlan.checked "counter" "counter.sv" "props.sv" .prove 0 with
  | .error _ => true
  | .ok _ => false

end Tests.Temporal
