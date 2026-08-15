-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Arbiter

/-! # Verified arbitration regressions -/

namespace Tests.Arbiter

open Loom.Hw
open Loom.Hw.Arbiter

private def emptyState : St where
  regs := fun _ width => 0#width
  mems := fun _ _ width => 0#width

private def requests : List (Expr 1) := [.lit 0, .lit 1, .lit 1, .lit 0]

#guard evalGrants emptyState (fixedPriority requests) ==
  [false, true, false, false]

example : (evalGrants emptyState (fixedPriority requests)).count true ≤ 1 :=
  fixedPriority_atMostOne emptyState requests

example : (fixedPolicy.grants requests).length = requests.length :=
  fixedPolicy.length_preserved requests

private def selected : Except String (FixedResult 8) :=
  fixed requests [.lit 10, .lit 20, .lit 30, .lit 40]

#guard match selected with
  | .error _ => false
  | .ok result =>
      result.valid.eval emptyState == 1#1 &&
      result.payload.eval emptyState == 20#8

#guard match fixed (width := 8) requests [.lit 1] with
  | .error _ => true
  | .ok _ => false

end Tests.Arbiter
