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

example : grantsRespectRequests
    (evalGrants emptyState (fixedPolicy.grants requests))
    (requests.map fun request => request.eval emptyState == 1#1) = true :=
  fixedPolicy.respectsRequests emptyState requests

example : WorkConserving fixedPolicy := fixedPolicy_workConserving

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

private def turn : Reg 1 := ⟨"turn"⟩
private def roundRobin : TwoWayRoundRobin := ⟨turn⟩

private def turnState (value : BitVec 1) : St where
  regs := fun name width =>
    if name == "turn" && width == 1 then value.setWidth width else 0#width
  mems := fun _ _ width => 0#width

/- Contention follows the stored turn; a lone requester is never blocked. -/
#guard let result := roundRobin.grants (.lit 1) (.lit 1)
  evalGrants (turnState 0) [result.grant0, result.grant1] == [true, false]
#guard let result := roundRobin.grants (.lit 1) (.lit 1)
  evalGrants (turnState 1) [result.grant0, result.grant1] == [false, true]
#guard let result := roundRobin.grants (.lit 1) (.lit 0)
  evalGrants (turnState 1) [result.grant0, result.grant1] == [true, false]

example (state : St) (request0 request1 : Expr 1) :
    (evalGrants state
      [(roundRobin.grants request0 request1).grant0,
       (roundRobin.grants request0 request1).grant1]).count true ≤ 1 :=
  roundRobin.grants_atMostOne state request0 request1

/- Acceptance of requester zero hands the next contested grant to one. -/
#guard let result := roundRobin.grants (.lit 1) (.lit 1)
  ((roundRobin.advance result (.lit 1)).run (turnState 0) (turnState 0)).regs
    "turn" 1 == 1#1

end Tests.Arbiter
