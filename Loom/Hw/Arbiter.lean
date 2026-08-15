-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Component

/-!
# Verified arbitration primitives

Arbitration policies are library values, not syntax. This first module
provides fixed-priority grants and payload selection over arbitrary finite
request lists, together with a Boolean reference model and a proof that no
two grants can be asserted.
-/

namespace Loom.Hw

namespace Arbiter

private def asserted (value : BitVec 1) : Bool := value = 1#1

private def fixedFrom (blocked : Expr 1) : List (Expr 1) → List (Expr 1)
  | [] => []
  | request :: rest =>
      .and request (.not blocked) :: fixedFrom (.or blocked request) rest

private theorem fixedFrom_length (blocked : Expr 1) (requests : List (Expr 1)) :
    (fixedFrom blocked requests).length = requests.length := by
  induction requests generalizing blocked with
  | nil => rfl
  | cons request rest ih => simp [fixedFrom, ih]

/-- Lowest list index has highest priority. -/
def fixedPriority (requests : List (Expr 1)) : List (Expr 1) :=
  fixedFrom (.lit 0) requests

private def fixedBoolFrom (blocked : Bool) : List Bool → List Bool
  | [] => []
  | request :: rest =>
      (request && !blocked) :: fixedBoolFrom (blocked || request) rest

def fixedPriorityBool (requests : List Bool) : List Bool :=
  fixedBoolFrom false requests

/-- Every asserted grant names an asserted request at the same list index. -/
def grantsRespectRequests : List Bool → List Bool → Bool
  | [], [] => true
  | grant :: grants, request :: requests =>
      (!grant || request) && grantsRespectRequests grants requests
  | _, _ => false

private theorem fixedBoolFrom_respects (blocked : Bool) (requests : List Bool) :
    grantsRespectRequests (fixedBoolFrom blocked requests) requests = true := by
  induction requests generalizing blocked with
  | nil => rfl
  | cons request rest ih =>
      cases blocked <;> cases request <;>
        simp [fixedBoolFrom, grantsRespectRequests, ih]

theorem fixedPriorityBool_respects (requests : List Bool) :
    grantsRespectRequests (fixedPriorityBool requests) requests = true := by
  exact fixedBoolFrom_respects false requests

def evalGrants (state : St) (grants : List (Expr 1)) : List Bool :=
  grants.map fun grant => asserted (grant.eval state)

private theorem fixedFrom_eval (state : St) (blocked : Expr 1)
    (requests : List (Expr 1)) :
    evalGrants state (fixedFrom blocked requests) =
      fixedBoolFrom (asserted (blocked.eval state))
        (requests.map fun request => asserted (request.eval state)) := by
  induction requests generalizing blocked with
  | nil => rfl
  | cons request rest ih =>
      simp only [fixedFrom, evalGrants, List.map_cons]
      change _ :: evalGrants state (fixedFrom (.or blocked request) rest) = _
      rw [ih]
      rcases Loom.Hw.bv1_cases (blocked.eval state) with blockedValue | blockedValue <;>
        rcases Loom.Hw.bv1_cases (request.eval state) with requestValue | requestValue <;>
        simp [fixedBoolFrom, asserted, Expr.eval, blockedValue, requestValue]

theorem fixedPriority_eval (state : St) (requests : List (Expr 1)) :
    evalGrants state (fixedPriority requests) =
      fixedPriorityBool
        (requests.map fun request => asserted (request.eval state)) := by
  simpa [fixedPriority, fixedPriorityBool, asserted, Expr.eval] using
    fixedFrom_eval state (.lit 0) requests

private theorem fixedBoolFrom_count (blocked : Bool) (requests : List Bool) :
    (fixedBoolFrom blocked requests).count true ≤ if blocked then 0 else 1 := by
  induction requests generalizing blocked with
  | nil => simp [fixedBoolFrom]
  | cons request rest ih =>
      cases blocked <;> cases request
      · simpa [fixedBoolFrom] using ih false
      · have tail := ih true
        simp [fixedBoolFrom] at tail ⊢
        omega
      · simpa [fixedBoolFrom] using ih true
      · simpa [fixedBoolFrom] using ih true

/-- Fixed-priority arbitration grants at most one requester. -/
theorem fixedPriorityBool_atMostOne (requests : List Bool) :
    (fixedPriorityBool requests).count true ≤ 1 := by
  simpa [fixedPriorityBool] using fixedBoolFrom_count false requests

theorem fixedPriority_atMostOne (state : St) (requests : List (Expr 1)) :
    (evalGrants state (fixedPriority requests)).count true ≤ 1 := by
  rw [fixedPriority_eval]
  exact fixedPriorityBool_atMostOne _

theorem fixedPriority_respects (state : St) (requests : List (Expr 1)) :
    grantsRespectRequests (evalGrants state (fixedPriority requests))
      (requests.map fun request => asserted (request.eval state)) = true := by
  rw [fixedPriority_eval]
  exact fixedPriorityBool_respects _

/-- A user-supplied stateless policy is admitted only together with its grant
count and mutual-exclusion proofs. Stateful policies such as round robin use a
separate state machine and must additionally state their progress premises. -/
structure SafePolicy where
  name : String
  grants : List (Expr 1) → List (Expr 1)
  length_preserved : ∀ requests, (grants requests).length = requests.length
  atMostOne : ∀ state requests,
    (evalGrants state (grants requests)).count true ≤ 1
  respectsRequests : ∀ state requests,
    grantsRespectRequests (evalGrants state (grants requests))
      (requests.map fun request => asserted (request.eval state)) = true

def fixedPolicy : SafePolicy where
  name := "fixed-priority"
  grants := fixedPriority
  length_preserved := by
    intro requests
    exact fixedFrom_length (.lit 0) requests
  atMostOne := fixedPriority_atMostOne
  respectsRequests := fixedPriority_respects

/-- Work conservation is deliberately separate from safety: a safe arbiter
may legally idle, while a work-conserving policy must grant when requested. -/
def WorkConserving (policy : SafePolicy) : Prop :=
  ∀ state requests,
    (requests.map fun request => asserted (request.eval state)).any id = true →
    (evalGrants state (policy.grants requests)).any id = true

private theorem fixedBoolFrom_any_false (requests : List Bool) :
    (fixedBoolFrom false requests).any id = requests.any id := by
  induction requests with
  | nil => rfl
  | cons request rest ih =>
      cases request
      · simpa [fixedBoolFrom] using ih
      · simp [fixedBoolFrom, fixedBoolFrom]

theorem fixedPolicy_workConserving : WorkConserving fixedPolicy := by
  intro state requests active
  change (evalGrants state (fixedPriority requests)).any id = true
  rw [fixedPriority_eval]
  change (fixedBoolFrom false
    (requests.map fun request => asserted (request.eval state))).any id = true
  rw [fixedBoolFrom_any_false]
  exact active

/-- Whether any request is selected. -/
def anyGrant (grants : List (Expr 1)) : Expr 1 := orTree grants

/-- Select the payload paired with the unique fixed-priority grant. The
fallback is used when no request is active. -/
def selectPayload {width : Nat} (grants : List (Expr 1))
    (payloads : List (Expr width)) (fallback : Expr width) : Expr width :=
  match grants, payloads with
  | grant :: grants, payload :: payloads =>
      .mux grant payload (selectPayload grants payloads fallback)
  | _, _ => fallback
termination_by grants

def selectPayloadValue {width : Nat} (grants : List Bool)
    (payloads : List (BitVec width)) (fallback : BitVec width) : BitVec width :=
  match grants, payloads with
  | grant :: grants, payload :: payloads =>
      if grant then payload else selectPayloadValue grants payloads fallback
  | _, _ => fallback
termination_by grants

theorem selectPayload_eval {width : Nat} (state : St)
    (grants : List (Expr 1)) (payloads : List (Expr width))
    (fallback : Expr width) :
    (selectPayload grants payloads fallback).eval state =
      selectPayloadValue (evalGrants state grants)
        (payloads.map fun payload => payload.eval state) (fallback.eval state) := by
  induction grants generalizing payloads with
  | nil => simp [selectPayload, selectPayloadValue, evalGrants]
  | cons grant rest ih =>
      cases payloads with
      | nil => simp [selectPayload, selectPayloadValue, evalGrants]
      | cons payload payloads =>
          simp only [selectPayload, selectPayloadValue, evalGrants, List.map_cons]
          change
            (if grant.eval state = 1#1 then payload.eval state
             else (selectPayload rest payloads fallback).eval state) =
            (if asserted (grant.eval state) then payload.eval state
             else selectPayloadValue (evalGrants state rest)
               (payloads.map fun item => item.eval state) (fallback.eval state))
          rcases Loom.Hw.bv1_cases (grant.eval state) with value | value <;>
            simp [asserted, value, ih]

structure FixedResult (width : Nat) where
  grants : List (Expr 1)
  valid : Expr 1
  payload : Expr width

def fixed {width : Nat} (requests : List (Expr 1))
    (payloads : List (Expr width)) (fallback : Expr width := .lit 0) :
    Except String (FixedResult width) := do
  unless requests.length == payloads.length do
    throw s!"arbiter request/payload count mismatch: {requests.length} requests, {payloads.length} payloads"
  let grants := fixedPriority requests
  return ⟨grants, anyGrant grants, selectPayload grants payloads fallback⟩

/-! ## Stateful two-requester round robin -/

/-- A deliberately exact two-requester round-robin arbiter. `turn = 0`
prefers requester zero and `turn = 1` prefers requester one. The turn changes
only when the selected transaction is accepted, so backpressure cannot rotate
a grant away from a stalled requester. -/
structure TwoWayRoundRobin where
  turn : Reg 1

namespace TwoWayRoundRobin

structure Result where
  grant0 : Expr 1
  grant1 : Expr 1

def grants (arbiter : TwoWayRoundRobin) (request0 request1 : Expr 1) : Result :=
  { grant0 := .and request0 (.or (.not arbiter.turn.rd) (.not request1))
    grant1 := .and request1 (.or arbiter.turn.rd (.not request0)) }

def valid (result : Result) : Expr 1 := .or result.grant0 result.grant1

def select {width : Nat} (result : Result) (payload0 payload1 : Expr width)
    (fallback : Expr width := .lit 0) : Expr width :=
  .mux result.grant0 payload0 (.mux result.grant1 payload1 fallback)

/-- Advance after a downstream acceptance. A lone requester remains eligible
regardless of the stored turn; a contested transfer hands priority to the
other requester. -/
def advance (arbiter : TwoWayRoundRobin) (result : Result)
    (accepted : Expr 1) : Act :=
  let next := .mux result.grant0 (.lit 1)
    (.mux result.grant1 (.lit 0) arbiter.turn.rd)
  .ite (.and accepted (valid result)) (arbiter.turn.set next) .skip

theorem grants_atMostOne (arbiter : TwoWayRoundRobin) (state : St)
    (request0 request1 : Expr 1) :
    (evalGrants state
      [(arbiter.grants request0 request1).grant0,
       (arbiter.grants request0 request1).grant1]).count true ≤ 1 := by
  rcases Loom.Hw.bv1_cases (arbiter.turn.rd.eval state) with turn | turn <;>
    simp [Reg.rd, Expr.eval] at turn <;>
    rcases Loom.Hw.bv1_cases (request0.eval state) with first | first <;>
    rcases Loom.Hw.bv1_cases (request1.eval state) with second | second <;>
    simp [grants, evalGrants, asserted, Expr.eval, Reg.rd, turn, first, second]

theorem grants_respect_requests (arbiter : TwoWayRoundRobin) (state : St)
    (request0 request1 : Expr 1) :
    grantsRespectRequests
      (evalGrants state
        [(arbiter.grants request0 request1).grant0,
         (arbiter.grants request0 request1).grant1])
      [asserted (request0.eval state), asserted (request1.eval state)] = true := by
  rcases Loom.Hw.bv1_cases (arbiter.turn.rd.eval state) with turn | turn <;>
    simp [Reg.rd, Expr.eval] at turn <;>
    rcases Loom.Hw.bv1_cases (request0.eval state) with first | first <;>
    rcases Loom.Hw.bv1_cases (request1.eval state) with second | second <;>
    simp [grants, evalGrants, grantsRespectRequests, asserted, Expr.eval,
      Reg.rd, turn, first, second]

theorem workConserving (arbiter : TwoWayRoundRobin) (state : St)
    (request0 request1 : Expr 1)
    (active : asserted (request0.eval state) || asserted (request1.eval state) = true) :
    (evalGrants state
      [(arbiter.grants request0 request1).grant0,
       (arbiter.grants request0 request1).grant1]).any id = true := by
  rcases Loom.Hw.bv1_cases (arbiter.turn.rd.eval state) with turn | turn <;>
    simp [Reg.rd, Expr.eval] at turn <;>
    rcases Loom.Hw.bv1_cases (request0.eval state) with first | first <;>
    rcases Loom.Hw.bv1_cases (request1.eval state) with second | second <;>
    simp [grants, evalGrants, asserted, Expr.eval, Reg.rd,
      turn, first, second] at active ⊢

end TwoWayRoundRobin

end Arbiter

end Loom.Hw
