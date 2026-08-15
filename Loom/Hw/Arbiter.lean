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

/-- A user-supplied stateless policy is admitted only together with its grant
count and mutual-exclusion proofs. Stateful policies such as round robin use a
separate state machine and must additionally state their progress premises. -/
structure SafePolicy where
  name : String
  grants : List (Expr 1) → List (Expr 1)
  length_preserved : ∀ requests, (grants requests).length = requests.length
  atMostOne : ∀ state requests,
    (evalGrants state (grants requests)).count true ≤ 1

def fixedPolicy : SafePolicy where
  name := "fixed-priority"
  grants := fixedPriority
  length_preserved := by
    intro requests
    exact fixedFrom_length (.lit 0) requests
  atMostOne := fixedPriority_atMostOne

/-- Whether any request is selected. -/
def anyGrant (grants : List (Expr 1)) : Expr 1 := orTree grants

/-- Select the payload paired with the unique fixed-priority grant. The
fallback is used when no request is active. -/
def selectPayload {width : Nat} (grants : List (Expr 1))
    (payloads : List (Expr width)) (fallback : Expr width) : Expr width :=
  (grants.zip payloads).foldr
    (fun pair rest => .mux pair.1 pair.2 rest) fallback

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

end Arbiter

end Loom.Hw
