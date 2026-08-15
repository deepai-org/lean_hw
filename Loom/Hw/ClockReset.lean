-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ExternalComponent

/-!
# Typed clock and reset contracts

Clock and reset policy is attached to the phantom domain type. `ResetValue` is
indexed by that policy, so resetless state cannot carry a fictitious reset
value and resettable state cannot omit one. The executable element semantics
covers resetless, synchronous-reset, and asynchronous-assert/synchronous-
release behavior. Lowering to today's scalar `RegDecl` is available only with
an explicit proof that the domain matches the core's rising-edge,
active-high synchronous reset.
-/

namespace Loom.Hw

universe u v

/-- Logical behavior attached to a domain type. Physical clock quality and
reset-tree implementation remain external assumptions. -/
class DomainPolicy (δ : Type v) [ClockDomain δ] where
  edge : ClockEdge
  reset : ResetBehavior

def DomainPolicy.contract (δ : Type v) [ClockDomain δ] [DomainPolicy δ] :
    DomainContract :=
  ⟨ClockDomain.name δ, DomainPolicy.edge δ, DomainPolicy.reset δ⟩

/-- Reset data whose constructors are legal only for the indexed behavior. -/
inductive ResetValue (α : Type u) : ResetBehavior → Type u where
  | resetless : ResetValue α .resetless
  | synchronous (activeHigh : Bool) (value : α) :
      ResetValue α (.synchronous activeHigh)
  | asynchronousAssertSynchronousRelease (activeHigh : Bool) (value : α) :
      ResetValue α (.asynchronousAssertSynchronousRelease activeHigh)

/-- Initialization is separate from reset. An unconstrained value is a real
contract choice and is never silently replaced by zero. -/
inductive Initialization (α : Type u) where
  | unconstrained
  | boot (value : α)
  deriving Repr

/-- One semantically typed state element in one typed domain. -/
structure StateElement (δ : Type v) (α : Type u)
    [ClockDomain δ] [DomainPolicy δ] [HwPacked α] where
  name : String
  initialization : Initialization α
  resetValue : ResetValue α (DomainPolicy.reset δ)

structure DomainEvent where
  edge : Option ClockEdge
  resetAsserted : Bool
  deriving Repr, DecidableEq, BEq

namespace StateElement

private def activeEdge {δ : Type v} [ClockDomain δ] [DomainPolicy δ]
    (event : DomainEvent) : Bool :=
  event.edge == some (DomainPolicy.edge δ)

/-- Exact one-event behavior for one state element. `ordinaryNext` is sampled
only on the domain's active edge. Asynchronous assertion dominates even when
no edge occurs; release resumes ordinary sampling only on an edge. -/
def step {δ : Type v} {α : Type u}
    [ClockDomain δ] [DomainPolicy δ] [HwPacked α]
    (element : StateElement δ α) (event : DomainEvent)
    (current ordinaryNext : α) : α :=
  match DomainPolicy.reset δ, element.resetValue with
  | .resetless, .resetless =>
      if activeEdge (δ := δ) event then ordinaryNext else current
  | .synchronous _, .synchronous _ reset =>
      if activeEdge (δ := δ) event then
        if event.resetAsserted then reset else ordinaryNext
      else current
  | .asynchronousAssertSynchronousRelease _,
      .asynchronousAssertSynchronousRelease _ reset =>
      if event.resetAsserted then reset
      else if activeEdge (δ := δ) event then ordinaryNext else current

/-- Proof that a typed domain has exactly the reset/edge behavior represented
by the current scalar core and emitted neutral RTL. -/
class CoreCompatible (δ : Type v) [ClockDomain δ] [DomainPolicy δ] : Prop where
  rising : DomainPolicy.edge δ = .rising
  synchronousActiveHigh : DomainPolicy.reset δ = .synchronous true

/-- Lower only the policy profile the current proved core actually supports.
The equality witness, rather than a runtime flag, authorizes the cast. -/
def regDecl {δ : Type v} {α : Type u}
    [ClockDomain δ] [DomainPolicy δ] [HwPacked α] [CoreCompatible δ]
    (element : StateElement δ α) : RegDecl :=
  let reset : ResetValue α (.synchronous true) :=
    (CoreCompatible.synchronousActiveHigh (δ := δ)) ▸ element.resetValue
  match reset with
  | .synchronous _ value =>
      ⟨element.name, HwPacked.width α, HwPacked.pack value⟩

end StateElement

end Loom.Hw
