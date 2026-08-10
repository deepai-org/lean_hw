-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Frame
import Machines.Lnp64mini.Core

/-!
# LNP64mini wake/continuation property

This is a machine-specific application of Loom's general
`TransitionProperty`; no scheduling concept is built into the property
language.  A wake changes only `tstate`.  In particular it preserves the
parked thread's ordinary resume PC and every part of its gate continuation.

Parking while inside a gate is intentional LNP64mini behavior and is exercised
by the gate selftest.  The checked rule is therefore continuation preservation,
not a false policy forbidding an in-gate park.
-/

namespace Machines.Lnp64mini.SchedulingInvariant

open Loom.Hw
open Machines.Lnp64mini

/-- The state needed to resume one parked slot, including one arbitrary gate
stack frame.  Quantifying the theorem over `slot` and `depth` covers the whole
bounded continuation stack without embedding either bound in Loom. -/
def wakePreservesContinuation (slot depth : Nat) : TransitionProperty :=
  TransitionProperty.all
    [ .unchanged (tpcRd (L5 slot))
    , .unchanged (tcontRd (L7 (slot * MAXD + depth)))
    , .unchanged (tcdomRd (L7 (slot * MAXD + depth)))
    , .unchanged (gdepthRd (L5 slot))
    , .unchanged in_gate ]

/-- The checked property's inferred names and widths all resolve in the real
LNP64mini Design. Addresses do not affect a memory read footprint, so one
instance validates the declaration surface for every slot/depth. -/
theorem wakePreservesContinuation_footprint_ok :
    design.propertyFootprintOkB (wakePreservesContinuation 0 0).footprint =
      true := by
  decide

theorem wakePreservesContinuation_reflexive (slot depth : Nat) :
    (wakePreservesContinuation slot depth).Reflexive := by
  intro σ
  simp [wakePreservesContinuation, TransitionProperty.all,
    TransitionProperty.unchanged, TransitionProperty.eval]

theorem wakePreservesContinuation_footprint_regs (slot depth : Nat) :
    (wakePreservesContinuation slot depth).footprint.regs =
      [(inGateReg.name, 32), (inGateReg.name, 32)] := by
  rfl

theorem wakePreservesContinuation_regs_unwritten (slot depth : Nat) :
    ∀ coord ∈ (wakePreservesContinuation slot depth).footprint.regs,
      coord ∉ wakeAllApply.regWrites := by
  intro coord selected
  rw [wakePreservesContinuation_footprint_regs] at selected
  have named : coord = (inGateReg.name, 32) := by simpa using selected
  subst coord
  decide

theorem wakePreservesContinuation_mems_unwritten (slot depth : Nat) :
    ∀ coord ∈ (wakePreservesContinuation slot depth).footprint.mems,
      coord.1 ∉ wakeAllApply.memWrites := by
  intro coord _
  have noMemoryWrites : wakeAllApply.memWrites = [] := by decide
  simp [noMemoryWrites]

/-- A local or remote wake cannot corrupt the continuation of any parked
thread.  The result is structural: it holds for every pre-state, slot, and
stack depth, independently of whether a wake guard fires. -/
theorem wake_preserves_continuation (σ : St) (slot depth : Nat) :
    (wakePreservesContinuation slot depth).eval σ
      (wakeAllApply.run σ σ) :=
  wakeAllApply.satisfiesTransition_of_unwritten
    (wakePreservesContinuation slot depth)
    (wakePreservesContinuation_regs_unwritten slot depth)
    (wakePreservesContinuation_mems_unwritten slot depth)
    (wakePreservesContinuation_reflexive slot depth) σ

end Machines.Lnp64mini.SchedulingInvariant
