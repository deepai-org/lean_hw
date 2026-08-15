-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ClockReset

/-! # Typed clock/reset policy regressions -/

namespace Tests.ClockReset

open Loom.Hw

private inductive SyncClock
private instance : ClockDomain SyncClock where name := "sync"
private instance : DomainPolicy SyncClock where
  edge := .rising
  reset := .synchronous true
private instance : StateElement.CoreCompatible SyncClock where
  rising := rfl
  synchronousActiveHigh := rfl

private inductive AsyncResetClock
private instance : ClockDomain AsyncResetClock where name := "async_reset"
private instance : DomainPolicy AsyncResetClock where
  edge := .rising
  reset := .asynchronousAssertSynchronousRelease true

private inductive ResetlessClock
private instance : ClockDomain ResetlessClock where name := "resetless"
private instance : DomainPolicy ResetlessClock where
  edge := .falling
  reset := .resetless

private def syncElement : StateElement SyncClock (BitVec 8) :=
  ⟨"count", .boot 9#8, .synchronous true 3#8⟩

private def asyncElement : StateElement AsyncResetClock (BitVec 8) :=
  ⟨"count", .unconstrained,
    .asynchronousAssertSynchronousRelease true 4#8⟩

private def resetlessElement : StateElement ResetlessClock (BitVec 8) :=
  ⟨"count", .unconstrained, .resetless⟩

example : syncElement.step ⟨none, true⟩ 10#8 11#8 = 10#8 := by decide
example : syncElement.step ⟨some .rising, true⟩ 10#8 11#8 = 3#8 := by decide
example : asyncElement.step ⟨none, true⟩ 10#8 11#8 = 4#8 := by decide
example : asyncElement.step ⟨none, false⟩ 10#8 11#8 = 10#8 := by decide
example : resetlessElement.step ⟨some .falling, true⟩ 10#8 11#8 = 11#8 := by decide

#guard syncElement.regDecl.init == 3#8

end Tests.ClockReset
