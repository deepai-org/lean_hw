-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Component

/-! Isolated compile-failure regression for nominal connection domains. -/

namespace Tests.ComponentConnectionNegative

open Loom.Hw

private inductive CoreClock
private inductive PeripheralClock

private instance : ClockDomain CoreClock where name := "core"
private instance : ClockDomain PeripheralClock where name := "peripheral"

/- A graph must not accept a connection carrying another nominal domain. -/
set_option linter.unusedVariables false in
example (graph : DomainComponentGraph CoreClock)
    (connection : DomainConnection PeripheralClock) : True := by
  fail_if_success
    let _ := graph.connect connection
  trivial

end Tests.ComponentConnectionNegative
