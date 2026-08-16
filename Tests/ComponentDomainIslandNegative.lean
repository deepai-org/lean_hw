-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Multiclock

/-! Isolated compile-failure regression for nominal island domains. -/

namespace Tests.ComponentDomainIslandNegative

open Loom.Hw

private inductive CoreClock
private inductive PeripheralClock

private instance : ClockDomain CoreClock where name := "core"
private instance : ClockDomain PeripheralClock where name := "peripheral"

/- A design owned by one domain must not elaborate as an island in another.
Keep this mismatch isolated: rendering several proof-heavy negative commands
in `Tests.Component` triggers a Lean 4.28 evaluator crash. -/
set_option linter.unusedVariables false in
example (design : DomainDesign PeripheralClock) : True := by
  fail_if_success
    let _ : DomainIslandHandle CoreClock :=
      DomainIslandHandle.named "bad" design
  trivial

end Tests.ComponentDomainIslandNegative
