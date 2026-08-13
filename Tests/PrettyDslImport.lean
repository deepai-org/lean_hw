-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Tests.PrettyDsl

/-! Persistent pretty-hardware metadata remains available to downstream proof
and inspection modules; it is not confined to the source file's elaborator. -/

open Loom.Hw.Dsl

/--
info: hardware satcounter
declarations:
  count: register 8 bits
  sat: register 1 bits
rules:
  tick
-/
#guard_msgs in
#show_hardware Tests.PrettyDsl.Counter.design

example : Tests.PrettyDsl.Counter.design.name = "satcounter" := by
  hw_unfold Tests.PrettyDsl.Counter.design
