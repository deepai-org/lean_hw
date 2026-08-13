-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Tests.PrettyDsl

/-! Persistent pretty-hardware metadata remains available to downstream proof
and inspection modules; it is not confined to the source file's elaborator. -/

open Loom.Hw.Dsl

/--
info: pretty hardware (source round trip checked)
hardware satcounter where
  output reg count : 8
  output reg sat : 1

  rule tick :=
    if count == 255 then
      sat <- 1
    else
      count <- count + 1
-/
#guard_msgs in
#show_hardware Tests.PrettyDsl.Counter.design

example : Tests.PrettyDsl.Counter.design.name = "satcounter" := by
  hw_unfold Tests.PrettyDsl.Counter.design
