-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Tests.PrettyDsl

/-! Persistent pretty-hardware metadata remains available to downstream proof
and inspection modules; it is not confined to the source file's elaborator. -/

open Loom.Hw.Dsl
open Loom.Hw
open Tests.PrettyDsl.SharedConstants

/- A bare `@[hw_const]` is intentionally source-file local. Importing the
module does not make it an ambient hardware-expression candidate. -/
/--
error: Nat values are not implicitly hardware expressions; mark a shared constant @[hw_const] or use a design-local `const`
-/
#guard_msgs in
example : Expr 8 := [hwexpr| OPCODE]

open scoped SharedOpcodes

/-- Only the explicitly exported scope crosses the module boundary. -/
example : ([hwexpr| SCOPED_OPCODE] : Expr 8) = .lit 0x2a#8 := rfl

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
