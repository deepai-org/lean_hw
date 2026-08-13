-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Dsl
import Loom.Hw.Semantics

/-!
# Pretty hardware syntax regressions

The surface quotations below must lower definitionally to the established
`Expr` and `Act` constructors.  They are syntax tests, not a second semantics.
-/

namespace Tests.PrettyDsl

open Loom.Hw
open Loom.Hw.Dsl

packed struct Header where
  tag : 3
  address : 5

packed struct RequestShape where
  address : 64
  write : 1
  size : 3
  data : 64

example : HwPacked.width Header = 8 := rfl
example : HwPacked.width RequestShape = 132 := rfl
example : RequestShape.layout.fields.map (fun field => field.lo) =
    [68, 67, 64, 0] := by native_decide
example : Header.layout.fields =
    [⟨"tag", 3, 5⟩, ⟨"address", 5, 0⟩] := by native_decide
example : Header.tagField.lo = 5 := rfl
example : Header.addressField.lo = 0 := rfl
example : HwPacked.pack ({ tag := 5#3, address := 17#5 } : Header) = 0xb1#8 := rfl
example (value : Header) : HwPacked.unpack (HwPacked.pack value) = value :=
  HwPacked.unpack_pack value
example (bits : BitVec 8) : HwPacked.pack (HwPacked.unpack (α := Header) bits) = bits :=
  HwPacked.pack_unpack (α := Header) bits

private def headerReg : PackedReg Header := .named "header"
private def headerInput : PackedInput Header := .named "header_input"
example : ([hwexpr| headerReg.tag] : Expr 3) =
    Header.tagField.read headerReg.rd := rfl
example : ([hwexpr| headerInput.address] : Expr 5) =
    Header.addressField.read headerInput.rd := rfl
example : [hwstmt| headerReg.tag <- 3] =
    headerReg.setField Header.tagField (.lit 3#3) := rfl

/-- error: duplicate packed field 'tag' -/
#guard_msgs in
packed struct DuplicateHeader where
  tag : 3
  tag : 5

/-- error: packed fields must have positive width -/
#guard_msgs in
packed struct ZeroWidthHeader where
  empty : 0

private def a : Reg 8 := ⟨"a"⟩
private def b : Reg 8 := ⟨"b"⟩
private def flag : Reg 1 := ⟨"flag"⟩
private def ram : Mem 4 8 := ⟨"ram"⟩
private def helper : Expr 8 := .xor a.rd b.rd
private def helperAct : Act := flag.set (.lit 1)
private def generatedValue (_ : Nat) : Expr 8 := .lit 7
private def staticShift : Nat := 3

example : ([hwexpr| a + b * 3] : Expr 8) =
    Expr.add a.rd (Expr.mul b.rd (.lit 3)) := rfl

example : ([hwexpr| (a + b) << 2] : Expr 8) =
    Expr.shl (Expr.add a.rd b.rd) (.lit 2) := rfl
example : ([hwexpr| a << staticShift] : Expr 8) = Expr.shl a.rd (.lit 3) := rfl
example (dynamicShift : Reg 8) : Expr 8 := [hwexpr| a >> dynamicShift]

example : ([hwexpr| a == b] : Expr 1) = Expr.eq a.rd b.rd := rfl
example : ([hwexpr| $(helper)] : Expr 8) = helper := rfl

example : ([hwexpr| a[7:4]] : Expr 4) = Expr.slice a.rd 4 4 := rfl
example : ([hwexpr| b[0]] : Expr 1) = Expr.slice b.rd 0 1 := rfl
example : ([hwexpr| zext a[3:0] to 8] : Expr 8) =
    Expr.zext (Expr.slice a.rd 0 4) 8 := rfl

example : [hwstmt| { a <- b + 1, flag <- 1 }] =
    Act.seq (a.set (.add b.rd (.lit 1))) (flag.set (.lit 1)) := rfl

example : [hwstmt| if flag then a <- b else b <- a] =
    Act.ite flag.rd (a.set b.rd) (b.set a.rd) := rfl
example : [hwstmt| $stmt(helperAct)] = helperAct := rfl
example : [hwstmt| ram[port 2, a[3:0]] <- b] =
    ram.write 2 (.slice a.rd 0 4) b.rd := rfl
example : ([hwexpr| ram[a[3:0]]] : Expr 8) = ram.rd (.slice a.rd 0 4) := rfl
example : [hwstmt| for i in $([0, 1]) generate a <- $(generatedValue i)] =
    Act.seq (a.set (.lit 7)) (a.set (.lit 7)) := rfl

example (register : Reg 8) : Act := [hwstmt| register <- register + 1]
example (expression : Expr 8) : Expr 8 := [hwexpr| expression * 3]

example : [hwstmt| { let next : 8 := a + 1, b <- next }] =
    (let next : Expr 8 := .add a.rd (.lit 1); b.set next) := rfl

private def zeroSt : St where
  regs := fun _ w => BitVec.ofNat w 0
  mems := fun _ _ w => BitVec.ofNat w 0

example : ([hwexpr| 0xff + 2] : Expr 8).eval zeroSt = 1#8 := by decide
example : ([hwexpr| 1 << 8] : Expr 8).eval zeroSt = 0#8 := by decide
example : ([hwexpr| 0b1010_0011] : Expr 8).eval zeroSt = 0xa3#8 := by decide

end Tests.PrettyDsl

namespace Tests.PrettyDsl.Counter

open Loom.Hw
open Loom.Hw.Dsl

hardware satcounter where
  output reg count : 8
  output reg sat : 1

  rule tick :=
    if count == 255 then
      sat <- 1
    else
      count <- count + 1

example : declarations.outputs = ["count", "sat"] := by decide
example : design.rules = [⟨"tick", tick⟩] := rfl

private def expectedTick : Act :=
  .ite (.eq count.rd (.lit 255))
    (sat.set (.lit 1))
    (count.set (.add count.rd (.lit 1)))

example : tick = expectedTick := rfl

example : design.name = "satcounter" := by
  hw_unfold design

/--
info: hardware satcounter
declarations:
  count: register 8 bits
  sat: register 1 bits
rules:
  tick
-/
#guard_msgs in
#show_hardware design

/-! The teaching executor is an inspection view over the existing one-cycle
semantics. This trace also pins the old-value/new-value presentation. -/
/--
info: rule tick: count 254 -> 255
final registers:
  count = 255
  sat = 0
-/
#guard_msgs in
#trace_cycle design with {} from { count := 254 }

/--
info: after 256 cycles:
  count = 255
  sat = 1
-/
#guard_msgs in
#run_hardware design for 256 cycles

end Tests.PrettyDsl.Counter

namespace Tests.PrettyDsl.Fsm

open Loom.Hw
open Loom.Hw.Dsl

hardware tiny_fsm where
  const CMD_QUANTUM : 7 := 72
  output states st : { Idle, Run, Done } := Idle
  output reg seen : 7

  rule advance :=
    case st of
    | Idle => { st <- Run, seen <- CMD_QUANTUM }
    | Run => st <- Done
    | Done => st <- Idle

example : st = (⟨"st"⟩ : Reg 2) := rfl
example : Idle = (Expr.lit 0 : Expr 2) := rfl
example : Run = (Expr.lit 1 : Expr 2) := rfl
example : Done = (Expr.lit 2 : Expr 2) := rfl
example : CMD_QUANTUM = (Expr.lit 72 : Expr 7) := rfl
example : declarations.outputs = ["st", "seen"] := by decide
example : declarations.regs.head?.map (fun declaration => declaration.init.toNat) = some 0 := by
  decide

end Tests.PrettyDsl.Fsm

namespace Tests.PrettyDsl.Interface

open Loom.Hw
open Loom.Hw.Dsl

hardware interface_demo where
  input enable : 1
  output reg count : 8 := 0xfe
  output wire done : 1 := count == 0xff

  rule tick :=
    if enable then count <- count + 1

example : declarations.inputs.map (fun declaration => declaration.name) = ["enable"] := by
  decide
example : enable = (⟨"enable"⟩ : Input 1) := rfl
example : enable.name = "enable" := by simp
example : count.name = "count" := by simp
example : declarations.combOutputs.map (fun declaration => declaration.name) = ["done"] := by
  decide
example : declarations.regs.head?.map (fun declaration => declaration.init.toNat) = some 0xfe := by
  decide

end Tests.PrettyDsl.Interface

namespace Tests.PrettyDsl.Memory

open Loom.Hw
open Loom.Hw.Dsl

hardware memory_demo where
  input address : 4
  input write_data : 8
  output reg read_data : 8
  memory scratch : 8 [16] using Memory.synchronousRead

  rule access := {
    scratch[port 0, address] <- write_data,
    read_data <- scratch[address]
  }

example : scratch = (⟨"scratch"⟩ : Mem 4 8) := rfl
example : declarations.mems.map (fun declaration =>
    (declaration.name, declaration.addrWidth, declaration.dataWidth)) =
    [("scratch", 4, 8)] := by decide
example : declarations.syncReadMems = ["scratch"] := by decide

end Tests.PrettyDsl.Memory

namespace Tests.PrettyDsl.PackedHardware

open Loom.Hw
open Loom.Hw.Dsl
open Tests.PrettyDsl

hardware packed_demo where
  input wire incoming : Header
  output reg pending : Header
  output wire observed : Header := pending
  output wire observed_tag : 3 := pending.tag

  rule capture := {
    pending <- incoming,
    pending.tag <- incoming.tag
  }

example : pending = (PackedReg.named "pending" : PackedReg Header) := rfl
example : incoming = (PackedInput.named "incoming" : PackedInput Header) := rfl
example : declarations.regs.map (fun declaration =>
    (declaration.name, declaration.width)) = [("pending", 8)] := by decide
example : declarations.inputs.map (fun declaration =>
    (declaration.name, declaration.width)) = [("incoming", 8)] := by decide
example : declarations.outputs = ["pending"] := by decide
example : declarations.combOutputs.map (fun declaration =>
    (declaration.name, declaration.width)) = [("observed", 8), ("observed_tag", 3)] := by
  decide

/--
info: hardware packed_demo
declarations:
  incoming: input 8 bits
  pending: register 8 bits
  observed: combinational output 8 bits
  observed_tag: combinational output 3 bits
rules:
  capture
-/
#guard_msgs in
#show_hardware design

end Tests.PrettyDsl.PackedHardware

namespace Tests.PrettyDsl.RegisterFamily

open Loom.Hw
open Loom.Hw.Dsl

hardware family_demo where
  input index : 2
  input value : 8
  output reg slots : 8 [4]
  output reg observed : 8

  rule access := {
    slots[index] <- value,
    observed <- slots[index]
  }

example : slots = (⟨"slots"⟩ : RegArray 8 4) := rfl
example : ([hwexpr| slots[2]] : Expr 8) = slots.rd ⟨2, by decide⟩ := rfl
example : [hwstmt| slots[2] <- 9] = slots.set ⟨2, by decide⟩ (.lit 9#8) := rfl
example : declarations.regs.map (fun declaration => declaration.name) =
    ["observed", "slots0", "slots1", "slots2", "slots3"] := by decide
example : declarations.outputs =
    ["observed", "slots0", "slots1", "slots2", "slots3"] := by decide

/-- error: register-family index 4 is outside 0 through 3 -/
#guard_msgs in
example : Expr 8 := [hwexpr| slots[4]]

end Tests.PrettyDsl.RegisterFamily

/--
error: memory depth 12 is not a power of two; the current Mem core represents exactly 2^addressWidth cells
-/
#guard_msgs in
hardware bad_depth where
  memory scratch : 8 [12]

namespace Tests.PrettyDsl.Lints

open Loom.Hw
open Loom.Hw.Dsl

namespace Reported

/--
warning: 'a' reads its start-of-cycle value; an earlier write takes effect next cycle
---
warning: 'a' may be written more than once in one cycle; the later write wins
-/
#guard_msgs in
hardware lint_demo where
  reg a : 8
  reg b : 8
  rule demonstrate := { a <- 1, b <- a, a <- 2 }

end Reported

namespace Suppressed

#guard_msgs in
hardware suppressed_lints where
  reg x : 8
  reg y : 8
  rule first suppress multiple_write because "the second assignment is intentional" := {
    x <- 1,
    suppress read_after_write because "this rule deliberately samples the old value" in
      y <- x,
    x <- 2
  }

/--
info: hardware suppressed_lints
declarations:
  x: register 8 bits
  y: register 8 bits
rules:
  first
lint suppressions:
  first: suppress multiple_write because "the second assignment is intentional"
  first: suppress read_after_write because "this rule deliberately samples the old value"
-/
#guard_msgs in
#show_hardware design

end Suppressed

end Tests.PrettyDsl.Lints

namespace Tests.PrettyDsl.Diagnostics

open Loom.Hw
open Loom.Hw.Dsl

private def a : Reg 8 := ⟨"a"⟩
private def b : Reg 8 := ⟨"b"⟩

/-- error: literal 300 does not fit in 8 bits; expected 0 through 255 -/
#guard_msgs in
example : Expr 8 := [hwexpr| 300]

/-- error: shift and arithmetic operators require parentheses; parenthesize the intended grouping -/
#guard_msgs in
example : Expr 8 := [hwexpr| a + b << 2]

/-- error: comparison and bitwise operators require parentheses; parenthesize the intended grouping -/
#guard_msgs in
example : Expr 1 := [hwexpr| a & b == a]

/-- error: literal 256 does not fit in 8 bits; expected 0 through 255 -/
#guard_msgs in
hardware bad_reset where
  reg overflowing : 8 := 256

/-- error: 'readonly' is not a writable register in this hardware block -/
#guard_msgs in
hardware bad_input_write where
  input readonly : 1
  rule bad := readonly <- 1

/-- error: non-exhaustive state case; missing Broken -/
#guard_msgs in
hardware bad_state_case where
  states mode : { Ready, Busy, Broken }
  rule incomplete :=
    case mode of
    | Ready => { mode <- Busy }
    | Busy => { mode <- Ready }

end Tests.PrettyDsl.Diagnostics
