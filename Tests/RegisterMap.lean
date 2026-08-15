-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.RegisterMap

/-! # Typed register-map regressions -/

namespace Tests.RegisterMap

open Loom.Hw
open Loom.Hw.RegisterMap

private def statusReg : Reg 8 := ⟨"status"⟩
private def controlReg : Reg 8 := ⟨"control"⟩
private def commandReg : Reg 8 := ⟨"command"⟩

private def status : Entry .readOnly 8 32 (BitVec 8) where
  name := "STATUS"
  address := 0x00
  register := statusReg
  reset := 0
  fits := by change 8 ≤ 32; omega

private def control : Entry .readWrite 8 32 (BitVec 8) where
  name := "CONTROL"
  address := 0x04
  register := controlReg
  reset := 3
  fits := by change 8 ≤ 32; omega
  writeBehavior := .oneToClear

private def command : Entry .writeOnly 8 32 (BitVec 8) where
  name := "COMMAND"
  address := 0x08
  register := commandReg
  reset := 0
  fits := by change 8 ≤ 32; omega

private def rawRegisters : Map 8 32 :=
  ⟨"device", [status.decl, control.decl, command.decl]⟩

private def registers : Map.Checked 8 32 :=
  match rawRegisters.check? with
  | .ok checked => checked
  | .error _ => ⟨rawRegisters, by native_decide⟩

#guard rawRegisters.locallyValidB
#guard registers.softwareConstants ==
  [⟨"STATUS", 0⟩, ⟨"CONTROL", 4⟩, ⟨"COMMAND", 8⟩]

private def state : St where
  regs := fun name width =>
    if name == "status" && width == 8 then (0xA5#8).setWidth width
    else if name == "control" && width == 8 then (0x0F#8).setWidth width
    else 0#width
  mems := fun _ _ width => 0#width

#guard (registers.decodeRead (.lit 0x00#8)).hit.eval state == 1#1
#guard (registers.decodeRead (.lit 0x00#8)).data.eval state == 0xA5#32
/- Write-only addresses do not appear readable. -/
#guard (registers.decodeRead (.lit 0x08#8)).hit.eval state == 0#1

/- W1C clears bits 0 and 2 from 0x0f, leaving 0x0a. -/
#guard ((registers.decodeWrite (.lit 1#1) (.lit 0x04#8)
    (.lit 0x05#32)).run state state).regs "control" 8 == 0x0A#8

example : PackedExpr (BitVec 8) := status.read
example : Act := control.write ⟨.lit 1#8⟩
example : Act := command.write ⟨.lit 9#8⟩

private def duplicateAddress : Map 8 32 :=
  ⟨"bad", [status.decl, { control.decl with address := 0x00 }]⟩

#guard !duplicateAddress.locallyValidB

#guard match duplicateAddress.check? with
  | .error _ => true
  | .ok _ => false

#guard registers.markdown.contains "`CONTROL`"

end Tests.RegisterMap
