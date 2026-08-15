-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.MemoryPort

/-! # Typed memory-port regressions -/

namespace Tests.MemoryPort

open Loom.Hw
open Loom.Hw.MemoryPort

private inductive CoreClock
private instance : ClockDomain CoreClock where name := "core"

private def bytes : LaneLayout 32 :=
  match LaneLayout.checked 32 8 with
  | .ok layout => layout
  | .error _ => LaneLayout.bits 32 (by omega)

#guard bytes.lanes == 4 && bytes.laneWidth == 8

private def memory : Mem 4 32 := ⟨"words"⟩
private def writePort : WritePort CoreClock 4 (BitVec 32) :=
  ⟨memory, 0, bytes⟩

private def state : St where
  regs := fun _ width => 0#width
  mems := fun name address width =>
    if name == "words" && address == 3 && width == 32 then
      (0x11223344#32).setWidth width
    else 0#width

/- Mask 0101 updates byte lanes 0 and 2 only. -/
#guard (bytes.merge (memory.rd (.lit 3#4)) (.lit 0xAABBCCDD#32)
    (.lit 0b0101#4)).eval state == 0x11BB33DD#32

#guard ((writePort.write (.lit 3#4) ⟨.lit 0xAABBCCDD#32⟩
    (.lit 0b0101#4)).run state state).mems "words" 3 32 == 0x11BB33DD#32

private def readData : Reg 32 := ⟨"read_data"⟩
private def readPort : SyncReadPort CoreClock 4 (BitVec 32) :=
  ⟨memory, readData⟩

#guard ((readPort.request (.lit 3#4)).run state state).regs "read_data" 32 ==
  0x11223344#32

private def bank : Bank CoreClock 4 (BitVec 32) :=
  { memory, writes := [writePort] }

#guard bank.locallyValidB

private def duplicatePortBank : Bank CoreClock 4 (BitVec 32) :=
  { memory, writes := [writePort, writePort] }

#guard !duplicatePortBank.locallyValidB

private def newDataPort : ReadWritePort .newData CoreClock 4 (BitVec 32) :=
  ⟨memory, readData, 0, bytes⟩

private def oldDataPort : ReadWritePort .oldData CoreClock 4 (BitVec 32) :=
  ⟨memory, readData, 0, bytes⟩

private def unchangedPort :
    ReadWritePort .unchangedOutput CoreClock 4 (BitVec 32) :=
  ⟨memory, readData, 0, bytes⟩

/- The same collision has three deliberately different observable results. -/
#guard ((newDataPort.cycle (.lit 1#1) (.lit 3#4) (.lit 1#1) (.lit 3#4)
    ⟨.lit 0xAABBCCDD#32⟩ (.lit 0b0101#4)).run state state).regs
      "read_data" 32 == 0x11BB33DD#32

#guard ((oldDataPort.cycle (.lit 1#1) (.lit 3#4) (.lit 1#1) (.lit 3#4)
    ⟨.lit 0xAABBCCDD#32⟩ (.lit 0b0101#4)).run state state).regs
      "read_data" 32 == 0x11223344#32

private def stateWithOutput : St :=
  { state with regs := state.regs.set "read_data" 0xDEADBEEF#32 }

#guard ((unchangedPort.cycle (.lit 1#1) (.lit 3#4) (.lit 1#1) (.lit 3#4)
    ⟨.lit 0xAABBCCDD#32⟩ (.lit 0b0101#4)).run stateWithOutput stateWithOutput).regs
      "read_data" 32 == 0xDEADBEEF#32

private def byteView : MixedWidthLayout 32 8 :=
  match MixedWidthLayout.checked 32 8 with
  | .ok layout => layout
  | .error _ =>
      { ratio := 4, selectorBits := 2, ratioPositive := by omega,
        portWidthPositive := by omega, complete := by omega,
        powerOfTwo := by decide }

#guard byteView.ratio == 4 && byteView.selectorBits == 2

private def bytePort : MixedWidthPort CoreClock 4 (BitVec 32) (BitVec 8) :=
  ⟨memory, 0, byteView⟩

/- Storage address 3, subword 2 selects byte 0x22. -/
#guard (bytePort.read (.lit 14#6)).bits.eval state == 0x22#8

/- Storage address 3, subword 1 replaces only byte 0x33. -/
#guard ((bytePort.write (.lit 13#6) ⟨.lit 0xAA#8⟩).run state state).mems
    "words" 3 32 == 0x1122AA44#32

#guard match MixedWidthLayout.checked 24 8 with
  | .error _ => true
  | .ok _ => false

end Tests.MemoryPort
