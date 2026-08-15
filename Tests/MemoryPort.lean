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

end Tests.MemoryPort
