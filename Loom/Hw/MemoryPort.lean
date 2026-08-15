-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Component
import Loom.Hw.SyncRead

/-!
# Typed memory-port library

This module exposes only memory behavior already represented exactly by the
proved Loom core: asynchronous old-data reads, one-tick registered capture,
lane-masked writes lowered to an old-word merge, and explicit ordered write
ports. It does not pretend to support write-first, no-change, nondeterministic,
or mixed-width behavior before those semantics exist in the core.
-/

namespace Loom.Hw

universe u v

namespace MemoryPort

/-- A complete, no-padding partition of a word into equal physical lanes.
Both values and proofs live once in the port, while the mask width is derived
from `lanes`. -/
structure LaneLayout (width : Nat) where
  lanes : Nat
  laneWidth : Nat
  lanesPositive : 0 < lanes
  laneWidthPositive : 0 < laneWidth
  complete : lanes * laneWidth = width
  deriving Repr

namespace LaneLayout

def checked (width laneWidth : Nat) : Except String (LaneLayout width) := do
  if lanePositive : 0 < laneWidth then
    if widthPositive : 0 < width then
      if divides : width % laneWidth = 0 then
        let lanes := width / laneWidth
        have complete : lanes * laneWidth = width := by
          rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero divides)]
        have lanesPositive : 0 < lanes := by
          by_contra notPositive
          have zero : lanes = 0 := Nat.eq_zero_of_not_pos notPositive
          rw [zero] at complete
          simp at complete
          omega
        return ⟨lanes, laneWidth, lanesPositive, lanePositive, complete⟩
      else
        throw s!"memory data width {width} is not divisible by lane width {laneWidth}"
    else throw "memory data width must be positive"
  else throw "memory write lane width must be positive"

def bits (width : Nat) (positive : 0 < width) : LaneLayout width where
  lanes := width
  laneWidth := 1
  lanesPositive := positive
  laneWidthPositive := by omega
  complete := by omega

end LaneLayout

/-- The exact currently supported read-during-write behavior. Reads observe
the pre-cycle memory, independently of writes committed at the edge. -/
inductive ReadDuringWrite where
  | oldData
  deriving Repr, DecidableEq, BEq

/-- The exact currently supported simultaneous-write behavior. Syntactic
order is explicit and the last enabled site wins, matching `Act.run` and the
compiler's ordered physical-port obligation. -/
inductive WriteCollision where
  | orderedLastWins
  deriving Repr, DecidableEq, BEq

/-- Expand one lane-enable bit per lane to a full-width word mask. Lane zero
selects the least-significant lane. -/
def LaneLayout.maskExpr {width : Nat} (layout : LaneLayout width)
    (enable : Expr layout.lanes) : Expr width :=
  (List.range layout.lanes).foldl (fun accumulated lane =>
    let selected : Expr 1 := .slice enable lane 1
    let laneBits : BitVec width :=
      (BitVec.allOnes layout.laneWidth).setWidth width <<<
        (lane * layout.laneWidth)
    .or accumulated (.mux selected (.lit laneBits) (.lit 0))) (.lit 0)

/-- Preserve disabled lanes from `old` and replace enabled lanes from `next`.
This is a pure smart constructor over the existing expression algebra. -/
def LaneLayout.merge {width : Nat} (layout : LaneLayout width)
    (old next : Expr width) (enable : Expr layout.lanes) : Expr width :=
  let mask := layout.maskExpr enable
  .or (.and old (.not mask)) (.and next mask)

/-- Same-clock masked write port. Domain and packed payload types are retained
at the construction boundary; the underlying `Mem` remains the proved scalar
core handle. -/
structure WritePort (δ : Type v) (addressWidth : Nat) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  memory : Mem addressWidth (HwPacked.width α)
  index : Nat
  layout : LaneLayout (HwPacked.width α)

namespace WritePort

def write {δ : Type v} {addressWidth : Nat} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (port : WritePort δ addressWidth α)
    (address : Expr addressWidth) (data : PackedExpr α)
    (enable : Expr port.layout.lanes) : Act :=
  port.memory.write port.index address
    (port.layout.merge (port.memory.rd address) data.bits enable)

theorem write_run_readback {δ : Type v} {addressWidth : Nat} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (port : WritePort δ addressWidth α)
    (address : Expr addressWidth) (data : PackedExpr α)
    (enable : Expr port.layout.lanes) (state accumulator : St) :
    ((port.write address data enable).run state accumulator).mems
        port.memory.name (address.eval state).toNat (HwPacked.width α) =
      (port.layout.merge (port.memory.rd address) data.bits enable).eval state := by
  simp [write, Mem.write, Act.run, MemEnv.set]

end WritePort

/-- A combinational read port. Its result is explicitly the pre-cycle word. -/
structure AsyncReadPort (δ : Type v) (addressWidth : Nat) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  memory : Mem addressWidth (HwPacked.width α)

namespace AsyncReadPort

def read {δ : Type v} {addressWidth : Nat} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (port : AsyncReadPort δ addressWidth α)
    (address : Expr addressWidth) : PackedExpr α :=
  ⟨port.memory.rd address⟩

end AsyncReadPort

/-- A one-tick read port. Capturing into `output` is the existing D19
block-memory shape; the checked design still decides whether every use of the
bank obeys that discipline. -/
structure SyncReadPort (δ : Type v) (addressWidth : Nat) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  memory : Mem addressWidth (HwPacked.width α)
  output : Reg (HwPacked.width α)

namespace SyncReadPort

def request {δ : Type v} {addressWidth : Nat} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (port : SyncReadPort δ addressWidth α)
    (address : Expr addressWidth) : Act :=
  port.output.set (port.memory.rd address)

def read {δ : Type v} {addressWidth : Nat} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (port : SyncReadPort δ addressWidth α) : PackedExpr α :=
  ⟨port.output.rd⟩

theorem request_run {δ : Type v} {addressWidth : Nat} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (port : SyncReadPort δ addressWidth α)
    (address : Expr addressWidth) (state accumulator : St) :
    ((port.request address).run state accumulator).regs
        port.output.name (HwPacked.width α) =
      state.mems port.memory.name (address.eval state).toNat
        (HwPacked.width α) := by
  simp [request, Reg.set, Mem.rd, Act.run, RegEnv.set, Expr.eval]

end SyncReadPort

/-- A bank-level declaration records the semantic policies that all current
ports share. The constructors are deliberately singletons until Loom gains
additional proved core behaviors. -/
structure Bank (δ : Type v) (addressWidth : Nat) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  memory : Mem addressWidth (HwPacked.width α)
  writes : List (WritePort δ addressWidth α)
  readDuringWrite : ReadDuringWrite := .oldData
  writeCollision : WriteCollision := .orderedLastWins

namespace Bank

def writeIndicesUniqueB {δ : Type v} {addressWidth : Nat} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (bank : Bank δ addressWidth α) : Bool :=
  let indices := bank.writes.map (·.index)
  indices.eraseDups.length == indices.length

def locallyValidB {δ : Type v} {addressWidth : Nat} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (bank : Bank δ addressWidth α) : Bool :=
  !bank.memory.name.isEmpty && bank.writeIndicesUniqueB &&
    bank.writes.all (fun port => port.memory == bank.memory)

end Bank

end MemoryPort

end Loom.Hw
