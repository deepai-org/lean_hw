-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Component
import Loom.Hw.SyncRead

/-!
# Typed memory-port library

This module exposes memory behavior represented exactly by ordinary Loom
actions: asynchronous reads, one-tick registered capture, lane-masked writes,
explicit ordered write ports, and deterministic old-data, new-data, or
unchanged-output read/write collisions. It does not pretend to support a
nondeterministic or mixed-width contract before those semantics exist.
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

/-- Cycle-visible behavior when one synchronous read and write address match.
Each constructor has a distinct lowering below. -/
inductive ReadDuringWrite where
  | oldData
  | newData
  | unchangedOutput
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

/-- A same-domain combined synchronous-read/masked-write port. The policy is
part of the port's type, so a client cannot accidentally substitute a port
with different collision behavior merely because its widths match. -/
structure ReadWritePort (policy : ReadDuringWrite) (δ : Type v)
    (addressWidth : Nat) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  memory : Mem addressWidth (HwPacked.width α)
  output : Reg (HwPacked.width α)
  index : Nat
  layout : LaneLayout (HwPacked.width α)

namespace ReadWritePort

private def collision {policy : ReadDuringWrite} {δ : Type v}
    {addressWidth : Nat} {α : Type u} [ClockDomain δ] [HwPacked α]
    (_port : ReadWritePort policy δ addressWidth α)
    (readEnable writeEnable : Expr 1)
    (readAddress writeAddress : Expr addressWidth) : Expr 1 :=
  .and readEnable (.and writeEnable (.eq readAddress writeAddress))

private def nextWord {policy : ReadDuringWrite} {δ : Type v}
    {addressWidth : Nat} {α : Type u} [ClockDomain δ] [HwPacked α]
    (port : ReadWritePort policy δ addressWidth α)
    (writeAddress : Expr addressWidth) (writeData : PackedExpr α)
    (writeLanes : Expr port.layout.lanes) : Expr (HwPacked.width α) :=
  port.layout.merge (port.memory.rd writeAddress) writeData.bits writeLanes

/-- One explicitly enabled port cycle. Reads capture at the edge. Writes use
the same edge and commit the lane merge. `newData` bypasses the merged word on
a collision; `unchangedOutput` suppresses the read-register update. -/
def cycle {policy : ReadDuringWrite} {δ : Type v}
    {addressWidth : Nat} {α : Type u} [ClockDomain δ] [HwPacked α]
    (port : ReadWritePort policy δ addressWidth α)
    (readEnable : Expr 1) (readAddress : Expr addressWidth)
    (writeEnable : Expr 1) (writeAddress : Expr addressWidth)
    (writeData : PackedExpr α) (writeLanes : Expr port.layout.lanes) : Act :=
  let same := collision port readEnable writeEnable readAddress writeAddress
  let merged := port.nextWord writeAddress writeData writeLanes
  let readAction := match policy with
    | .oldData =>
        .ite readEnable (port.output.set (port.memory.rd readAddress)) .skip
    | .newData =>
        .ite readEnable
          (port.output.set (.mux same merged (port.memory.rd readAddress))) .skip
    | .unchangedOutput =>
        .ite (.and readEnable (.not same))
          (port.output.set (port.memory.rd readAddress)) .skip
  let writeAction :=
    .ite writeEnable (port.memory.write port.index writeAddress merged) .skip
  .seq readAction writeAction

def read {policy : ReadDuringWrite} {δ : Type v}
    {addressWidth : Nat} {α : Type u} [ClockDomain δ] [HwPacked α]
    (port : ReadWritePort policy δ addressWidth α) : PackedExpr α :=
  ⟨port.output.rd⟩

end ReadWritePort

/-- Same-domain simple dual port: one synchronous reader and one masked writer
over the same memory. The shared handle is stored once, so membership cannot
drift between separately assembled ports. -/
structure SimpleDualPort (δ : Type v) (addressWidth : Nat) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  memory : Mem addressWidth (HwPacked.width α)
  readOutput : Reg (HwPacked.width α)
  writeIndex : Nat
  layout : LaneLayout (HwPacked.width α)

namespace SimpleDualPort

def readPort {δ : Type v} {addressWidth : Nat} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (port : SimpleDualPort δ addressWidth α) : SyncReadPort δ addressWidth α :=
  ⟨port.memory, port.readOutput⟩

def writePort {δ : Type v} {addressWidth : Nat} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (port : SimpleDualPort δ addressWidth α) : WritePort δ addressWidth α :=
  ⟨port.memory, port.writeIndex, port.layout⟩

end SimpleDualPort

/-- Same-domain true dual port with independently selected deterministic read
collision policies. Port indices are distinct by construction; action order A
then B makes B the explicit winner of a simultaneous same-address write. -/
structure TrueDualPort (policyA policyB : ReadDuringWrite)
    (δ : Type v) (addressWidth : Nat) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  memory : Mem addressWidth (HwPacked.width α)
  outputA : Reg (HwPacked.width α)
  outputB : Reg (HwPacked.width α)
  indexA : Nat
  indexB : Nat
  indicesDistinct : indexA ≠ indexB
  layout : LaneLayout (HwPacked.width α)

namespace TrueDualPort

def portA {policyA policyB : ReadDuringWrite}
    {δ : Type v} {addressWidth : Nat} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (ports : TrueDualPort policyA policyB δ addressWidth α) :
    ReadWritePort policyA δ addressWidth α :=
  ⟨ports.memory, ports.outputA, ports.indexA, ports.layout⟩

def portB {policyA policyB : ReadDuringWrite}
    {δ : Type v} {addressWidth : Nat} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (ports : TrueDualPort policyA policyB δ addressWidth α) :
    ReadWritePort policyB δ addressWidth α :=
  ⟨ports.memory, ports.outputB, ports.indexB, ports.layout⟩

def cycle {policyA policyB : ReadDuringWrite}
    {δ : Type v} {addressWidth : Nat} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (ports : TrueDualPort policyA policyB δ addressWidth α)
    (readEnableA : Expr 1) (readAddressA : Expr addressWidth)
    (writeEnableA : Expr 1) (writeAddressA : Expr addressWidth)
    (writeDataA : PackedExpr α) (writeLanesA : Expr ports.layout.lanes)
    (readEnableB : Expr 1) (readAddressB : Expr addressWidth)
    (writeEnableB : Expr 1) (writeAddressB : Expr addressWidth)
    (writeDataB : PackedExpr α) (writeLanesB : Expr ports.layout.lanes) : Act :=
  .seq
    (ports.portA.cycle readEnableA readAddressA writeEnableA writeAddressA
      writeDataA writeLanesA)
    (ports.portB.cycle readEnableB readAddressB writeEnableB writeAddressB
      writeDataB writeLanesB)

end TrueDualPort

/-- A bank-level declaration records the semantic policies that all current
ports share. The constructors are deliberately singletons until Loom gains
additional proved core behaviors. -/
structure Bank (δ : Type v) (addressWidth : Nat) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  memory : Mem addressWidth (HwPacked.width α)
  writes : List (WritePort δ addressWidth α)
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

/-! ## Exact mixed-width views -/

/-- A narrow port partitions each storage word into a power-of-two number of
equal subwords. The proof fields are the address-mapping authority; no backend
may invent a different lane order. Subword zero is least-significant. -/
structure MixedWidthLayout (storageWidth portWidth : Nat) where
  ratio : Nat
  selectorBits : Nat
  ratioPositive : 0 < ratio
  portWidthPositive : 0 < portWidth
  complete : ratio * portWidth = storageWidth
  powerOfTwo : 2 ^ selectorBits = ratio
  deriving Repr

namespace MixedWidthLayout

def checked (storageWidth portWidth : Nat) :
    Except String (MixedWidthLayout storageWidth portWidth) := do
  if portPositive : 0 < portWidth then
    if storagePositive : 0 < storageWidth then
      if divides : storageWidth % portWidth = 0 then
        let ratio := storageWidth / portWidth
        let selectorBits := Nat.log2 ratio
        if power : 2 ^ selectorBits = ratio then
          have complete : ratio * portWidth = storageWidth := by
            rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero divides)]
          have ratioPositive : 0 < ratio := by
            by_contra notPositive
            have ratioZero : ratio = 0 := Nat.eq_zero_of_not_pos notPositive
            rw [ratioZero] at complete
            simp at complete
            omega
          return ⟨ratio, selectorBits, ratioPositive, portPositive,
            complete, power⟩
        else
          throw s!"mixed-width ratio {ratio} is not a power of two"
      else
        throw s!"storage width {storageWidth} is not divisible by port width {portWidth}"
    else throw "mixed-width storage width must be positive"
  else throw "mixed-width port width must be positive"

private def storageAddress {storageAddressWidth storageWidth portWidth : Nat}
    (layout : MixedWidthLayout storageWidth portWidth)
    (address : Expr (storageAddressWidth + layout.selectorBits)) :
    Expr storageAddressWidth :=
  .slice address layout.selectorBits storageAddressWidth

private def selector {storageAddressWidth storageWidth portWidth : Nat}
    (layout : MixedWidthLayout storageWidth portWidth)
    (address : Expr (storageAddressWidth + layout.selectorBits)) :
    Expr layout.selectorBits :=
  .slice address 0 layout.selectorBits

private def subwordField {storageWidth portWidth : Nat}
    (layout : MixedWidthLayout storageWidth portWidth)
    (index : Fin layout.ratio) : PackedField (BitVec storageWidth) portWidth where
  name := s!"subword{index.val}"
  lo := index.val * portWidth
  inBounds := by
    change index.val * portWidth + portWidth ≤ storageWidth
    have below : index.val + 1 ≤ layout.ratio :=
      Nat.succ_le_iff.mpr index.isLt
    have scaled := Nat.mul_le_mul_right portWidth below
    rw [layout.complete] at scaled
    simpa [Nat.add_mul] using scaled

/-- Read one narrow subword through a finite selector mux. Every underlying
slice is static and carries its own bound proof. -/
def read {storageAddressWidth storageWidth portWidth : Nat}
    (layout : MixedWidthLayout storageWidth portWidth)
    (memory : Mem storageAddressWidth storageWidth)
    (address : Expr (storageAddressWidth + layout.selectorBits)) : Expr portWidth :=
  let full : PackedExpr (BitVec storageWidth) :=
    ⟨memory.rd (layout.storageAddress address)⟩
  (List.finRange layout.ratio).foldr (fun index fallback =>
    .mux (.eq (layout.selector address)
      (.lit (BitVec.ofNat layout.selectorBits index.val)))
      ((layout.subwordField index).read full) fallback) (.lit 0)

/-- Replace one selected narrow subword and preserve every other bit. -/
def replace {storageAddressWidth storageWidth portWidth : Nat}
    (layout : MixedWidthLayout storageWidth portWidth)
    (address : Expr (storageAddressWidth + layout.selectorBits))
    (current : Expr storageWidth) (next : Expr portWidth) : Expr storageWidth :=
  let full : PackedExpr (BitVec storageWidth) := ⟨current⟩
  (List.finRange layout.ratio).foldr (fun index fallback =>
    .mux (.eq (layout.selector address)
      (.lit (BitVec.ofNat layout.selectorBits index.val)))
      (full.setField (layout.subwordField index) next).bits fallback) current

end MixedWidthLayout

/-- A full-write narrow view of a wider neutral memory. Address width grows by
the statically proved selector width; payload nominal type remains exact. -/
structure MixedWidthPort (δ : Type v) (storageAddressWidth : Nat)
    (Storage PortValue : Type u)
    [ClockDomain δ] [HwPacked Storage] [HwPacked PortValue] where
  memory : Mem storageAddressWidth (HwPacked.width Storage)
  index : Nat
  layout : MixedWidthLayout (HwPacked.width Storage) (HwPacked.width PortValue)

namespace MixedWidthPort

def read {δ : Type v} {storageAddressWidth : Nat}
    {Storage PortValue : Type u}
    [ClockDomain δ] [HwPacked Storage] [HwPacked PortValue]
    (port : MixedWidthPort δ storageAddressWidth Storage PortValue)
    (address : Expr (storageAddressWidth + port.layout.selectorBits)) :
    PackedExpr PortValue :=
  ⟨port.layout.read port.memory address⟩

def write {δ : Type v} {storageAddressWidth : Nat}
    {Storage PortValue : Type u}
    [ClockDomain δ] [HwPacked Storage] [HwPacked PortValue]
    (port : MixedWidthPort δ storageAddressWidth Storage PortValue)
    (address : Expr (storageAddressWidth + port.layout.selectorBits))
    (value : PackedExpr PortValue) : Act :=
  let storageAddress := port.layout.storageAddress address
  port.memory.write port.index storageAddress
    (port.layout.replace address (port.memory.rd storageAddress) value.bits)

end MixedWidthPort

end MemoryPort

end Loom.Hw
