-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Packed
import Loom.Hw.Compile
import Loom.Hw.FastEval
import Loom.Hw.DagEval
import Loom.Hw.RecoveryProtocol
import Loom.Hw.Multiclock

/-!
# Packed-value and partial-write regressions

These tests pin the core semantics independently of optional pretty syntax:
packed wrappers erase to scalar Loom objects, field writes compose through the
ordered accumulator, and all RHS expressions still read the pre-cycle state.
-/

namespace Tests.Packed

open Loom.Hw

/-- A genuine semantic record. Software manipulates named fields while its
canonical hardware representation places the first field in the MSBs. -/
structure Packet where
  tag : BitVec 3
  address : BitVec 5
  deriving DecidableEq, Repr

instance : HwPacked Packet where
  width := 8
  pack := fun packet => packet.tag ++ packet.address
  unpack := fun bits =>
    { tag := bits.extractLsb' 5 3
      address := bits.extractLsb' 0 5 }
  unpack_pack := by
    intro value
    cases value
    rw [BitVec.extractLsb'_append_eq_left,
      BitVec.extractLsb'_append_eq_right]
  pack_unpack := by
    intro bits
    exact BitVec.extractLsb'_append_extractLsb'

def packetValue (bits : BitVec 8) : Packet := HwPacked.unpack bits

structure OtherPacket where
  bits : BitVec 8
  deriving DecidableEq, Repr

instance : HwPacked OtherPacket where
  width := 8
  pack := OtherPacket.bits
  unpack := OtherPacket.mk
  unpack_pack := by intro value; cases value; rfl
  pack_unpack := by intro bits; rfl

def packetLayout : PackedLayout Packet where
  fields :=
    [ { name := "tag", width := 3, lo := 5 }
    , { name := "address", width := 5, lo := 0 } ]
  namesUnique := by decide
  inBounds := by
    intro field member
    simp at member
    rcases member with rfl | rfl <;> decide
  disjoint := by decide
  complete := by decide
  msbFirst := by
    intro index inRange
    simp at inRange
    have : index = 0 ∨ index = 1 := by omega
    rcases this with rfl | rfl <;> simp

instance : HwPackedLayout Packet := ⟨packetLayout⟩

def packet : PackedReg Packet := .named "packet"
def packetIn : PackedInput Packet := .named "packet_in"
def packetMem : PackedMem 4 Packet := .named "packet_mem"
def packetChan : PackedChan Packet := .named "packet_chan" 2
def packetSource := packetChan.source
def packetSink := packetChan.sink

/-- Structured channel values use the exact scalar recovery proof through
their canonical packer; there is no field-wise CDC or reset representation. -/
def packetRecovery : Chan.RecoveryRefinement packetChan.bits :=
  Chan.RecoveryProtocol.refinement packetChan.bits

def packedRecoveryValue : Packet := ⟨5#3, 17#5⟩

def packetRecoveryRequests : List packetRecovery.Request :=
  [{ sourceTick := true,
      transfer := { push := some (HwPacked.pack packedRecoveryValue) } },
    { sourceTick := true, sinkTick := true, sourceRecover := true }] ++
    List.replicate 24 { sourceTick := true, sinkTick := true }

def packetRecoveryAbstract :
    Chan.RecoveryRefinement.AbstractTraceResult (HwPacked.width Packet) :=
  Chan.RecoveryRefinement.runAbstract packetChan.bits []
    (packetRecovery.observedEvents packetRecovery.reset packetRecoveryRequests)

example : packetRecoveryAbstract.discarded =
    [[HwPacked.pack packedRecoveryValue]] := by native_decide
example : (packetRecoveryAbstract.discarded.map fun epoch =>
    epoch.map (HwPacked.unpack (α := Packet))) = [[packedRecoveryValue]] := by
  native_decide

/-! Packed payload types survive System topology, independent-reset
realization, hierarchy, and emission. The implementation still sees the one
canonical eight-bit representation. -/

def packetClockA : ClockHandle := .named "packet_clk_a"
def packetClockB : ClockHandle := .named "packet_clk_b"
def packetProducerDesign : Design :=
  Design.ofDecls "packet_producer" Declarations.empty []
def packetConsumerDesign : Design :=
  Design.ofDecls "packet_consumer" Declarations.empty []
def packetProducerIsland : IslandHandle :=
  .named "packet_producer" packetProducerDesign packetClockA
def packetConsumerIsland : IslandHandle :=
  .named "packet_consumer" packetConsumerDesign packetClockB
def packetRoute :=
  packetChan.between packetProducerIsland packetConsumerIsland
def packetSystemBuilder : SystemBuilder :=
  System.empty
    |>.addErasedIsland packetProducerIsland
    |>.addErasedIsland packetConsumerIsland
    |>.addChannel packetRoute
    |>.withClockRel .asynchronous
    |>.withIndependentReset
def packetSystem : System := packetSystemBuilder.certify (by decide)
def packetApplication : System.Application packetSystem :=
  packetSystem.realizeWith RealizationPlan.recoveryPortable (by native_decide)

example : packetApplication.artifact.emissionCheck.isOk := by native_decide
example : packetApplication.artifact.renderedVerilog.contains
    "input wire [7:0] src_payload" := by native_decide
example : packetApplication.artifact.renderedVerilog.contains
    "system_recovery_coordinator_cell" := by native_decide

def packetExportSource := packetChan.exportSource packetProducerIsland
def packetExportSink := packetChan.exportSink packetConsumerIsland
example : (System.empty
    |>.addErasedIsland packetProducerIsland
    |>.addErasedIsland packetConsumerIsland
    |>.exportPackedSource packetExportSource
    |>.exportPackedSink packetExportSink
    |>.connectPackedExports packetExportSource packetExportSink).check.isOk := by
  native_decide

def otherPacketChan : PackedChan OtherPacket := .named "packet_chan" 2
def otherPacketExportSink :=
  otherPacketChan.exportSink packetConsumerIsland
#check_failure System.empty.connectPackedExports packetExportSource
  otherPacketExportSink

/-- First declared field is the MSB field. -/
def tag : PackedField Packet 3 :=
  HwPackedLayout.fieldAt (α := Packet) ⟨0, by decide⟩
/-- Last declared field is the LSB field. -/
def address : PackedField Packet 5 :=
  HwPackedLayout.fieldAt (α := Packet) ⟨1, by decide⟩
def tagMember : PackedMember Packet 3 where
  field := tag
  project := Packet.tag
  project_eq_get := by
    intro value
    cases value
    exact BitVec.extractLsb'_append_eq_left.symm
def addressMember : PackedMember Packet 5 where
  field := address
  project := Packet.address
  project_eq_get := by
    intro value
    cases value
    exact BitVec.extractLsb'_append_eq_right.symm
def lowNibble : PackedField Packet 4 := ⟨"low", 0, by change 0 + 4 ≤ 8; omega⟩
def middleNibble : PackedField Packet 4 := ⟨"middle", 2, by change 2 + 4 ≤ 8; omega⟩
def lowPair : PackedField Packet 2 := ⟨"lowPair", 0, by change 0 + 2 ≤ 8; omega⟩

private def stateWith (value : Nat) : St where
  regs := fun name width =>
    if name = packet.name then BitVec.ofNat width value else 0#width
  mems := fun _ _ width => 0#width

private def bitsAfter (action : Act) (initial : Nat := 0) : BitVec 8 :=
  (action.run (stateWith initial) (stateWith initial)).regs packet.name 8

example : HwPacked.unpack (HwPacked.pack (Packet.mk 5#3 5#5)) =
    Packet.mk 5#3 5#5 := by
  rfl
example : packet.rd.bits = Expr.reg 8 "packet" := rfl
example : packetIn.rd.bits = Expr.reg 8 "packet_in" := rfl
example : (packet.decl (Packet.mk 5#3 17#5)).init = 0xB1#8 := rfl
example : tag.read packet.rd = Expr.slice packet.rd.bits 5 3 := rfl
example (value : Packet) : tag.get value = value.tag := by
  exact tagMember.get_eq_project value
example (value : Packet) : address.get value = value.address := by
  exact addressMember.get_eq_project value
example : HwPackedLayout.findIndex? (α := Packet) "address" = some 1 := rfl
example : (packetMem.rd (.lit 0#4)).bits =
    Expr.memRead 8 "packet_mem" (.lit 0#4) := rfl
example : (packetMem.decl (fun _ => Packet.mk 5#3 17#5)).init 7 =
    0xB1#8 := rfl
example : Chan 8 := packetChan.bits
example : packetChan.enqValue (Packet.mk 5#3 17#5) =
    packetChan.bits.enq (.lit 0xB1#8) := rfl
example : packetChan.deq.bits = packetChan.bits.deq := rfl

/- Equal representation width does not make distinct semantic packed types
assignment-compatible, and packed records do not acquire implicit arithmetic. -/
#check_failure (packet.rd : PackedExpr OtherPacket)
#check_failure Expr.add packet.rd packet.rd
#check_failure packetSource.send (PackedExpr.ofValue (OtherPacket.mk 0xA5#8))
example : PackedExpr Packet := packetSink.data

def declarations : Declarations :=
  Declarations.empty
    |>.addPackedReg packet (packetValue 0#8) (exported := true)
    |>.addPackedInput packetIn
    |>.addPackedMem packetMem (fun _ => packetValue 0#8)
    |>.addPackedOutput ⟨"packet_view", packet.rd⟩

example : declarations.regs.map (fun reg => (reg.name, reg.width)) =
    [("packet", 8)] := by decide
example : declarations.inputs.map (fun input => (input.name, input.width)) =
    [("packet_in", 8)] := by decide
example : declarations.mems.map (fun mem =>
    (mem.name, mem.addrWidth, mem.dataWidth)) = [("packet_mem", 4, 8)] := by
  decide

def assembled : PackedExpr Packet :=
  .ofFields (.cons (.lit 5#3) (.cons (.lit 17#5) .nil))

#guard assembled.eval (stateWith 0) == packetValue 0xB1#8
#guard (PackedExpr.eq assembled
  (PackedExpr.fromBits (Expr.lit 0xB1#8))).eval (stateWith 0) == 1#1
example : (PackedExpr.fromBits (α := Packet) (.lit 0xB1#8)).bits =
    Expr.lit 0xB1#8 := rfl
#guard (packet.rd.setField tag (.lit 5#3)).eval (stateWith 0x11) ==
  packetValue 0xB1#8
#guard
  match PackedField.checked (α := Packet) "tag" 5 3 with
  | .ok field => field.lo == 5
  | .error _ => false
#guard
  match PackedField.checked (α := Packet) "bad" 7 2 with
  | .ok _ => false
  | .error message => message.contains "exceeds"

example :
    (InputBinding.toEnv [packetIn.bind (packetValue 0xA5#8)]) "packet_in" 8 =
      0xA5#8 := by
  native_decide

example :
    (PackedOutput.evalState ⟨"packet_view", assembled⟩ (stateWith 0)) =
      packetValue 0xB1#8 := by
  native_decide

/-! Disjoint writes survive and declaration-order field placement is exact. -/
def disjointWrites : Act :=
  .seq (packet.setMember tagMember (.lit 5#3))
    (packet.setMember addressMember (.lit 17#5))

#guard bitsAfter disjointWrites == 0xB1#8

/-! Overlapping writes are ordered, with the later field winning. -/
def overlappingWrites : Act :=
  .seq (packet.setField lowNibble (.lit 0xF#4))
    (packet.setField middleNibble (.lit 0#4))

#guard bitsAfter overlappingWrites == 0x03#8

/-! Whole/slice ordering uses the same accumulator. -/
#guard bitsAfter
  (.seq (packet.setValue (packetValue 0xAA#8))
    (packet.setField lowPair (.lit 3#2))) == 0xAB#8
#guard bitsAfter
  (.seq (packet.setField lowPair (.lit 3#2))
    (packet.setValue (packetValue 0xAA#8))) == 0xAA#8

/-! The RHS reads pre-cycle state even after an earlier whole write. Initial
low bits are `01`; a sequential interpretation would have read zero instead. -/
def preCycleRead : Act :=
  .seq (packet.setValue (packetValue 0#8))
    (packet.setField lowPair (.slice packet.rd.bits 0 2))

#guard bitsAfter preCycleRead 0xA5 == 0x01#8

def design : Design where
  name := "packed_test"
  regs := [packet.decl (packetValue 0#8)]
  mems := []
  rules := [⟨"update", disjointWrites⟩]
  outputs := [packet.name]

private def designFor (action : Act) (initial : BitVec 8) : Design where
  name := "packed_evaluator_test"
  regs := [packet.bits.decl initial]
  mems := []
  rules := [⟨"update", action⟩]
  outputs := [packet.name]

private def evaluatorsAgree (action : Act) (initial : BitVec 8) : Bool :=
  let candidate := designFor action initial
  let source := candidate.cycle candidate.reset
  let expected := (source.regs packet.name 8).toNat
  let fast := fastCycle candidate.elaborate candidate.fastReset
  let dag := DagEval.cycle (DagEval.lower candidate.elaborate)
    candidate.fastReset
  fast.regs.getD 0 0 == expected && dag.regs.getD 0 0 == expected

#guard evaluatorsAgree overlappingWrites 0#8
#guard evaluatorsAgree
  (.seq (packet.setValue (packetValue 0xAA#8))
    (packet.setField lowPair (.lit 3#2))) 0#8
#guard evaluatorsAgree preCycleRead 0xA5#8

example :
    (PackedOutput.evalOpen ⟨"packet_view", packetIn.rd⟩
      { design with inputs := [packetIn.decl] }
      (InputBinding.toEnv [packetIn.bind (packetValue 0xA5#8)]) design.reset) =
      packetValue 0xA5#8 := by
  native_decide

/-! Reference compilation and both optimized evaluators agree on the packed
partial-write design. -/
#guard
  let source := design.cycle design.reset
  let fast := fastCycle design.elaborate design.fastReset
  fast.regs.getD 0 0 == (source.regs packet.name 8).toNat

#guard
  let source := design.cycle design.reset
  let dagDesign := DagEval.lower design.elaborate
  let dag := DagEval.cycle dagDesign design.fastReset
  dag.regs.getD 0 0 == (source.regs packet.name 8).toNat

example :
    Compile.mvEval (Compile.convSt design.reset)
      (Compile.nextReg packet.name 8 disjointWrites (.reg 8 packet.name)) =
      (disjointWrites.run design.reset design.reset).regs packet.name 8 := by
  apply Compile.nextReg_correct
  rfl

end Tests.Packed
