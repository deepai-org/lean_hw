-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.AsyncQueueStorageDesign
import Loom.Hw.AsyncFifo
import Loom.Hw.Declarations
import Loom.Hw.GrayCode

/-!
# Compiler-facing asynchronous FIFO control islands

The two values in this file are ordinary single-clock `Design`s. Every
pointer register, Gray increment, two-stage synchronizer, and full/empty
predicate
comparison is therefore handled by Loom's existing proved compiler and
certified DAG evaluator. They mention no FPGA primitive, ASIC macro, synthesis
tool, or clock ratio.

Only combinational port plumbing is left to the structural System layer:
`writeTake = sourceValid && !fullNow`, `readTake = sinkPop && !emptyNow`, address
slices, and payload wiring to an `AsyncQueueStorage` leaf. Keeping those
signals combinational is correctness-critical: registering a storage command
would allow a pointer publication to outrun the corresponding data write.
-/

namespace Loom.Hw.Cdc.AsyncFifoDesign

open Loom.Hw

/-- A power-of-two queue shape supported by the stock Gray controller. -/
structure Parameters where
  width : Nat
  depth : Nat
  depthAtLeastTwo : 2 ≤ depth
  powerOfTwo : 2 ^ Nat.log2 depth = depth

def addressWidth (p : Parameters) : Nat := Nat.log2 p.depth
def pointerWidth (p : Parameters) : Nat := addressWidth p + 1

def sourceValid : Reg 1 := ⟨"source_valid"⟩
def sourcePayload (p : Parameters) : Reg p.width := ⟨"source_payload"⟩
def rawReadGray (p : Parameters) : Reg (pointerWidth p) := ⟨"raw_read_gray"⟩
def sinkPop : Reg 1 := ⟨"sink_pop"⟩
def rawWriteGray (p : Parameters) : Reg (pointerWidth p) := ⟨"raw_write_gray"⟩

def writeBinary (p : Parameters) : Reg (pointerWidth p) := ⟨"write_binary"⟩
def writeGray (p : Parameters) : Reg (pointerWidth p) := ⟨"write_gray"⟩
def readGraySync0 (p : Parameters) : Reg (pointerWidth p) := ⟨"read_gray_sync0"⟩
def readGraySync1 (p : Parameters) : Reg (pointerWidth p) := ⟨"read_gray_sync1"⟩

def readBinary (p : Parameters) : Reg (pointerWidth p) := ⟨"read_binary"⟩
def readGray (p : Parameters) : Reg (pointerWidth p) := ⟨"read_gray"⟩
def writeGraySync0 (p : Parameters) : Reg (pointerWidth p) := ⟨"write_gray_sync0"⟩
def writeGraySync1 (p : Parameters) : Reg (pointerWidth p) := ⟨"write_gray_sync1"⟩

/-- Binary-to-Gray at the exact finite hardware width. -/
def toGray {width : Nat} (binary : Expr width) : Expr width :=
  .xor binary (.shr binary (.lit (BitVec.ofNat width 1)))

/-- Prefix-XOR Gray decoder. Only a synchronized Gray word is decoded; raw
binary pointer bits never cross a clock boundary. -/
def fromGrayPrefix {width : Nat} (gray : Expr width) : Nat → Expr width
  | 0 => gray
  | steps + 1 =>
      .xor (fromGrayPrefix gray steps)
        (.shr gray (.lit (BitVec.ofNat width (steps + 1))))

def fromGray {width : Nat} (gray : Expr width) : Expr width :=
  fromGrayPrefix gray (width - 1)

/-- The finite-width expression decoder implements the arithmetic prefix
decoder. -/
theorem fromGrayPrefix_eval_toNat {width : Nat} (gray : Expr width)
    (steps : Nat) (within : steps < width) (state : St) :
    ((fromGrayPrefix gray steps).eval state).toNat =
      Gray.decodePrefix ((gray.eval state).toNat) steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have previousWithin : steps < width := lt_trans (Nat.lt_succ_self _) within
      have shiftBound : steps + 1 < 2 ^ width := by
        have widthLt : width < 2 ^ width := Nat.lt_two_pow_self
        omega
      simp [fromGrayPrefix, Expr.eval, ih previousWithin, BitVec.toNat_xor,
        BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt shiftBound, Gray.decodePrefix]

theorem fromGrayPrefix_eval_congr {width : Nat} (left right : Expr width)
    (steps : Nat) (state : St) (equal : left.eval state = right.eval state) :
    (fromGrayPrefix left steps).eval state =
      (fromGrayPrefix right steps).eval state := by
  induction steps with
  | zero => exact equal
  | succ steps ih =>
      simp only [fromGrayPrefix, Expr.eval]
      rw [ih, equal]

theorem fromGray_eval_congr {width : Nat} (left right : Expr width)
    (state : St) (equal : left.eval state = right.eval state) :
    (fromGray left).eval state = (fromGray right).eval state := by
  exact fromGrayPrefix_eval_congr left right (width - 1) state equal

/-- Technology-neutral full comparison target. The synchronized Gray pointer
is decoded *after* its two destination-domain stages; no raw binary bus
crosses the boundary. Adding one depth in the finite pointer ring identifies
the full generation. -/
def fullTarget (p : Parameters) : Expr (pointerWidth p) :=
  .add (fromGray (readGraySync1 p).rd)
    (.lit (BitVec.ofNat (pointerWidth p) p.depth))

def fullNow (p : Parameters) : Expr 1 :=
  .eq (writeBinary p).rd (fullTarget p)

def emptyNow (p : Parameters) : Expr 1 :=
  .eq (readBinary p).rd (fromGray (writeGraySync1 p).rd)

def writeTake (p : Parameters) : Expr 1 :=
  .and sourceValid.rd (.not (fullNow p))

def readTake (p : Parameters) : Expr 1 :=
  .and sinkPop.rd (.not (emptyNow p))

def writeAddressView (p : Parameters) : Expr (addressWidth p) :=
  .slice (writeBinary p).rd 0 (addressWidth p)

def readAddressView (p : Parameters) : Expr (addressWidth p) :=
  .slice (readBinary p).rd 0 (addressWidth p)

def nextWriteBinary (p : Parameters) : Expr (pointerWidth p) :=
  .add (writeBinary p).rd (.zext (writeTake p) (pointerWidth p))

def nextReadBinary (p : Parameters) : Expr (pointerWidth p) :=
  .add (readBinary p).rd (.zext (readTake p) (pointerWidth p))

def nextWriteGray (p : Parameters) : Expr (pointerWidth p) :=
  toGray (nextWriteBinary p)

def nextReadGray (p : Parameters) : Expr (pointerWidth p) :=
  toGray (nextReadBinary p)

/-- Write-clock control island. The synchronizer registers are explicitly
named so physical evidence can attach placement/preservation intent without
changing the generic semantics or selecting a vendor attribute syntax. -/
def sourceControl (p : Parameters) : Design where
  name := s!"async_fifo_source_control_w{p.width}_d{p.depth}"
  regs := [(writeBinary p).decl, (writeGray p).decl,
    (readGraySync0 p).decl, (readGraySync1 p).decl]
  mems := []
  rules := [
    ⟨"synchronize_read_pointer", .seq
      ((readGraySync0 p).set (rawReadGray p).rd)
      ((readGraySync1 p).set (readGraySync0 p).rd)⟩,
    ⟨"advance_write_pointer", .seq
      ((writeBinary p).set (nextWriteBinary p))
      ((writeGray p).set (nextWriteGray p))⟩]
  inputs := [sourceValid.input, (sourcePayload p).input, (rawReadGray p).input]
  outputs := [(writeBinary p).name, (writeGray p).name,
    (readGraySync0 p).name, (readGraySync1 p).name]
  combOutputs := [
    ⟨"source_ready", 1, .not (fullNow p)⟩,
    ⟨"write_take", 1, writeTake p⟩,
    ⟨"write_address", addressWidth p, writeAddressView p⟩,
    ⟨"write_data", p.width, (sourcePayload p).rd⟩]

/-- Read-clock control island, symmetric with `sourceControl`. -/
def sinkControl (p : Parameters) : Design where
  name := s!"async_fifo_sink_control_w{p.width}_d{p.depth}"
  regs := [(readBinary p).decl, (readGray p).decl,
    (writeGraySync0 p).decl, (writeGraySync1 p).decl]
  mems := []
  rules := [
    ⟨"synchronize_write_pointer", .seq
      ((writeGraySync0 p).set (rawWriteGray p).rd)
      ((writeGraySync1 p).set (writeGraySync0 p).rd)⟩,
    ⟨"advance_read_pointer", .seq
      ((readBinary p).set (nextReadBinary p))
      ((readGray p).set (nextReadGray p))⟩]
  inputs := [sinkPop.input, (rawWriteGray p).input]
  outputs := [(readBinary p).name, (readGray p).name,
    (writeGraySync0 p).name, (writeGraySync1 p).name]
  combOutputs := [
    ⟨"sink_valid", 1, .not (emptyNow p)⟩,
    ⟨"read_take", 1, readTake p⟩,
    ⟨"read_address", addressWidth p, readAddressView p⟩]

/-! ## Source-semantic equations

These equations expose the ordinary `Design.cycleOpen` semantics consumed by
the later FIFO refinement. Compiler correctness transports them unchanged to
the emitted module; they are not a second executable model. -/

theorem source_writeBinary_cycle (p : Parameters) (input : InEnv) (state : St) :
    ((sourceControl p).cycleOpen input state).regs
        (writeBinary p).name (pointerWidth p) =
      (nextWriteBinary p).eval
        (state.setInputs (sourceControl p).inputs input) := by
  simp [Design.cycleOpen, Design.cycle, sourceControl, Act.run, Reg.set, RegEnv.set,
    writeBinary, writeGray, readGraySync0, readGraySync1]

theorem source_writeGray_cycle (p : Parameters) (input : InEnv) (state : St) :
    ((sourceControl p).cycleOpen input state).regs
        (writeGray p).name (pointerWidth p) =
      (nextWriteGray p).eval
        (state.setInputs (sourceControl p).inputs input) := by
  simp [Design.cycleOpen, Design.cycle, sourceControl, Act.run, Reg.set, RegEnv.set,
    writeBinary, writeGray, readGraySync0, readGraySync1]

theorem source_sync_cycle (p : Parameters) (input : InEnv) (state : St) :
    ((sourceControl p).cycleOpen input state).regs
        (readGraySync1 p).name (pointerWidth p) =
      state.regs (readGraySync0 p).name (pointerWidth p) := by
  simp [Design.cycleOpen, Design.cycle, sourceControl, Act.run, Reg.set, Reg.rd, RegEnv.set,
    St.setInputs, rawReadGray, readGraySync0, readGraySync1, sourceValid,
    sourcePayload, writeBinary, writeGray]
  exact state.setInputs_regs_notin (sourceControl p).inputs input
    (readGraySync0 p).name (pointerWidth p) (by
      intro declared member equal
      have names := congrArg Prod.fst equal
      simp [sourceControl, Reg.input, sourceValid, sourcePayload, rawReadGray] at member
      rcases member with rfl | rfl | rfl <;>
        simp [readGraySync0] at names)

theorem source_sync0_cycle (p : Parameters) (input : InEnv) (state : St) :
    ((sourceControl p).cycleOpen input state).regs
        (readGraySync0 p).name (pointerWidth p) =
      input (rawReadGray p).name (pointerWidth p) := by
  simp [Design.cycleOpen, Design.cycle, sourceControl, Act.run, Reg.set, Reg.rd,
    RegEnv.set, St.setInputs, rawReadGray, readGraySync0, readGraySync1,
    sourceValid, sourcePayload, writeBinary, writeGray, Reg.input]
  simp only [Expr.eval]
  simp [RegEnv.set]

theorem sink_readBinary_cycle (p : Parameters) (input : InEnv) (state : St) :
    ((sinkControl p).cycleOpen input state).regs
        (readBinary p).name (pointerWidth p) =
      (nextReadBinary p).eval
        (state.setInputs (sinkControl p).inputs input) := by
  simp [Design.cycleOpen, Design.cycle, sinkControl, Act.run, Reg.set, RegEnv.set,
    readBinary, readGray, writeGraySync0, writeGraySync1]

theorem sink_readGray_cycle (p : Parameters) (input : InEnv) (state : St) :
    ((sinkControl p).cycleOpen input state).regs
        (readGray p).name (pointerWidth p) =
      (nextReadGray p).eval
        (state.setInputs (sinkControl p).inputs input) := by
  simp [Design.cycleOpen, Design.cycle, sinkControl, Act.run, Reg.set, RegEnv.set,
    readBinary, readGray, writeGraySync0, writeGraySync1]

theorem sink_sync_cycle (p : Parameters) (input : InEnv) (state : St) :
    ((sinkControl p).cycleOpen input state).regs
        (writeGraySync1 p).name (pointerWidth p) =
      state.regs (writeGraySync0 p).name (pointerWidth p) := by
  simp [Design.cycleOpen, Design.cycle, sinkControl, Act.run, Reg.set, Reg.rd, RegEnv.set,
    St.setInputs, rawWriteGray, writeGraySync0, writeGraySync1, sinkPop,
    readBinary, readGray]
  exact state.setInputs_regs_notin (sinkControl p).inputs input
    (writeGraySync0 p).name (pointerWidth p) (by
      intro declared member equal
      have names := congrArg Prod.fst equal
      simp [sinkControl, Reg.input, sinkPop, rawWriteGray] at member
      rcases member with rfl | rfl <;>
        simp [writeGraySync0] at names)

theorem sink_sync0_cycle (p : Parameters) (input : InEnv) (state : St) :
    ((sinkControl p).cycleOpen input state).regs
        (writeGraySync0 p).name (pointerWidth p) =
      input (rawWriteGray p).name (pointerWidth p) := by
  simp [Design.cycleOpen, Design.cycle, sinkControl, Act.run, Reg.set, Reg.rd,
    RegEnv.set, St.setInputs, rawWriteGray, writeGraySync0, writeGraySync1,
    sinkPop, readBinary, readGray, Reg.input]
  simp only [Expr.eval]
  simp [RegEnv.set]

structure Controls (p : Parameters) where
  source : CertifiedDesign (sourceControl p)
  sink : CertifiedDesign (sinkControl p)

def certify (p : Parameters)
    (sourceCompiler : Compile.designWFCheck (sourceControl p) = true)
    (sourceFast : (sourceControl p).fastWFB = true)
    (sinkCompiler : Compile.designWFCheck (sinkControl p) = true)
    (sinkFast : (sinkControl p).fastWFB = true) : Controls p where
  source := .ofChecks sourceCompiler sourceFast
  sink := .ofChecks sinkCompiler sinkFast

/-- Names requiring synchronizer implementation intent. The list is neutral
metadata; ASYNC_REG/DONT_TOUCH attributes or ASIC synchronizer-cell selection
are evidence/backend decisions. -/
def synchronizerRegisters (p : Parameters) : List (String × List String) :=
  [((sourceControl p).name, [(readGraySync0 p).name, (readGraySync1 p).name]),
   ((sinkControl p).name, [(writeGraySync0 p).name, (writeGraySync1 p).name])]

def sourceDrive (p : Parameters) (push : Option (BitVec p.width))
    (remoteGray : BitVec (pointerWidth p)) : InEnv :=
  fun name width =>
    if name = sourceValid.name then
      if h : width = 1 then h.symm ▸ (if push.isSome then 1#1 else 0#1) else 0
    else if name = (sourcePayload p).name then
      if h : width = p.width then h.symm ▸ push.getD 0 else 0
    else if name = (rawReadGray p).name then
      if h : width = pointerWidth p then h.symm ▸ remoteGray else 0
    else 0

def sinkDrive (p : Parameters) (pop : Bool)
    (remoteGray : BitVec (pointerWidth p)) : InEnv :=
  fun name width =>
    if name = sinkPop.name then
      if h : width = 1 then h.symm ▸ (if pop then 1#1 else 0#1) else 0
    else if name = (rawWriteGray p).name then
      if h : width = pointerWidth p then h.symm ▸ remoteGray else 0
    else 0

theorem sourceDrive_valid (p : Parameters) (push : Option (BitVec p.width))
    (remoteGray : BitVec (pointerWidth p)) :
    sourceDrive p push remoteGray sourceValid.name 1 =
      if push.isSome then 1#1 else 0#1 := by
  simp [sourceDrive, sourceValid]

theorem sourceDrive_payload (p : Parameters) (push : Option (BitVec p.width))
    (remoteGray : BitVec (pointerWidth p)) :
    sourceDrive p push remoteGray (sourcePayload p).name p.width = push.getD 0 := by
  simp [sourceDrive, sourceValid, sourcePayload]

theorem sourceDrive_remote (p : Parameters) (push : Option (BitVec p.width))
    (remoteGray : BitVec (pointerWidth p)) :
    sourceDrive p push remoteGray (rawReadGray p).name (pointerWidth p) = remoteGray := by
  simp [sourceDrive, sourceValid, sourcePayload, rawReadGray]

theorem sinkDrive_pop (p : Parameters) (pop : Bool)
    (remoteGray : BitVec (pointerWidth p)) :
    sinkDrive p pop remoteGray sinkPop.name 1 = if pop then 1#1 else 0#1 := by
  simp [sinkDrive, sinkPop]

theorem sinkDrive_remote (p : Parameters) (pop : Bool)
    (remoteGray : BitVec (pointerWidth p)) :
    sinkDrive p pop remoteGray (rawWriteGray p).name (pointerWidth p) = remoteGray := by
  simp [sinkDrive, sinkPop, rawWriteGray]

/-! ## Relation to the schedule-level FIFO model -/

def pointerWord (p : Parameters) (count : Nat) : BitVec (pointerWidth p) :=
  BitVec.ofNat (pointerWidth p) count

def grayWord (p : Parameters) (count : Nat) : BitVec (pointerWidth p) :=
  BitVec.ofNat (pointerWidth p)
    (Gray.encode (count % 2 ^ pointerWidth p))

private theorem mod_ne_of_ordered_distance {left right modulus : Nat}
    (ordered : left ≤ right) (different : left ≠ right)
    (distance : right - left < modulus) : left % modulus ≠ right % modulus := by
  intro equalMod
  have congruent : Nat.ModEq modulus left right := equalMod
  have divides : modulus ∣ right - left :=
    (Nat.modEq_iff_dvd' ordered).mp congruent
  have positive : 0 < right - left :=
    Nat.sub_pos_of_lt (lt_of_le_of_ne ordered different)
  have modulusLe : modulus ≤ right - left := Nat.le_of_dvd positive divides
  omega

theorem pointerRing_eq (p : Parameters) :
    2 ^ pointerWidth p = 2 * p.depth := by
  simp [pointerWidth, addressWidth, Nat.pow_succ, p.powerOfTwo, Nat.mul_comm]

/-- Within the legal occupancy window, equality of finite ring pointers is
equivalent to the unbounded distance being exactly one queue depth. -/
theorem pointerWord_eq_add_depth_iff (p : Parameters) (seen next : Nat)
    (ordered : seen ≤ next) (bounded : next - seen ≤ p.depth) :
    pointerWord p next = pointerWord p (seen + p.depth) ↔
      next - seen = p.depth := by
  constructor
  · intro wordsEqual
    by_contra notFull
    have belowDepth : next - seen < p.depth := by omega
    have nextLt : next < seen + p.depth := by omega
    have ringPositive : 0 < 2 ^ pointerWidth p := Nat.two_pow_pos _
    have depthLtRing : p.depth < 2 ^ pointerWidth p := by
      rw [pointerRing_eq]
      have := p.depthAtLeastTwo
      omega
    have modEqual : next % 2 ^ pointerWidth p =
        (seen + p.depth) % 2 ^ pointerWidth p := by
      have := congrArg BitVec.toNat wordsEqual
      simpa [pointerWord] using this
    exact (mod_ne_of_ordered_distance (Nat.le_of_lt nextLt) (Nat.ne_of_lt nextLt)
      (by omega : seen + p.depth - next < 2 ^ pointerWidth p)) modEqual
  · intro fullDistance
    have nextEq : next = seen + p.depth := by omega
    exact congrArg (pointerWord p) nextEq

theorem pointerWord_eq_iff (p : Parameters) (left right : Nat)
    (ordered : left ≤ right) (bounded : right - left ≤ p.depth) :
    pointerWord p left = pointerWord p right ↔ left = right := by
  constructor
  · intro wordsEqual
    by_contra different
    have depthLtRing : p.depth < 2 ^ pointerWidth p := by
      rw [pointerRing_eq]
      omega
    have modEqual : left % 2 ^ pointerWidth p = right % 2 ^ pointerWidth p := by
      have := congrArg BitVec.toNat wordsEqual
      simpa [pointerWord] using this
    exact (mod_ne_of_ordered_distance ordered different (by omega)) modEqual
  · exact fun | rfl => rfl

/-- Decoding a finite emitted Gray pointer recovers the corresponding binary
pointer word. -/
theorem fromGray_grayWord (p : Parameters) (count : Nat) (state : St) :
    (fromGray (.lit (grayWord p count))).eval state = pointerWord p count := by
  apply BitVec.eq_of_toNat_eq
  have positive : 0 < pointerWidth p := by simp [pointerWidth]
  unfold fromGray
  rw [fromGrayPrefix_eval_toNat _ (pointerWidth p - 1) (by omega)]
  let value := count % 2 ^ pointerWidth p
  have valueBound : value < 2 ^ pointerWidth p :=
    Nat.mod_lt count (Nat.two_pow_pos _)
  have grayBound : Gray.encode value < 2 ^ pointerWidth p :=
    Gray.encode_lt_two_pow valueBound
  have grayToNat : (grayWord p count).toNat = Gray.encode value := by
    simp [grayWord, value, Nat.mod_eq_of_lt grayBound]
  change Gray.decodePrefix (grayWord p count).toNat (pointerWidth p - 1) =
    (pointerWord p count).toNat
  rw [grayToNat, Gray.decodePrefix_encode_width positive valueBound]
  simp [pointerWord, value]

/-- The expression compiled into both control islands is exactly the
finite-width image of the mathematical Gray encoding. -/
theorem toGray_pointerWord (p : Parameters) (count : Nat) (state : St) :
    (toGray (.lit (pointerWord p count))).eval state = grayWord p count := by
  apply BitVec.eq_of_toNat_eq
  have widthPositive : 0 < pointerWidth p := by simp [pointerWidth]
  have oneLt : 1 < 2 ^ pointerWidth p :=
    Nat.one_lt_two_pow (Nat.ne_of_gt widthPositive)
  have shiftedLt : (count % 2 ^ pointerWidth p) >>> 1 <
      2 ^ pointerWidth p :=
    lt_of_le_of_lt (Nat.shiftRight_le _ _)
      (Nat.mod_lt count (Nat.two_pow_pos (pointerWidth p)))
  simp [toGray, pointerWord, grayWord, Gray.encode, Expr.eval,
    BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt oneLt,
    Nat.mod_eq_of_lt shiftedLt]

theorem pointerWord_succ (p : Parameters) (count : Nat) :
    pointerWord p (count + 1) = pointerWord p count + 1 := by
  apply BitVec.eq_of_toNat_eq
  simp [pointerWord, BitVec.toNat_add]

theorem pointerWord_add (p : Parameters) (left right : Nat) :
    pointerWord p (left + right) =
      pointerWord p left + BitVec.ofNat (pointerWidth p) right := by
  apply BitVec.eq_of_toNat_eq
  simp [pointerWord, BitVec.toNat_add, Nat.add_mod]

theorem toGray_pointerWord_succ (p : Parameters) (count : Nat) (state : St) :
    (toGray (.lit (pointerWord p count + 1))).eval state =
      grayWord p (count + 1) := by
  rw [← pointerWord_succ]
  exact toGray_pointerWord p (count + 1) state

/-- State relation used to replace the schedule model's logical counters by
finite emitted pointer registers. Counts remain unbounded ghosts; every
physical coordinate is their finite-width image. The flag clauses are stated
against the synchronized conservative views, not a clock ratio. -/
structure ControlRepAt {width : Nat} (p : Parameters) (sameWidth : p.width = width)
    (fifo : AsyncFifo.State width) (source sink : St) : Prop where
  writeBinary : source.regs (writeBinary p).name (pointerWidth p) =
    pointerWord p fifo.writeCount
  writeGray : source.regs (writeGray p).name (pointerWidth p) =
    grayWord p fifo.writeCount
  readStage0 : source.regs (readGraySync0 p).name (pointerWidth p) =
    grayWord p fifo.readStage0
  readSeen : source.regs (readGraySync1 p).name (pointerWidth p) =
    grayWord p fifo.readSeenByWrite
  readBinary : sink.regs (readBinary p).name (pointerWidth p) =
    pointerWord p fifo.readCount
  readGray : sink.regs (readGray p).name (pointerWidth p) =
    grayWord p fifo.readCount
  writeStage0 : sink.regs (writeGraySync0 p).name (pointerWidth p) =
    grayWord p fifo.writeStage0
  writeSeen : sink.regs (writeGraySync1 p).name (pointerWidth p) =
    grayWord p fifo.writeSeenByRead

def ControlRep {width : Nat} (p : Parameters) (sameWidth : p.width = width)
    (fifo : AsyncFifo.State width) (source sink : St) : Prop :=
  ControlRepAt p sameWidth fifo source sink

/-- Non-vacuity at common reset. This is the base case for the compiled
control refinement. -/
theorem controlRep_reset (p : Parameters) :
    ControlRep p rfl (AsyncFifo.reset p.width)
      (sourceControl p).reset (sinkControl p).reset := by
  refine {
    writeBinary := ?_
    writeGray := ?_
    readStage0 := ?_
    readSeen := ?_
    readBinary := ?_
    readGray := ?_
    writeStage0 := ?_
    writeSeen := ?_ }
  all_goals
    simp [Design.reset, sourceControl, sinkControl, RegEnv.set, Reg.decl,
      writeBinary, writeGray, readGraySync0, readGraySync1,
      readBinary, readGray, writeGraySync0, writeGraySync1,
      pointerWord, grayWord, Gray.encode, AsyncFifo.reset]

/-! ## Executable request wiring

The request-to-port functions below are logical wiring only. They select no
physical CDC primitive and mention no implementation technology. -/

def sourcePush {width : Nat} (request : AsyncFifo.Request width) :
    Option (BitVec width) :=
  if request.sourceReleased && request.sourceTick then request.push else none

def sourceInput (p : Parameters) (fifo : AsyncFifo.State p.width)
    (request : AsyncFifo.Request p.width) : InEnv :=
  sourceDrive p (sourcePush request)
    (grayWord p (AsyncFifo.sample fifo.readStage0 fifo.readCount request.readSample))

def sinkPopRequest {width : Nat} (request : AsyncFifo.Request width) : Bool :=
  request.sinkReleased && request.sinkTick && request.pop

def sinkInput (p : Parameters) (fifo : AsyncFifo.State p.width)
    (request : AsyncFifo.Request p.width) : InEnv :=
  sinkDrive p (sinkPopRequest request)
    (grayWord p (AsyncFifo.sample fifo.writeStage0 fifo.writeCount request.writeSample))

def sourceNext (p : Parameters) (fifo : AsyncFifo.State p.width)
    (request : AsyncFifo.Request p.width) (state : St) : St :=
  if request.sourceReleased && request.sourceTick then
    (sourceControl p).cycleOpen (sourceInput p fifo request) state
  else state

def sinkNext (p : Parameters) (fifo : AsyncFifo.State p.width)
    (request : AsyncFifo.Request p.width) (state : St) : St :=
  if request.sinkReleased && request.sinkTick then
    (sinkControl p).cycleOpen (sinkInput p fifo request) state
  else state

@[simp] private theorem bit_and_one (value : BitVec 1) :
    value &&& 1#1 = value := by
  bv_decide

@[simp] private theorem bit_and_zero (value : BitVec 1) :
    value &&& 0#1 = 0#1 := by
  bv_decide

/-- The compiled write enable is exactly the executable FIFO's accepted
transfer decision, assuming the proven occupancy bound and control-state
relation. -/
theorem writeTake_eq_accepted (p : Parameters) (c : Chan p.width)
    (depthEq : c.depth = p.depth) (queue : Chan.State p.width)
    (fifo : AsyncFifo.State p.width) (source sink : St)
    (request : AsyncFifo.Request p.width)
    (fifoRep : AsyncFifo.Rep c queue fifo)
    (controlRep : ControlRep p rfl fifo source sink) :
    (writeTake p).eval
        (source.setInputs (sourceControl p).inputs (sourceInput p fifo request)) =
      if (AsyncFifo.accepted c fifo request).isSome then 1#1 else 0#1 := by
  let driven := source.setInputs (sourceControl p).inputs (sourceInput p fifo request)
  have writePreserved :
      (source.setInputs (sourceControl p).inputs (sourceInput p fifo request)).regs
          (writeBinary p).name (pointerWidth p) =
        source.regs (writeBinary p).name (pointerWidth p) :=
    source.setInputs_regs_notin (sourceControl p).inputs (sourceInput p fifo request)
      (writeBinary p).name (pointerWidth p) (by
        intro declared member equal
        have names := congrArg Prod.fst equal
        simp [sourceControl, Reg.input, sourceValid, sourcePayload, rawReadGray] at member
        rcases member with rfl | rfl | rfl <;> simp [writeBinary] at names)
  have syncPreserved :
      (source.setInputs (sourceControl p).inputs (sourceInput p fifo request)).regs
          (readGraySync1 p).name (pointerWidth p) =
        source.regs (readGraySync1 p).name (pointerWidth p) :=
    source.setInputs_regs_notin (sourceControl p).inputs (sourceInput p fifo request)
      (readGraySync1 p).name (pointerWidth p) (by
        intro declared member equal
        have names := congrArg Prod.fst equal
        simp [sourceControl, Reg.input, sourceValid, sourcePayload, rawReadGray] at member
        rcases member with rfl | rfl | rfl <;> simp [readGraySync1] at names)
  have validDriven :
      (source.setInputs (sourceControl p).inputs (sourceInput p fifo request)).regs
          sourceValid.name 1 =
        if (sourcePush request).isSome then 1#1 else 0#1 := by
    simp [St.setInputs, sourceControl, sourceInput, RegEnv.set, sourceDrive,
      Reg.input, sourceValid, sourcePayload, rawReadGray]
  have syncEval :
      ((readGraySync1 p).rd.eval driven) = grayWord p fifo.readSeenByWrite := by
    simp only [Reg.rd, Expr.eval, driven]
    rw [syncPreserved, controlRep.readSeen]
  have decoded :
      (fromGray (readGraySync1 p).rd).eval driven =
        pointerWord p fifo.readSeenByWrite :=
    (fromGray_eval_congr (readGraySync1 p).rd
      (.lit (grayWord p fifo.readSeenByWrite)) driven syncEval).trans
        (fromGray_grayWord p fifo.readSeenByWrite driven)
  have fullEval :
      (fullNow p).eval driven =
        if fifo.writeCount - fifo.readSeenByWrite = p.depth then 1#1 else 0#1 := by
    have ordered : fifo.readSeenByWrite ≤ fifo.writeCount :=
      le_trans fifoRep.readViewSafe fifoRep.countersOrdered
    have bounded : fifo.writeCount - fifo.readSeenByWrite ≤ p.depth := by
      simpa [depthEq] using fifoRep.writerViewBounded
    have fullIff := pointerWord_eq_add_depth_iff p fifo.readSeenByWrite
      fifo.writeCount ordered bounded
    have targetEval :
        (fromGray (readGraySync1 p).rd).eval driven +
            BitVec.ofNat (pointerWidth p) p.depth =
          pointerWord p (fifo.readSeenByWrite + p.depth) := by
      rw [decoded, ← pointerWord_add]
    have writeDriven : driven.regs (writeBinary p).name (pointerWidth p) =
        pointerWord p fifo.writeCount := by
      dsimp only [driven]
      rw [writePreserved, controlRep.writeBinary]
    simp only [fullNow, fullTarget, Expr.eval, Reg.rd]
    change (if driven.regs (writeBinary p).name (pointerWidth p) =
        (fromGray (readGraySync1 p).rd).eval driven +
          BitVec.ofNat (pointerWidth p) p.depth then 1#1 else 0#1) = _
    simp [writeDriven, targetEval, fullIff]
  change (driven.regs sourceValid.name 1 &&& ~~~(fullNow p).eval driven) = _
  rw [validDriven, fullEval]
  have occupancyBound : fifo.writeCount - fifo.readSeenByWrite ≤ p.depth := by
    simpa [depthEq] using fifoRep.writerViewBounded
  have spaceIff : fifo.writeCount - fifo.readSeenByWrite < p.depth ↔
      fifo.writeCount - fifo.readSeenByWrite ≠ p.depth := by omega
  unfold AsyncFifo.accepted
  rw [depthEq]
  by_cases fullNow : fifo.writeCount - fifo.readSeenByWrite = p.depth <;>
    simp [fullNow, sourcePush, spaceIff]

/-- The compiled read enable is exactly the executable FIFO's delivery
decision. The data value itself is supplied by the separately certified
`AsyncQueueStorage` leaf. -/
theorem readTake_eq_delivered (p : Parameters) (c : Chan p.width)
    (depthEq : c.depth = p.depth) (queue : Chan.State p.width)
    (fifo : AsyncFifo.State p.width)
    (source sink : St) (request : AsyncFifo.Request p.width)
    (fifoRep : AsyncFifo.Rep c queue fifo)
    (controlRep : ControlRep p rfl fifo source sink) :
    (readTake p).eval
        (sink.setInputs (sinkControl p).inputs (sinkInput p fifo request)) =
      if (AsyncFifo.delivered c fifo request).isSome then 1#1 else 0#1 := by
  let driven := sink.setInputs (sinkControl p).inputs (sinkInput p fifo request)
  have readPreserved :
      (sink.setInputs (sinkControl p).inputs (sinkInput p fifo request)).regs
          (readBinary p).name (pointerWidth p) =
        sink.regs (readBinary p).name (pointerWidth p) :=
    sink.setInputs_regs_notin (sinkControl p).inputs (sinkInput p fifo request)
      (readBinary p).name (pointerWidth p) (by
        intro declared member equal
        have names := congrArg Prod.fst equal
        simp [sinkControl, Reg.input, sinkPop, rawWriteGray] at member
        rcases member with rfl | rfl <;> simp [readBinary] at names)
  have syncPreserved :
      (sink.setInputs (sinkControl p).inputs (sinkInput p fifo request)).regs
          (writeGraySync1 p).name (pointerWidth p) =
        sink.regs (writeGraySync1 p).name (pointerWidth p) :=
    sink.setInputs_regs_notin (sinkControl p).inputs (sinkInput p fifo request)
      (writeGraySync1 p).name (pointerWidth p) (by
        intro declared member equal
        have names := congrArg Prod.fst equal
        simp [sinkControl, Reg.input, sinkPop, rawWriteGray] at member
        rcases member with rfl | rfl <;> simp [writeGraySync1] at names)
  have popDriven :
      (sink.setInputs (sinkControl p).inputs (sinkInput p fifo request)).regs
          sinkPop.name 1 = if sinkPopRequest request then 1#1 else 0#1 := by
    simp [St.setInputs, sinkControl, sinkInput, RegEnv.set, sinkDrive,
      Reg.input, sinkPop, rawWriteGray]
  have syncEval :
      ((writeGraySync1 p).rd.eval driven) = grayWord p fifo.writeSeenByRead := by
    simp only [Reg.rd, Expr.eval, driven]
    rw [syncPreserved, controlRep.writeSeen]
  have decoded :
      (fromGray (writeGraySync1 p).rd).eval driven =
        pointerWord p fifo.writeSeenByRead :=
    (fromGray_eval_congr (writeGraySync1 p).rd
      (.lit (grayWord p fifo.writeSeenByRead)) driven syncEval).trans
        (fromGray_grayWord p fifo.writeSeenByRead driven)
  have emptyEval :
      (emptyNow p).eval driven =
        if fifo.readCount = fifo.writeSeenByRead then 1#1 else 0#1 := by
    have readDriven : driven.regs (readBinary p).name (pointerWidth p) =
        pointerWord p fifo.readCount := by
      dsimp only [driven]
      rw [readPreserved, controlRep.readBinary]
    have viewedBounded : fifo.writeSeenByRead - fifo.readCount ≤ p.depth := by
      have actualBound := fifoRep.bounded
      rw [depthEq] at actualBound
      exact le_trans (Nat.sub_le_sub_right fifoRep.writeViewSafe fifo.readCount)
        actualBound
    have emptyIff := pointerWord_eq_iff p fifo.readCount fifo.writeSeenByRead
      fifoRep.writeViewLower viewedBounded
    simp only [emptyNow, Expr.eval, Reg.rd]
    change (if driven.regs (readBinary p).name (pointerWidth p) =
        (fromGray (writeGraySync1 p).rd).eval driven then 1#1 else 0#1) = _
    simp [readDriven, decoded, emptyIff]
  change (driven.regs sinkPop.name 1 &&& ~~~(emptyNow p).eval driven) = _
  rw [popDriven, emptyEval]
  have nonemptyIff : fifo.readCount < fifo.writeSeenByRead ↔
      fifo.readCount ≠ fifo.writeSeenByRead := by
    have := fifoRep.writeViewLower
    omega
  by_cases emptyNow : fifo.readCount = fifo.writeSeenByRead <;>
    simp [emptyNow, sinkPopRequest, AsyncFifo.delivered, nonemptyIff]

theorem nextWriteBinary_eval (p : Parameters) (c : Chan p.width)
    (depthEq : c.depth = p.depth) (queue : Chan.State p.width)
    (fifo : AsyncFifo.State p.width) (source sink : St)
    (request : AsyncFifo.Request p.width)
    (fifoRep : AsyncFifo.Rep c queue fifo)
    (controlRep : ControlRep p rfl fifo source sink) :
    (nextWriteBinary p).eval
        (source.setInputs (sourceControl p).inputs (sourceInput p fifo request)) =
      pointerWord p (AsyncFifo.step c fifo request).state.writeCount := by
  let driven := source.setInputs (sourceControl p).inputs (sourceInput p fifo request)
  have writePreserved : driven.regs (writeBinary p).name (pointerWidth p) =
      pointerWord p fifo.writeCount := by
    dsimp only [driven]
    rw [source.setInputs_regs_notin (sourceControl p).inputs (sourceInput p fifo request)
      (writeBinary p).name (pointerWidth p) (by
        intro declared member equal
        have names := congrArg Prod.fst equal
        simp [sourceControl, Reg.input, sourceValid, sourcePayload, rawReadGray] at member
        rcases member with rfl | rfl | rfl <;> simp [writeBinary] at names)]
    exact controlRep.writeBinary
  have take := writeTake_eq_accepted p c depthEq queue fifo source sink request
    fifoRep controlRep
  change (driven.regs (writeBinary p).name (pointerWidth p) +
      BitVec.zeroExtend (pointerWidth p) ((writeTake p).eval driven)) = _
  rw [writePreserved, take]
  cases acceptedEq : AsyncFifo.accepted c fifo request with
  | none => simp [AsyncFifo.step, acceptedEq]
  | some value =>
      simp only [AsyncFifo.step, acceptedEq, Option.isSome_some, ↓reduceIte]
      have oneExtended : BitVec.zeroExtend (pointerWidth p) 1#1 =
          BitVec.ofNat (pointerWidth p) 1 := by
        apply BitVec.eq_of_toNat_eq
        simp
      rw [oneExtended]
      exact (pointerWord_succ p fifo.writeCount).symm

theorem nextReadBinary_eval (p : Parameters) (c : Chan p.width)
    (depthEq : c.depth = p.depth) (queue : Chan.State p.width)
    (fifo : AsyncFifo.State p.width) (source sink : St)
    (request : AsyncFifo.Request p.width)
    (fifoRep : AsyncFifo.Rep c queue fifo)
    (controlRep : ControlRep p rfl fifo source sink) :
    (nextReadBinary p).eval
        (sink.setInputs (sinkControl p).inputs (sinkInput p fifo request)) =
      pointerWord p (AsyncFifo.step c fifo request).state.readCount := by
  let driven := sink.setInputs (sinkControl p).inputs (sinkInput p fifo request)
  have readPreserved : driven.regs (readBinary p).name (pointerWidth p) =
      pointerWord p fifo.readCount := by
    dsimp only [driven]
    rw [sink.setInputs_regs_notin (sinkControl p).inputs (sinkInput p fifo request)
      (readBinary p).name (pointerWidth p) (by
        intro declared member equal
        have names := congrArg Prod.fst equal
        simp [sinkControl, Reg.input, sinkPop, rawWriteGray] at member
        rcases member with rfl | rfl <;> simp [readBinary] at names)]
    exact controlRep.readBinary
  have take := readTake_eq_delivered p c depthEq queue fifo source sink request
    fifoRep controlRep
  change (driven.regs (readBinary p).name (pointerWidth p) +
      BitVec.zeroExtend (pointerWidth p) ((readTake p).eval driven)) = _
  rw [readPreserved, take]
  cases deliveredEq : AsyncFifo.delivered c fifo request with
  | none => simp [AsyncFifo.step, deliveredEq]
  | some value =>
      simp only [AsyncFifo.step, deliveredEq, Option.isSome_some, ↓reduceIte]
      have oneExtended : BitVec.zeroExtend (pointerWidth p) 1#1 =
          BitVec.ofNat (pointerWidth p) 1 := by
        apply BitVec.eq_of_toNat_eq
        simp
      rw [oneExtended]
      exact (pointerWord_succ p fifo.readCount).symm

theorem toGray_eval_congr {width : Nat} (left right : Expr width)
    (state : St) (equal : left.eval state = right.eval state) :
    (toGray left).eval state = (toGray right).eval state := by
  simp [toGray, Expr.eval, equal]

theorem nextWriteGray_eval (p : Parameters) (c : Chan p.width)
    (depthEq : c.depth = p.depth) (queue : Chan.State p.width)
    (fifo : AsyncFifo.State p.width) (source sink : St)
    (request : AsyncFifo.Request p.width)
    (fifoRep : AsyncFifo.Rep c queue fifo)
    (controlRep : ControlRep p rfl fifo source sink) :
    (nextWriteGray p).eval
        (source.setInputs (sourceControl p).inputs (sourceInput p fifo request)) =
      grayWord p (AsyncFifo.step c fifo request).state.writeCount := by
  let driven := source.setInputs (sourceControl p).inputs (sourceInput p fifo request)
  have binary := nextWriteBinary_eval p c depthEq queue fifo source sink request
    fifoRep controlRep
  exact (toGray_eval_congr (nextWriteBinary p)
    (.lit (pointerWord p (AsyncFifo.step c fifo request).state.writeCount))
    driven binary).trans
      (toGray_pointerWord p (AsyncFifo.step c fifo request).state.writeCount driven)

theorem nextReadGray_eval (p : Parameters) (c : Chan p.width)
    (depthEq : c.depth = p.depth) (queue : Chan.State p.width)
    (fifo : AsyncFifo.State p.width) (source sink : St)
    (request : AsyncFifo.Request p.width)
    (fifoRep : AsyncFifo.Rep c queue fifo)
    (controlRep : ControlRep p rfl fifo source sink) :
    (nextReadGray p).eval
        (sink.setInputs (sinkControl p).inputs (sinkInput p fifo request)) =
      grayWord p (AsyncFifo.step c fifo request).state.readCount := by
  let driven := sink.setInputs (sinkControl p).inputs (sinkInput p fifo request)
  have binary := nextReadBinary_eval p c depthEq queue fifo source sink request
    fifoRep controlRep
  exact (toGray_eval_congr (nextReadBinary p)
    (.lit (pointerWord p (AsyncFifo.step c fifo request).state.readCount))
    driven binary).trans
      (toGray_pointerWord p (AsyncFifo.step c fifo request).state.readCount driven)

/-- The complete compiler-facing controller relation is inductive for every
executable request. Source and sink may tick separately, together, or not at
all; synchronizer samples remain adversarial within the executable model. -/
theorem controlRep_step (p : Parameters) (c : Chan p.width)
    (depthEq : c.depth = p.depth) (queue : Chan.State p.width)
    (fifo : AsyncFifo.State p.width) (source sink : St)
    (request : AsyncFifo.Request p.width)
    (fifoRep : AsyncFifo.Rep c queue fifo)
    (controlRep : ControlRep p rfl fifo source sink) :
    ControlRep p rfl (AsyncFifo.step c fifo request).state
      (sourceNext p fifo request source) (sinkNext p fifo request sink) := by
  refine {
    writeBinary := ?_
    writeGray := ?_
    readStage0 := ?_
    readSeen := ?_
    readBinary := ?_
    readGray := ?_
    writeStage0 := ?_
    writeSeen := ?_ }
  · by_cases on : request.sourceReleased && request.sourceTick
    · simp only [sourceNext, on, ↓reduceIte]
      rw [source_writeBinary_cycle]
      exact nextWriteBinary_eval p c depthEq queue fifo source sink request
        fifoRep controlRep
    · simp [sourceNext, on, AsyncFifo.step, AsyncFifo.accepted,
        controlRep.writeBinary]
  · by_cases on : request.sourceReleased && request.sourceTick
    · simp only [sourceNext, on, ↓reduceIte]
      rw [source_writeGray_cycle]
      exact nextWriteGray_eval p c depthEq queue fifo source sink request
        fifoRep controlRep
    · simp [sourceNext, on, AsyncFifo.step, AsyncFifo.accepted,
        controlRep.writeGray]
  · by_cases on : request.sourceReleased && request.sourceTick
    · simp only [sourceNext, on, ↓reduceIte]
      rw [source_sync0_cycle]
      unfold sourceInput
      rw [sourceDrive_remote]
      simp [AsyncFifo.step, on]
    · simp [sourceNext, on, AsyncFifo.step, controlRep.readStage0]
  · by_cases on : request.sourceReleased && request.sourceTick
    · simp only [sourceNext, on, ↓reduceIte]
      rw [source_sync_cycle, controlRep.readStage0]
      simp [AsyncFifo.step, on]
    · simp [sourceNext, on, AsyncFifo.step, controlRep.readSeen]
  · by_cases on : request.sinkReleased && request.sinkTick
    · simp only [sinkNext, on, ↓reduceIte]
      rw [sink_readBinary_cycle]
      exact nextReadBinary_eval p c depthEq queue fifo source sink request
        fifoRep controlRep
    · simp [sinkNext, on, AsyncFifo.step, AsyncFifo.delivered,
        controlRep.readBinary]
  · by_cases on : request.sinkReleased && request.sinkTick
    · simp only [sinkNext, on, ↓reduceIte]
      rw [sink_readGray_cycle]
      exact nextReadGray_eval p c depthEq queue fifo source sink request
        fifoRep controlRep
    · simp [sinkNext, on, AsyncFifo.step, AsyncFifo.delivered,
        controlRep.readGray]
  · by_cases on : request.sinkReleased && request.sinkTick
    · simp only [sinkNext, on, ↓reduceIte]
      rw [sink_sync0_cycle]
      unfold sinkInput
      rw [sinkDrive_remote]
      simp [AsyncFifo.step, on]
    · simp [sinkNext, on, AsyncFifo.step, controlRep.writeStage0]
  · by_cases on : request.sinkReleased && request.sinkTick
    · simp only [sinkNext, on, ↓reduceIte]
      rw [sink_sync_cycle, controlRep.writeStage0]
      simp [AsyncFifo.step, on]
    · simp [sinkNext, on, AsyncFifo.step, controlRep.writeSeen]

/-! ## Joined compiler-produced controller refinement -/

namespace Compiled

variable (p : Parameters) (c : Chan p.width) (depthEq : c.depth = p.depth)
  (positiveDepth : 0 < c.depth)
  (implementation : AsyncQueueStorage.Implementation
    (AsyncFifo.storageParameters c positiveDepth))

/-- Concrete channel state containing the selected proved storage state and
both ordinary compiler-facing control `Design` states. The finite FIFO state
inside `composed` is the semantic join state; `controls` below proves that the
compiler-facing registers take exactly the corresponding transition. -/
structure State where
  composed : AsyncFifo.WithStorage.State c positiveDepth implementation
  source : St
  sink : St

def reset : State p c positiveDepth implementation where
  composed := AsyncFifo.WithStorage.reset c positiveDepth implementation
  source := (sourceControl p).reset
  sink := (sinkControl p).reset

def step (state : State p c positiveDepth implementation)
    (request : AsyncFifo.Request p.width) :
    Chan.ConcreteResult (State p c positiveDepth implementation) p.width :=
  let physical := AsyncFifo.WithStorage.step c positiveDepth implementation
    state.composed request
  { state :=
      { composed := physical.state
        source := sourceNext p state.composed.fifo request state.source
        sink := sinkNext p state.composed.fifo request state.sink }
    accepted := physical.accepted
    delivered := physical.delivered }

/-- The abstract queue is represented by the parametric storage composition,
while `controls` states that the actual compiler-facing pointer/synchronizer
registers are exactly its control state. -/
structure Rep (queue : Chan.State p.width)
    (state : State p c positiveDepth implementation) : Prop where
  composed : AsyncFifo.WithStorage.Rep c positiveDepth implementation
    queue state.composed
  controls : ControlRep p rfl state.composed.fifo state.source state.sink

theorem rep_reset :
    Rep p c positiveDepth implementation []
      (reset p c positiveDepth implementation) := by
  exact {
    composed := AsyncFifo.WithStorage.rep_reset c positiveDepth implementation
    controls := controlRep_reset p }

include depthEq in
theorem rep_step (queue : Chan.State p.width)
    (state : State p c positiveDepth implementation)
    (request : AsyncFifo.Request p.width)
    (rep : Rep p c positiveDepth implementation queue state) :
    let physical := step p c positiveDepth implementation state request
    let abstract := c.step queue physical.event
    Rep p c positiveDepth implementation abstract.state physical.state ∧
      abstract.accepted = physical.accepted.isSome ∧
      abstract.delivered = physical.delivered := by
  dsimp only
  have composedNext := AsyncFifo.WithStorage.rep_step c positiveDepth implementation
    queue state.composed request rep.composed
  have controlsNext := controlRep_step p c depthEq queue state.composed.fifo
    state.source state.sink request rep.composed.fifo rep.controls
  exact ⟨
    { composed := composedNext.1
      controls := controlsNext },
    composedNext.2⟩

/-- A single technology-neutral channel refinement whose concrete state
contains compiler-produced control Designs and the selected proved storage
implementation. Structural emission of those components remains a separate
theorem boundary. No FPGA family, ASIC macro, or synthesis flow is selected. -/
def refinement : Chan.Refinement c where
  ConcreteState := State p c positiveDepth implementation
  Request := AsyncFifo.Request p.width
  reset := reset p c positiveDepth implementation
  step := step p c positiveDepth implementation
  Rep := Rep p c positiveDepth implementation
  reset_refines := rep_reset p c positiveDepth implementation
  step_refines := by
    intro queue state request rep
    exact rep_step p c depthEq positiveDepth implementation queue state request rep

end Compiled

end Loom.Hw.Cdc.AsyncFifoDesign
