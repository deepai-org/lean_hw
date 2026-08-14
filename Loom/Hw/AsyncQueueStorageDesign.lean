-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.AsyncQueueStorage
import Loom.Hw.Notation
import Loom.Hw.CertifiedDesign

/-!
# Compiler-produced portable asynchronous-queue storage

This file is the unconditional implementation witness for
`AsyncQueueStorage`.  The write-clock Design owns a bank of ordinary
registers.  The read-clock Design samples those slot outputs through a
balanced mux and an explicit synchronous response pipeline.  The FIFO
ownership theorem must prove that the selected slot is stable before the
read; no unsynchronized control or changing payload is exposed to users.

Both halves are ordinary `Design` values.  Consequently their registers,
muxes, enables, and pipeline are handled by the existing compiler and DAG
certificate path.  A macro backend may replace this deliberately
area-expensive implementation behind the same storage contract.
-/

namespace Loom.Hw.Cdc.AsyncQueueStorage

open Loom.Hw

/-- Address width sufficient for every declared physical slot. -/
def addressWidth (p : Parameters) : Nat := Nat.log2 (p.depth - 1) + 1

def writeEnable : Reg 1 := ⟨"write_enable"⟩
def writeAddress (p : Parameters) : Reg (addressWidth p) := ⟨"write_address"⟩
def writeData (p : Parameters) : Reg p.width := ⟨"write_data"⟩
def readEnable : Reg 1 := ⟨"read_enable"⟩
def readAddress (p : Parameters) : Reg (addressWidth p) := ⟨"read_address"⟩

def slots (p : Parameters) : RegArray p.width p.depth := ⟨"slot_"⟩
def readSlotInputs (p : Parameters) : RegArray p.width p.depth := ⟨"slot_"⟩
def readDataPipeline (p : Parameters) : RegArray p.width p.readLatency :=
  ⟨"read_data_"⟩
def readValidPipeline (p : Parameters) : RegArray 1 p.readLatency :=
  ⟨"read_valid_"⟩

def readSample (p : Parameters) : Expr p.width :=
  (readSlotInputs p).dynRd (readAddress p).rd (.lit 0)

/-- Write-domain half. Every storage bit is an ordinary compiler-visible
register; the only action is a typed, dynamically selected write. -/
def writerDesign (p : Parameters) : Design :=
  let bank := slots p
  { name := s!"async_queue_register_bank_writer_w{p.width}_d{p.depth}"
    regs := bank.decls
    mems := []
    rules := [⟨"write", .ite writeEnable.rd
      (bank.dynSet (writeAddress p).rd (writeData p).rd) .skip⟩]
    inputs := [writeEnable.input, (writeAddress p).input, (writeData p).input]
    outputs := bank.handles.map (·.name) }

private def readPipelineActions (p : Parameters) : List Act :=
  let incoming := readSample p
  (List.range p.readLatency).flatMap fun stage =>
    if stage = 0 then
      [(readDataPipeline p).regN 0 |>.set incoming,
       (readValidPipeline p).regN 0 |>.set readEnable.rd]
    else
      [(readDataPipeline p).regN stage |>.set
          ((readDataPipeline p).regN (stage - 1)).rd,
       (readValidPipeline p).regN stage |>.set
          ((readValidPipeline p).regN (stage - 1)).rd]

/-- Read-domain half. Slot values are data inputs; the FIFO proof is
responsible for their stability. Address selection and the declared positive
read-latency pipeline are entirely ordinary Design logic. -/
def readerDesign (p : Parameters) : Design :=
  let dataPipe := readDataPipeline p
  let validPipe := readValidPipeline p
  let last := p.readLatency - 1
  { name := s!"async_queue_register_bank_reader_w{p.width}_d{p.depth}_l{p.readLatency}"
    regs := dataPipe.decls ++ validPipe.decls
    mems := []
    rules := [⟨"read_pipeline", actSeq (readPipelineActions p)⟩]
    inputs := (readSlotInputs p).handles.map (·.input) ++
      [readEnable.input, (readAddress p).input]
    outputs := [(dataPipe.regN last).name, (validPipe.regN last).name]
    combOutputs := [⟨"read_sample", p.width, readSample p⟩] }

/-- The complete compiler-facing portable realization. `slotConnections`
names the only cross-domain data edges. They are internal to the storage
leaf, not raw user System connections, and later conformance proves they are
stable whenever the reader is allowed to consume them. -/
structure RegisterBankDesigns (p : Parameters) where
  writer : Design
  reader : Design
  writer_eq : writer = writerDesign p
  reader_eq : reader = readerDesign p
  slotConnections : List String
  slots_eq : slotConnections = (slots p).handles.map (·.name)

def registerBankDesigns (p : Parameters) : RegisterBankDesigns p where
  writer := writerDesign p
  reader := readerDesign p
  writer_eq := rfl
  reader_eq := rfl
  slotConnections := (slots p).handles.map (·.name)
  slots_eq := rfl

/-- Mechanical compiler-side acceptance of both halves. This proposition is
the input to `designWFCheck_sound`; concrete certified packages discharge it
by kernel evaluation. -/
def RegisterBankDesigns.compilerReady {p : Parameters}
    (designs : RegisterBankDesigns p) : Prop :=
  Compile.designWFCheck designs.writer = true ∧
  Compile.designWFCheck designs.reader = true ∧
  designs.writer.fastWFB = true ∧ designs.reader.fastWFB = true

/-- Both portable storage halves packaged on the same compiler/DAG/byte path
as any other certified single-clock Design. No runtime DAG rejection remains:
`prepareSimulator?_complete` constructs the certificate for every generated
lowering. -/
structure CertifiedRegisterBankDesigns (p : Parameters) where
  designs : RegisterBankDesigns p
  writer : CertifiedDesign designs.writer
  reader : CertifiedDesign designs.reader

def RegisterBankDesigns.certify {p : Parameters} (designs : RegisterBankDesigns p)
    (ready : designs.compilerReady) : CertifiedRegisterBankDesigns p :=
  let writerBase : FastEval.VerifiedSimulator designs.writer := ⟨ready.2.2.1⟩
  let readerBase : FastEval.VerifiedSimulator designs.reader := ⟨ready.2.2.2⟩
  let writerDag := DagEval.verifiedSimulatorOfPreparation writerBase
    (DagEval.prepareSimulator?_complete writerBase)
  let readerDag := DagEval.verifiedSimulatorOfPreparation readerBase
    (DagEval.prepareSimulator?_complete readerBase)
  { designs
    writer := .of (Compile.designWFCheck_sound _ ready.1) writerDag
    reader := .of (Compile.designWFCheck_sound _ ready.2.1) readerDag }

/-! ## Unconditional production-shape witness

The stock FIFO used by the small example and LNP64mini has two slots and a
one-read-tick storage latency. The theorem remains polymorphic in payload
width. Deeper or differently pipelined leaves use the same contract, but are
not silently selected as generic implementation defaults. -/

namespace DepthTwo

def parameters (width : Nat) : Parameters where
  width := width
  depth := 2
  readLatency := 1
  depthPositive := by decide
  readLatencyPositive := by decide

def slot0 (width : Nat) : Reg width := (slots (parameters width)).regN 0
def slot1 (width : Nat) : Reg width := (slots (parameters width)).regN 1
def readSlot0 (width : Nat) : Reg width := (readSlotInputs (parameters width)).regN 0
def readSlot1 (width : Nat) : Reg width := (readSlotInputs (parameters width)).regN 1
def readData (width : Nat) : Reg width :=
  (readDataPipeline (parameters width)).regN 0
def readValid (width : Nat) : Reg 1 :=
  (readValidPipeline (parameters width)).regN 0

@[simp] theorem slot0_name (width : Nat) : (slot0 width).name = "slot_0" := by rfl
@[simp] theorem slot1_name (width : Nat) : (slot1 width).name = "slot_1" := by rfl
@[simp] theorem readSlot0_name (width : Nat) : (readSlot0 width).name = "slot_0" := by rfl
@[simp] theorem readSlot1_name (width : Nat) : (readSlot1 width).name = "slot_1" := by rfl

private theorem slotNamesDifferent :
    "slot_" ++ toString (0 : Nat) ≠ "slot_" ++ toString (1 : Nat) := by
  decide

@[simp] private theorem slotZeroText :
    "slot_" ++ toString (0 : Nat) = "slot_0" := by decide
@[simp] private theorem slotOneText :
    "slot_" ++ toString (1 : Nat) = "slot_1" := by decide

private theorem rangeTwo : List.range 2 = [0, 1] := by decide
private theorem rangeOne : List.range 1 = [0] := by decide

private def zeroState : St where
  regs := fun _ width => 0#width
  mems := fun _ _ width => 0#width

def writerInitial {width : Nat} (initial : Fin 2 → BitVec width) : St :=
  { zeroState with
    regs := (zeroState.regs.set (slot0 width).name (initial ⟨0, by simp⟩)).set
      (slot1 width).name (initial ⟨1, by simp⟩) }

def writerDrive {width : Nat} (event : Event (parameters width)) : InEnv :=
  let active := event.activeWrite
  fun name bits =>
    if name = writeEnable.name then
      if h : bits = 1 then h.symm ▸ (if active.isSome then 1#1 else 0#1) else 0
    else if name = (writeAddress (parameters width)).name then
      if h : bits = addressWidth (parameters width) then
        h.symm ▸ BitVec.ofNat _ (active.map (·.1.val) |>.getD 0)
      else 0
    else if name = (writeData (parameters width)).name then
      if h : bits = width then
        h.symm ▸ (active.map (·.2) |>.getD 0)
      else 0
    else 0

def readerDrive {width : Nat} (writer : St)
    (event : Event (parameters width)) : InEnv :=
  let active := event.activeRead
  fun name bits =>
    if name = (readSlot0 width).name then
      if h : bits = width then h.symm ▸ writer.regs (slot0 width).name width else 0
    else if name = (readSlot1 width).name then
      if h : bits = width then h.symm ▸ writer.regs (slot1 width).name width else 0
    else if name = readEnable.name then
      if h : bits = 1 then h.symm ▸ (if active.isSome then 1#1 else 0#1) else 0
    else if name = (readAddress (parameters width)).name then
      if h : bits = addressWidth (parameters width) then
        h.symm ▸ BitVec.ofNat _ (active.map (·.val) |>.getD 0)
      else 0
    else 0

structure State (width : Nat) where
  writer : St
  reader : St

def reset {width : Nat} (initial : Fin 2 → BitVec width) : State width where
  writer := writerInitial initial
  reader := (readerDesign (parameters width)).reset

def writerStep {width : Nat} (state : St) (event : Event (parameters width)) : St :=
  if event.writeTick then
    (writerDesign (parameters width)).cycleOpen (writerDrive event) state
  else state

def readerStep {width : Nat} (writer reader : St)
    (event : Event (parameters width)) : St :=
  if event.readTick then
    (readerDesign (parameters width)).cycleOpen (readerDrive writer event) reader
  else reader

def readResponse {width : Nat} (reader : St)
    (event : Event (parameters width)) : Option (BitVec width) :=
  if event.readTick && reader.regs (readValid width).name 1 = 1#1 then
    some (reader.regs (readData width).name width)
  else none

def step {width : Nat} (state : State width) (event : Event (parameters width)) :
    Result (State width) (parameters width) :=
  let writerNext := writerStep state.writer event
  let readerNext := readerStep state.writer state.reader event
  ⟨⟨writerNext, readerNext⟩, readResponse readerNext event⟩

structure Rep {width : Nat} (reference : ReferenceState (parameters width))
    (state : State width) : Prop where
  slot0 : state.writer.regs (slot0 width).name width =
    reference.memory ⟨0, by simp [parameters]⟩
  slot1 : state.writer.regs (slot1 width).name width =
    reference.memory ⟨1, by simp [parameters]⟩
  pipelineEmpty : reference.readPipeline = []

theorem reset_refines {width : Nat} (initial : Fin 2 → BitVec width) :
    Rep (⟨initial, []⟩ : ReferenceState (parameters width)) (reset initial) := by
  refine ⟨?_, ?_, rfl⟩
  · simp [reset, writerInitial, zeroState, RegEnv.set]
  · simp [reset, writerInitial, zeroState, RegEnv.set]

theorem writerStep_slot0 {width : Nat} (state : St)
    (event : Event (parameters width)) :
    (writerStep state event).regs (slot0 width).name width =
      match event.activeWrite with
      | some (address, value) => if address.val = 0 then value
          else state.regs (slot0 width).name width
      | none => state.regs (slot0 width).name width := by
  rcases event with ⟨writeTick, write, readTick, read⟩
  cases writeTick with
  | false => simp [writerStep, Event.activeWrite]
  | true =>
    cases write with
    | none =>
      simp [writerStep, writerDesign, writerDrive, Event.activeWrite,
        Design.cycleOpen, Design.cycle, Act.run, RegArray.dynSet, dynWrite,
        actSeq, Expr.eval, RegEnv.set, St.setInputs, parameters, addressWidth, slots,
        RegArray.regN,
        rangeTwo,
        writeEnable, writeAddress, writeData, Reg.input, Reg.rd]
    | some pair =>
      rcases pair with ⟨address, value⟩
      have addressBound : address.val < 2 := address.isLt
      have addressCases : address.val = 0 ∨ address.val = 1 := by omega
      rcases addressCases with addressZero | addressOne
      · have addressEq : address = ⟨0, by simp [parameters]⟩ := Fin.ext addressZero
        subst address
        simp [writerStep, writerDesign, writerDrive, Event.activeWrite,
          Design.cycleOpen, Design.cycle, Act.run, RegArray.dynSet, dynWrite,
          actSeq, Expr.eval, RegEnv.set, St.setInputs, parameters, addressWidth, slots,
          RegArray.regN,
          rangeTwo,
          writeEnable, writeAddress, writeData, Reg.input, Reg.rd]
      · have addressEq : address = ⟨1, by simp [parameters]⟩ := Fin.ext addressOne
        subst address
        simp [writerStep, writerDesign, writerDrive, Event.activeWrite,
          Design.cycleOpen, Design.cycle, Act.run, RegArray.dynSet, dynWrite,
          actSeq, Expr.eval, RegEnv.set, St.setInputs, parameters, addressWidth, slots,
          RegArray.regN,
          rangeTwo,
          writeEnable, writeAddress, writeData, Reg.input, Reg.rd]

theorem writerStep_slot1 {width : Nat} (state : St)
    (event : Event (parameters width)) :
    (writerStep state event).regs (slot1 width).name width =
      match event.activeWrite with
      | some (address, value) => if address.val = 1 then value
          else state.regs (slot1 width).name width
      | none => state.regs (slot1 width).name width := by
  rcases event with ⟨writeTick, write, readTick, read⟩
  cases writeTick with
  | false => simp [writerStep, Event.activeWrite]
  | true =>
    cases write with
    | none =>
      simp [writerStep, writerDesign, writerDrive, Event.activeWrite,
        Design.cycleOpen, Design.cycle, Act.run, RegArray.dynSet, dynWrite,
        actSeq, Expr.eval, RegEnv.set, St.setInputs, parameters, addressWidth, slots,
        RegArray.regN,
        rangeTwo,
        writeEnable, writeAddress, writeData, Reg.input, Reg.rd]
    | some pair =>
      rcases pair with ⟨address, value⟩
      have addressBound : address.val < 2 := address.isLt
      have addressCases : address.val = 0 ∨ address.val = 1 := by omega
      rcases addressCases with addressZero | addressOne
      · have addressEq : address = ⟨0, by simp [parameters]⟩ := Fin.ext addressZero
        subst address
        simp [writerStep, writerDesign, writerDrive, Event.activeWrite,
          Design.cycleOpen, Design.cycle, Act.run, RegArray.dynSet, dynWrite,
          actSeq, Expr.eval, RegEnv.set, St.setInputs, parameters, addressWidth, slots,
          RegArray.regN,
          rangeTwo,
          writeEnable, writeAddress, writeData, Reg.input, Reg.rd]
      · have addressEq : address = ⟨1, by simp [parameters]⟩ := Fin.ext addressOne
        subst address
        simp [writerStep, writerDesign, writerDrive, Event.activeWrite,
          Design.cycleOpen, Design.cycle, Act.run, RegArray.dynSet, dynWrite,
          actSeq, Expr.eval, RegEnv.set, St.setInputs, parameters, addressWidth, slots,
          RegArray.regN,
          rangeTwo,
          writeEnable, writeAddress, writeData, Reg.input, Reg.rd]

theorem readResponse_step {width : Nat} (writer reader : St)
    (event : Event (parameters width)) :
    readResponse (readerStep writer reader event) event =
      match event.activeRead with
      | some address => some (if address.val = 0 then
          writer.regs (slot0 width).name width
        else writer.regs (slot1 width).name width)
      | none => none := by
  rcases event with ⟨writeTick, write, readTick, read⟩
  cases readTick with
  | false => simp [readResponse, readerStep, Event.activeRead]
  | true =>
    cases read with
    | none =>
      simp [readResponse, readerStep, readerDesign, readerDrive, Event.activeRead,
        Design.cycleOpen, Design.cycle, Act.run, readPipelineActions, actSeq,
        Expr.eval, RegEnv.set, St.setInputs, parameters, addressWidth,
        readDataPipeline, readValidPipeline, readSample, readValid,
        readSlotInputs, RegArray.handles, RegArray.reg, RegArray.regN,
        List.finRange, readEnable, readAddress,
        Reg.input, Reg.rd, Reg.set]
    | some address =>
      have addressBound : address.val < 2 := address.isLt
      have addressCases : address.val = 0 ∨ address.val = 1 := by omega
      rcases addressCases with addressZero | addressOne
      · have addressEq : address = ⟨0, by simp [parameters]⟩ := Fin.ext addressZero
        subst address
        simp [readResponse, readerStep, readerDesign, readerDrive, Event.activeRead,
          Design.cycleOpen, Design.cycle, Act.run, readPipelineActions, actSeq,
          Expr.eval, RegEnv.set, St.setInputs, parameters, addressWidth,
          readDataPipeline, readValidPipeline, readSample, readData, readValid,
          readSlotInputs, RegArray.handles, RegArray.reg, RegArray.dynRd, dynRead,
          RegArray.regN, List.finRange,
          rangeTwo, readEnable, readAddress, Reg.input, Reg.rd, Reg.set,
          priTree_eval, priChain]
      · have addressEq : address = ⟨1, by simp [parameters]⟩ := Fin.ext addressOne
        subst address
        simp [readResponse, readerStep, readerDesign, readerDrive, Event.activeRead,
          Design.cycleOpen, Design.cycle, Act.run, readPipelineActions, actSeq,
          Expr.eval, RegEnv.set, St.setInputs, parameters, addressWidth,
          readDataPipeline, readValidPipeline, readSample, readData, readValid,
          readSlotInputs, RegArray.handles, RegArray.reg, RegArray.dynRd, dynRead,
          RegArray.regN, List.finRange,
          rangeTwo, readEnable, readAddress, Reg.input, Reg.rd, Reg.set,
          priTree_eval, priChain]

theorem referenceStep_pipeline_empty {width : Nat}
    (reference : ReferenceState (parameters width))
    (event : Event (parameters width)) (empty : reference.readPipeline = []) :
    (referenceStep reference event).state.readPipeline = [] := by
  cases tick : event.readTick <;>
    simp [referenceStep, tick, empty, advancePipeline, parameters]

theorem referenceStep_response {width : Nat}
    (reference : ReferenceState (parameters width))
    (event : Event (parameters width)) (empty : reference.readPipeline = []) :
    (referenceStep reference event).response = event.activeRead.map reference.memory := by
  cases tick : event.readTick <;> cases readEq : event.read <;>
    simp [referenceStep, Event.activeRead, tick, readEq, empty,
      advancePipeline, parameters]

theorem rep_step {width : Nat} (reference : ReferenceState (parameters width))
    (state : State width) (event : Event (parameters width))
    (rep : Rep reference state) :
    let expected := referenceStep reference event
    let actual := step state event
    Rep expected.state actual.state ∧ actual.response = expected.response := by
  dsimp only
  constructor
  · refine {
      slot0 := ?_
      slot1 := ?_
      pipelineEmpty := referenceStep_pipeline_empty reference event rep.pipelineEmpty }
    · change (writerStep state.writer event).regs (slot0 width).name width = _
      rw [writerStep_slot0, referenceStep_memory]
      cases writeEq : event.activeWrite with
      | none => simpa [writeMemory] using rep.slot0
      | some pair =>
          rcases pair with ⟨address, value⟩
          have addressBound : address.val < 2 := address.isLt
          have addressCases : address.val = 0 ∨ address.val = 1 := by omega
          rcases addressCases with addressZero | addressOne
          · have addressEq : address = ⟨0, by simp [parameters]⟩ := Fin.ext addressZero
            subst address
            simp [writeMemory]
          · have addressEq : address = ⟨1, by simp [parameters]⟩ := Fin.ext addressOne
            subst address
            simpa [writeMemory] using rep.slot0
    · change (writerStep state.writer event).regs (slot1 width).name width = _
      rw [writerStep_slot1, referenceStep_memory]
      cases writeEq : event.activeWrite with
      | none => simpa [writeMemory] using rep.slot1
      | some pair =>
          rcases pair with ⟨address, value⟩
          have addressBound : address.val < 2 := address.isLt
          have addressCases : address.val = 0 ∨ address.val = 1 := by omega
          rcases addressCases with addressZero | addressOne
          · have addressEq : address = ⟨0, by simp [parameters]⟩ := Fin.ext addressZero
            subst address
            simpa [writeMemory] using rep.slot1
          · have addressEq : address = ⟨1, by simp [parameters]⟩ := Fin.ext addressOne
            subst address
            simp [writeMemory]
  · change readResponse (readerStep state.writer state.reader event) event = _
    rw [readResponse_step, referenceStep_response reference event rep.pipelineEmpty]
    cases readEq : event.activeRead with
    | none => simp
    | some address =>
        have addressBound : address.val < 2 := address.isLt
        have addressCases : address.val = 0 ∨ address.val = 1 := by omega
        rcases addressCases with addressZero | addressOne
        · have addressEq : address = ⟨0, by simp [parameters]⟩ := Fin.ext addressZero
          subst address
          simpa using rep.slot0
        · have addressEq : address = ⟨1, by simp [parameters]⟩ := Fin.ext addressOne
          subst address
          simpa using rep.slot1

/-- Unconditional implementation whose state transitions and returned data
are the semantics of the compiler-produced writer/reader Designs above. -/
def implementation (width : Nat) : Implementation (parameters width) where
  State := State width
  reset := reset
  step := step
  Rep := Rep
  reset_refines := reset_refines
  step_refines := by
    intro reference concrete event _ rep
    exact rep_step reference concrete event rep

def binding (width : Nat) : Binding (parameters width) :=
  registerBankBinding (parameters width)
end DepthTwo

end Loom.Hw.Cdc.AsyncQueueStorage
