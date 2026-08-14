-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.AsyncQueueStorageDesign

namespace Loom.Hw.Cdc.AsyncQueueStorage.Portable

open Loom.Hw

/-- Shape of the technology-neutral compiled register bank. -/
structure Shape where
  width : Nat
  depth : Nat
  positive : 0 < depth

def Shape.parameters (shape : Shape) : Parameters where
  width := shape.width
  depth := shape.depth
  readLatency := 1
  depthPositive := shape.positive
  readLatencyPositive := by decide

def Shape.addressWidth (shape : Shape) : Nat :=
  AsyncQueueStorage.addressWidth shape.parameters

def slotName (i : Nat) : String :=
  String.ofList (List.replicate (i + 1) 's')

theorem slotName_length (i : Nat) : (slotName i).toList.length = i + 1 := by
  simp [slotName]

theorem slotName_injective : Function.Injective slotName := by
  intro i j equal
  have lengths := congrArg (fun name : String => name.toList.length) equal
  simpa [slotName] using lengths

def slot (shape : Shape) (i : Nat) : Reg shape.width := ⟨slotName i⟩

def writeEnable (shape : Shape) : Reg 1 := ⟨slotName shape.depth⟩
def writeAddress (shape : Shape) : Reg shape.addressWidth := ⟨slotName (shape.depth + 1)⟩
def writeData (shape : Shape) : Reg shape.width := ⟨slotName (shape.depth + 2)⟩
def readEnable (shape : Shape) : Reg 1 := ⟨slotName (shape.depth + 3)⟩
def readAddress (shape : Shape) : Reg shape.addressWidth := ⟨slotName (shape.depth + 4)⟩

def slotWrite (shape : Shape) (n : Nat) (idx : Expr shape.addressWidth)
    (value : Expr shape.width) : Act :=
  match n with
  | 0 => .skip
  | n + 1 => .seq (slotWrite shape n idx value)
      (.ite (.eq idx (.lit (BitVec.ofNat shape.addressWidth n)))
        (.write shape.width (slotName n) value) .skip)

def slotRead (shape : Shape) (n : Nat) (idx : Expr shape.addressWidth) :
    Expr shape.width :=
  match n with
  | 0 => .lit 0
  | n + 1 => .mux (.eq idx (.lit (BitVec.ofNat shape.addressWidth n)))
      (.reg shape.width (slotName n)) (slotRead shape n idx)

def readSample (shape : Shape) : Expr shape.width :=
  slotRead shape shape.depth (readAddress shape).rd

def writerDesign (shape : Shape) : Design where
  name := s!"async_queue_portable_writer_w{shape.width}_d{shape.depth}"
  regs := (List.range shape.depth).map (fun i => (slot shape i).decl)
  mems := []
  rules := [⟨"write", .ite (writeEnable shape).rd
    (slotWrite shape shape.depth (writeAddress shape).rd (writeData shape).rd) .skip⟩]
  inputs := [(writeEnable shape).input, (writeAddress shape).input,
    (writeData shape).input]
  outputs := (List.range shape.depth).map (fun i => (slot shape i).name)

/-- Portable first-word-fall-through read view. The selected slot is a
combinational output over ownership-protected register-bank inputs. There is
no hidden or unused response pipeline; `ChannelTiming.storageReadStages = 0`
describes this exact circuit. Registered RAM/SRAM leaves remain separate
implementations of the storage contract with their own reported latency. -/
def readerDesign (shape : Shape) : Design where
  name := s!"async_queue_portable_fwft_reader_w{shape.width}_d{shape.depth}"
  regs := []
  mems := []
  rules := []
  inputs := (List.range shape.depth).map (fun i => (slot shape i).input) ++
    [(readEnable shape).input, (readAddress shape).input]
  outputs := []
  combOutputs := [⟨"read_sample", shape.width, readSample shape⟩]

@[simp] theorem readerDesign_no_state (shape : Shape) :
    (readerDesign shape).regs = [] ∧ (readerDesign shape).rules = [] :=
  ⟨rfl, rfl⟩

private def writerInitial (shape : Shape)
    (initial : Fin shape.depth → BitVec shape.width) : St where
  regs := fun name bits =>
    if widthEq : bits = shape.width then
      if inRange : name.toList.length - 1 < shape.depth then
        widthEq.symm ▸ initial ⟨name.toList.length - 1, inRange⟩
      else 0
    else 0
  mems := fun _ _ bits => 0#bits

private def writerDrive (shape : Shape) (event : Event shape.parameters) : InEnv :=
  let active := event.activeWrite
  fun name bits =>
    if name = (writeEnable shape).name then
      if h : bits = 1 then h.symm ▸ (if active.isSome then 1#1 else 0#1) else 0
    else if name = (writeAddress shape).name then
      if h : bits = shape.addressWidth then
        h.symm ▸ BitVec.ofNat _ (active.map (·.1.val) |>.getD 0)
      else 0
    else if name = (writeData shape).name then
      if h : bits = shape.width then h.symm ▸ (active.map (·.2) |>.getD 0) else 0
    else 0

private def readerDrive (shape : Shape) (writer : St)
    (event : Event shape.parameters) : InEnv :=
  let active := event.activeRead
  fun name bits =>
    if name = (readEnable shape).name then
      if h : bits = 1 then h.symm ▸ (if active.isSome then 1#1 else 0#1) else 0
    else if name = (readAddress shape).name then
      if h : bits = shape.addressWidth then
        h.symm ▸ BitVec.ofNat _ (active.map (·.val) |>.getD 0)
      else 0
    else writer.regs name bits

structure State (shape : Shape) where
  writer : St
  reader : St

private def reset (shape : Shape)
    (initial : Fin shape.depth → BitVec shape.width) : State shape where
  writer := writerInitial shape initial
  reader := (readerDesign shape).reset

private def writerStep (shape : Shape) (state : St)
    (event : Event shape.parameters) : St :=
  if event.writeTick then
    (writerDesign shape).cycleOpen (writerDrive shape event) state
  else state

private def readerStep (shape : Shape) (writer reader : St)
    (event : Event shape.parameters) : St :=
  if event.readTick then
    (readerDesign shape).cycleOpen (readerDrive shape writer event) reader
  else reader

private def readResponse (shape : Shape) (writer reader : St)
    (event : Event shape.parameters) : Option (BitVec shape.width) :=
  if event.activeRead.isSome then
    some (readSample shape |>.eval
      (reader.setInputs (readerDesign shape).inputs (readerDrive shape writer event)))
  else none

private def step (shape : Shape) (state : State shape)
    (event : Event shape.parameters) : Result (State shape) shape.parameters :=
  let writerNext := writerStep shape state.writer event
  let readerNext := readerStep shape state.writer state.reader event
  ⟨⟨writerNext, readerNext⟩, readResponse shape state.writer state.reader event⟩

structure Rep (shape : Shape) (reference : ReferenceState shape.parameters)
    (state : State shape) : Prop where
  slots : ∀ address : Fin shape.depth,
    state.writer.regs (slotName address.val) shape.width = reference.memory address
  pipelineEmpty : reference.readPipeline = []

theorem depth_le_addressCapacity (shape : Shape) :
    shape.depth ≤ 2 ^ shape.addressWidth := by
  change shape.depth ≤ 2 ^ (Nat.log2 (shape.depth - 1) + 1)
  have lower := Nat.lt_log2_self (n := shape.depth - 1)
  omega

theorem bitvec_ofNat_injective {bits left right : Nat}
    (leftBound : left < 2 ^ bits) (rightBound : right < 2 ^ bits)
    (equal : BitVec.ofNat bits left = BitVec.ofNat bits right) : left = right := by
  have values := congrArg BitVec.toNat equal
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftBound,
    Nat.mod_eq_of_lt rightBound] using values

theorem slotWrite_preserve (shape : Shape) (sigma acc : St)
    (idx : Expr shape.addressWidth) (value : Expr shape.width)
    (n target : Nat) (outside : n ≤ target) :
    ((slotWrite shape n idx value).run sigma acc).regs
      (slotName target) shape.width = acc.regs (slotName target) shape.width := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have prior := ih (Nat.le_trans (Nat.le_succ n) outside)
      have different : slotName n ≠ slotName target := by
        apply slotName_injective.ne
        omega
      simp only [slotWrite, Act.run]
      split
      · change ((Act.run sigma (slotWrite shape n idx value) acc).regs.set
          (slotName n) (value.eval sigma)) (slotName target) shape.width = _
        rw [RegEnv.set_read_other]
        · exact prior
        · exact different.symm
      · exact prior

theorem slotWrite_at (shape : Shape) (sigma acc : St)
    (idx : Expr shape.addressWidth) (value : Expr shape.width)
    (n target : Nat) (inside : target < n) :
    ((slotWrite shape n idx value).run sigma acc).regs
      (slotName target) shape.width =
      if (.eq idx (.lit (BitVec.ofNat shape.addressWidth target)) : Expr 1).eval sigma = 1#1
      then value.eval sigma else acc.regs (slotName target) shape.width := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [slotWrite, Act.run]
      by_cases last : target = n
      · subst target
        split
        · simp
        · simpa using slotWrite_preserve shape sigma acc idx value n n (Nat.le_refl n)
      · have earlier : target < n := by omega
        have prior := ih earlier
        have different : slotName n ≠ slotName target :=
          slotName_injective.ne (Ne.symm last)
        split
        · change ((Act.run sigma (slotWrite shape n idx value) acc).regs.set
            (slotName n) (value.eval sigma)) (slotName target) shape.width = _
          rw [RegEnv.set_read_other]
          · exact prior
          · exact different.symm
        · exact prior

theorem slotRead_at (shape : Shape) (sigma : St)
    (idx : Expr shape.addressWidth) (n target : Nat) (inside : target < n)
    (capacity : n ≤ 2 ^ shape.addressWidth)
    (indexEq : idx.eval sigma = BitVec.ofNat shape.addressWidth target) :
    (slotRead shape n idx).eval sigma = sigma.regs (slotName target) shape.width := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [slotRead, Expr.eval]
      by_cases last : target = n
      · subst target
        simp [indexEq]
      · have earlier : target < n := by omega
        have targetBound : target < 2 ^ shape.addressWidth :=
          lt_of_lt_of_le earlier (Nat.le_trans (Nat.le_succ n) capacity)
        have nBound : n < 2 ^ shape.addressWidth :=
          lt_of_lt_of_le (Nat.lt_succ_self n) capacity
        have different : BitVec.ofNat shape.addressWidth target ≠
            BitVec.ofNat shape.addressWidth n := by
          intro equal
          exact last (bitvec_ofNat_injective targetBound nBound equal)
        rw [indexEq]
        simp [different, ih earlier (Nat.le_trans (Nat.le_succ n) capacity)]

theorem writerInitial_slot (shape : Shape)
    (initial : Fin shape.depth → BitVec shape.width) (address : Fin shape.depth) :
    (writerInitial shape initial).regs (slotName address.val) shape.width = initial address := by
  simp only [writerInitial, slotName_length]
  rw [dif_pos True.intro]
  have reduced : address.val + 1 - 1 = address.val := by omega
  simp only [reduced]
  rw [dif_pos address.isLt]

theorem reset_refines (shape : Shape)
    (initial : Fin shape.depth → BitVec shape.width) :
    Rep shape (⟨initial, []⟩ : ReferenceState shape.parameters)
      (reset shape initial) := by
  exact ⟨writerInitial_slot shape initial, rfl⟩

private theorem slotName_ne_writeEnable (shape : Shape) (i : Nat) :
    i < shape.depth → slotName i ≠ (writeEnable shape).name := by
  intro inside equal
  have same := slotName_injective equal
  simp at same
  omega

private theorem slotName_ne_writeAddress (shape : Shape) (i : Nat) :
    i < shape.depth → slotName i ≠ (writeAddress shape).name := by
  intro inside equal
  have same := slotName_injective equal
  simp at same
  omega

private theorem slotName_ne_writeData (shape : Shape) (i : Nat) :
    i < shape.depth → slotName i ≠ (writeData shape).name := by
  intro inside equal
  have same := slotName_injective equal
  simp at same
  omega

private theorem writerInputs_slot (shape : Shape) (state : St)
    (event : Event shape.parameters) (target : Nat) (inside : target < shape.depth) :
    (state.setInputs (writerDesign shape).inputs (writerDrive shape event)).regs
      (slotName target) shape.width = state.regs (slotName target) shape.width := by
  apply St.setInputs_regs_notin
  intro input member same
  simp only [writerDesign, List.mem_cons] at member
  rcases member with rfl | rfl | member
  · exact slotName_ne_writeEnable shape target inside (congrArg Prod.fst same)
  · exact slotName_ne_writeAddress shape target inside (congrArg Prod.fst same)
  · have inputEq : input = (writeData shape).input := by simpa using member
    subst input
    exact slotName_ne_writeData shape target inside (congrArg Prod.fst same)

private theorem writerInputs_enable (shape : Shape) (state : St)
    (event : Event shape.parameters) :
    (state.setInputs (writerDesign shape).inputs (writerDrive shape event)).regs
      (writeEnable shape).name 1 = if event.activeWrite.isSome then 1#1 else 0#1 := by
  have ea : (writeEnable shape).name ≠ (writeAddress shape).name := by
    apply slotName_injective.ne
    omega
  have ed : (writeEnable shape).name ≠ (writeData shape).name := by
    apply slotName_injective.ne
    omega
  simp only [writerDesign, St.setInputs, List.foldl_cons, List.foldl_nil, Reg.input]
  rw [RegEnv.set_read_other _ _ _ _ _ ed,
    RegEnv.set_read_other _ _ _ _ _ ea, RegEnv.set_read_self]
  simp [writerDrive]

private theorem writerInputs_address (shape : Shape) (state : St)
    (event : Event shape.parameters) :
    (state.setInputs (writerDesign shape).inputs (writerDrive shape event)).regs
      (writeAddress shape).name shape.addressWidth =
        BitVec.ofNat _ (event.activeWrite.map (·.1.val) |>.getD 0) := by
  have ad : (writeAddress shape).name ≠ (writeData shape).name := by
    apply slotName_injective.ne
    omega
  have ae : (writeAddress shape).name ≠ (writeEnable shape).name := by
    apply slotName_injective.ne
    omega
  simp only [writerDesign, St.setInputs, List.foldl_cons, List.foldl_nil, Reg.input]
  rw [RegEnv.set_read_other _ _ _ _ _ ad, RegEnv.set_read_self]
  simp [writerDrive, ae, Shape.parameters]

private theorem writerInputs_data (shape : Shape) (state : St)
    (event : Event shape.parameters) :
    (state.setInputs (writerDesign shape).inputs (writerDrive shape event)).regs
      (writeData shape).name shape.width =
        (event.activeWrite.map (fun pair => pair.2) |>.getD 0) := by
  have de : (writeData shape).name ≠ (writeEnable shape).name := by
    apply slotName_injective.ne
    omega
  have da : (writeData shape).name ≠ (writeAddress shape).name := by
    apply slotName_injective.ne
    omega
  simp only [writerDesign, St.setInputs, List.foldl_cons, List.foldl_nil, Reg.input]
  rw [RegEnv.set_read_self]
  simp [writerDrive, de, da, Shape.parameters]

theorem writerStep_slot (shape : Shape) (state : St)
    (event : Event shape.parameters) (target : Fin shape.depth) :
    (writerStep shape state event).regs (slotName target.val) shape.width =
      match event.activeWrite with
      | some (address, value) =>
          if address = target then value
          else state.regs (slotName target.val) shape.width
      | none => state.regs (slotName target.val) shape.width := by
  rcases event with ⟨writeTick, write, readTick, read⟩
  cases writeTick with
  | false => simp [writerStep, Event.activeWrite]
  | true =>
      cases write with
      | none =>
          let event : Event shape.parameters := ⟨true, none, readTick, read⟩
          let driven := state.setInputs (writerDesign shape).inputs
            (writerDrive shape event)
          change (if (writeEnable shape).rd.eval driven = 1#1 then
              (slotWrite shape shape.depth (writeAddress shape).rd
                (writeData shape).rd).run driven driven else driven).regs
                (slotName target.val) shape.width = _
          have enable : (writeEnable shape).rd.eval driven = 0#1 := by
            simpa [event, driven, Event.activeWrite] using
              writerInputs_enable shape state event
          rw [enable]
          exact writerInputs_slot shape state event target.val target.isLt
      | some pair =>
          rcases pair with ⟨address, value⟩
          let event : Event shape.parameters := ⟨true, some (address, value), readTick, read⟩
          let driven := state.setInputs (writerDesign shape).inputs
            (writerDrive shape event)
          change (if (writeEnable shape).rd.eval driven = 1#1 then
              (slotWrite shape shape.depth (writeAddress shape).rd
                (writeData shape).rd).run driven driven else driven).regs
                (slotName target.val) shape.width = _
          have enable : (writeEnable shape).rd.eval driven = 1#1 := by
            simpa [event, driven, Event.activeWrite] using
              writerInputs_enable shape state event
          rw [enable]
          simp only [if_true]
          rw [slotWrite_at shape driven driven (writeAddress shape).rd
            (writeData shape).rd shape.depth target.val target.isLt]
          have addressInput : (writeAddress shape).rd.eval driven =
              BitVec.ofNat shape.addressWidth address.val := by
            simpa [event, driven, Event.activeWrite] using
              writerInputs_address shape state event
          have dataInput : (writeData shape).rd.eval driven = value := by
            simpa [event, driven, Event.activeWrite] using
              writerInputs_data shape state event
          have targetState := writerInputs_slot shape state event target.val target.isLt
          by_cases same : address = target
          · subst address
            simp [Expr.eval, addressInput, dataInput, Event.activeWrite]
          · have addressBound : address.val < 2 ^ shape.addressWidth :=
              lt_of_lt_of_le address.isLt (depth_le_addressCapacity shape)
            have targetBound : target.val < 2 ^ shape.addressWidth :=
              lt_of_lt_of_le target.isLt (depth_le_addressCapacity shape)
            have different : BitVec.ofNat shape.addressWidth address.val ≠
                BitVec.ofNat shape.addressWidth target.val := by
              intro equal
              apply same
              apply Fin.ext
              exact bitvec_ofNat_injective addressBound targetBound equal
            simp [Expr.eval, addressInput, Event.activeWrite,
              same, different]
            simpa [driven] using targetState

private theorem slotName_ne_readEnable (shape : Shape) (i : Nat)
    (inside : i < shape.depth) : slotName i ≠ (readEnable shape).name := by
  intro equal
  have same := slotName_injective equal
  simp at same
  omega

private theorem slotName_ne_readAddress (shape : Shape) (i : Nat)
    (inside : i < shape.depth) : slotName i ≠ (readAddress shape).name := by
  intro equal
  have same := slotName_injective equal
  simp at same
  omega

private theorem readerDrive_slot (shape : Shape) (writer : St)
    (event : Event shape.parameters) (target : Nat) (inside : target < shape.depth) :
    readerDrive shape writer event (slotName target) shape.width =
      writer.regs (slotName target) shape.width := by
  simp [readerDrive, slotName_ne_readEnable shape target inside,
    slotName_ne_readAddress shape target inside]

private def installSlotInputs (shape : Shape) (writer : St)
    (event : Event shape.parameters) (n : Nat) (regs : RegEnv) : RegEnv :=
  ((List.range n).map (fun i => (slot shape i).input)).foldl
    (fun acc input => acc.set input.name
      (readerDrive shape writer event input.name input.width)) regs

private theorem installSlotInputs_preserve (shape : Shape) (writer : St)
    (event : Event shape.parameters) (n target : Nat) (outside : n ≤ target)
    (regs : RegEnv) :
    installSlotInputs shape writer event n regs (slotName target) shape.width =
      regs (slotName target) shape.width := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have prior := ih (Nat.le_trans (Nat.le_succ n) outside)
      have different : slotName target ≠ slotName n := by
        apply slotName_injective.ne
        omega
      simp only [installSlotInputs, List.range_succ, List.map_append,
        List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Reg.input, slot]
      rw [RegEnv.set_read_other]
      · simpa [installSlotInputs] using prior
      · exact different

private theorem installSlotInputs_at (shape : Shape) (writer : St)
    (event : Event shape.parameters) (n target : Nat) (inside : target < n)
    (withinDepth : n ≤ shape.depth) (regs : RegEnv) :
    installSlotInputs shape writer event n regs (slotName target) shape.width =
      writer.regs (slotName target) shape.width := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [installSlotInputs, List.range_succ, List.map_append,
        List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Reg.input, slot]
      by_cases last : target = n
      · subst target
        rw [RegEnv.set_read_self]
        exact readerDrive_slot shape writer event n (by omega)
      · have earlier : target < n := by omega
        have different : slotName target ≠ slotName n :=
          slotName_injective.ne last
        rw [RegEnv.set_read_other]
        · simpa [installSlotInputs] using ih earlier (by omega)
        · exact different

private theorem readerInputs_slot (shape : Shape) (writer reader : St)
    (event : Event shape.parameters) (target : Fin shape.depth) :
    (reader.setInputs (readerDesign shape).inputs
      (readerDrive shape writer event)).regs (slotName target.val) shape.width =
      writer.regs (slotName target.val) shape.width := by
  simp only [readerDesign, St.setInputs, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Reg.input]
  rw [RegEnv.set_read_other]
  · rw [RegEnv.set_read_other]
    · exact installSlotInputs_at shape writer event shape.depth target.val
        target.isLt (Nat.le_refl _) reader.regs
    · exact slotName_ne_readEnable shape target.val target.isLt
  · exact slotName_ne_readAddress shape target.val target.isLt

private theorem readerInputs_enable (shape : Shape) (writer reader : St)
    (event : Event shape.parameters) :
    (reader.setInputs (readerDesign shape).inputs
      (readerDrive shape writer event)).regs (readEnable shape).name 1 =
      if event.activeRead.isSome then 1#1 else 0#1 := by
  have different : (readEnable shape).name ≠ (readAddress shape).name := by
    apply slotName_injective.ne
    omega
  simp only [readerDesign, St.setInputs, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Reg.input]
  rw [RegEnv.set_read_other]
  · rw [RegEnv.set_read_self]
    simp [readerDrive]
  · exact different

private theorem readerInputs_address (shape : Shape) (writer reader : St)
    (event : Event shape.parameters) :
    (reader.setInputs (readerDesign shape).inputs
      (readerDrive shape writer event)).regs
      (readAddress shape).name shape.addressWidth =
      BitVec.ofNat shape.addressWidth (event.activeRead.map (·.val) |>.getD 0) := by
  simp only [readerDesign, St.setInputs, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Reg.input]
  rw [RegEnv.set_read_self]
  have different : (readAddress shape).name ≠ (readEnable shape).name := by
    apply slotName_injective.ne
    omega
  simp [readerDrive, different]

theorem readResponse_step (shape : Shape) (writer reader : St)
    (event : Event shape.parameters) :
    readResponse shape writer reader event =
      match event.activeRead with
      | some address => some (writer.regs (slotName address.val) shape.width)
      | none => none := by
  cases active : event.activeRead with
  | none => simp [readResponse, active]
  | some address =>
      let driven := reader.setInputs (readerDesign shape).inputs
        (readerDrive shape writer event)
      have addressInput : (readAddress shape).rd.eval driven =
          BitVec.ofNat shape.addressWidth address.val := by
        simpa [driven, active] using readerInputs_address shape writer reader event
      have selected := slotRead_at shape driven (readAddress shape).rd
        shape.depth address.val address.isLt (depth_le_addressCapacity shape)
        addressInput
      have slotInput := readerInputs_slot shape writer reader event address
      have selectedValue :
          (slotRead shape shape.depth (readAddress shape).rd).eval driven =
            writer.regs (slotName address.val) shape.width := by
        rw [selected]
        simpa [driven] using slotInput
      simp [readResponse, active, readSample, driven, selectedValue]

theorem referenceStep_pipeline_empty (shape : Shape)
    (reference : ReferenceState shape.parameters) (event : Event shape.parameters)
    (empty : reference.readPipeline = []) :
    (referenceStep reference event).state.readPipeline = [] := by
  cases tick : event.readTick <;>
    simp [referenceStep, tick, empty, advancePipeline, Shape.parameters]

theorem referenceStep_response (shape : Shape)
    (reference : ReferenceState shape.parameters) (event : Event shape.parameters)
    (empty : reference.readPipeline = []) :
    (referenceStep reference event).response = event.activeRead.map reference.memory := by
  cases tick : event.readTick <;> cases readEq : event.read <;>
    simp [referenceStep, Event.activeRead, tick, readEq, empty,
      advancePipeline, Shape.parameters]

theorem rep_step (shape : Shape) (reference : ReferenceState shape.parameters)
    (state : State shape) (event : Event shape.parameters)
    (rep : Rep shape reference state) :
    let expected := referenceStep reference event
    let actual := step shape state event
    Rep shape expected.state actual.state ∧ actual.response = expected.response := by
  dsimp only
  constructor
  · refine {
      slots := ?_
      pipelineEmpty := referenceStep_pipeline_empty shape reference event rep.pipelineEmpty }
    intro target
    change (writerStep shape state.writer event).regs
      (slotName target.val) shape.width = _
    rw [writerStep_slot shape state.writer event target, referenceStep_memory]
    cases writeEq : event.activeWrite with
    | none => simpa [writeMemory, writeEq] using rep.slots target
    | some pair =>
        rcases pair with ⟨address, value⟩
        by_cases same : address = target
        · subst address
          simp [writeMemory]
        · simpa [writeEq, writeMemory, same, Ne.symm same] using rep.slots target
  · change readResponse shape state.writer state.reader event = _
    rw [readResponse_step shape, referenceStep_response shape reference event rep.pipelineEmpty]
    cases readEq : event.activeRead with
    | none => simp
    | some address => simpa using rep.slots address

/-- Unconditional compiled register-bank implementation for every positive
depth. The concrete transition is exactly the two ordinary Designs above. -/
def implementation (shape : Shape) : Implementation shape.parameters where
  State := State shape
  reset := reset shape
  step := step shape
  Rep := Rep shape
  reset_refines := reset_refines shape
  step_refines := by
    intro reference concrete event _ rep
    exact rep_step shape reference concrete event rep

private theorem regEnv_set_zero (name : String) (width : Nat) :
    RegEnv.set (fun _ bits => 0#bits) name (0#width) =
      (fun _ bits => 0#bits) := by
  funext candidate bits
  unfold RegEnv.set
  split
  · split
    · subst candidate
      subst bits
      rfl
    · rfl
  · rfl

private theorem resetFold_all_zero (decls : List RegDecl)
    (allZero : ∀ decl ∈ decls, decl.init = 0#decl.width) :
    decls.foldl (fun (state : RegEnv) decl =>
      RegEnv.set state decl.name decl.init)
        (fun _ bits => 0#bits) =
      (fun _ bits => 0#bits) := by
  induction decls with
  | nil => rfl
  | cons head tail ih =>
      rw [List.foldl_cons, allZero head (List.mem_cons_self),
        regEnv_set_zero]
      exact ih (fun decl member =>
        allZero decl (List.mem_cons_of_mem head member))

/-- The all-zero initialization used by the portable FIFO packages exactly
the ordinary writer `Design` reset state. This connects the storage contract's
parameterized reset to the compiled wrapper's asserted reset edge. -/
theorem implementation_reset_writer_zero (shape : Shape) :
    ((implementation shape).reset (fun _ => 0)).writer =
      (writerDesign shape).reset := by
  apply congrArg₂ St.mk
  · change (writerInitial shape (fun _ => 0)).regs = _
    rw [resetFold_all_zero]
    · funext name width
      change (if widthEq : width = shape.width then
          if inRange : name.toList.length - 1 < shape.depth then
            widthEq.symm ▸ (0#shape.width)
          else 0#width
        else 0#width) = 0#width
      split
      · subst width
        split <;> rfl
      · rfl
    · intro decl member
      simp [writerDesign] at member
      rcases member with ⟨index, _, rfl⟩
      rfl
  · rfl

def binding (shape : Shape) : Binding shape.parameters :=
  registerBankBinding shape.parameters

/-- Compiler/simulator readiness for both exact Designs used by the portable
storage implementation. -/
def compilerReady (shape : Shape) : Prop :=
  Compile.designWFCheck (writerDesign shape) = true ∧
  Compile.designWFCheck (readerDesign shape) = true ∧
  (writerDesign shape).fastWFB = true ∧ (readerDesign shape).fastWFB = true

/-- Exact compiler/DAG/byte packages for the two Designs whose cycle semantics
define `implementation`. -/
structure CertifiedDesigns (shape : Shape) where
  writer : CertifiedDesign (writerDesign shape)
  reader : CertifiedDesign (readerDesign shape)

def certify (shape : Shape) (ready : compilerReady shape) : CertifiedDesigns shape :=
  let writerBase : FastEval.VerifiedSimulator (writerDesign shape) := ⟨ready.2.2.1⟩
  let readerBase : FastEval.VerifiedSimulator (readerDesign shape) := ⟨ready.2.2.2⟩
  let writerDag := DagEval.verifiedSimulatorOfPreparation writerBase
    (DagEval.prepareSimulator?_complete writerBase)
  let readerDag := DagEval.verifiedSimulatorOfPreparation readerBase
    (DagEval.prepareSimulator?_complete readerBase)
  { writer := .of (Compile.designWFCheck_sound _ ready.1) writerDag
    reader := .of (Compile.designWFCheck_sound _ ready.2.1) readerDag }

end Loom.Hw.Cdc.AsyncQueueStorage.Portable
