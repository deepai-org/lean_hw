-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SoCFabricGauntlet.Design
import Loom.Hw.Footprint
import Loom.Hw.Frame
import Loom.Hw.TraceContract

/-!
# Schedule-independent SoC Fabric Gauntlet proof surface

This file separates the pure register-service model from observations of a
finite `System` execution.  A finite cut may contain transactions in flight,
so unconditional results use conservation/prefix statements; equality after
drain is a progress corollary, not a safety premise.
-/

namespace Machines.Multiclock.SoCFabricGauntlet

open Loom.Hw

def noInputs : ExternalInputs :=
  fun _ island name width =>
    if (island = "cpu" || island = "dma") && name = "transaction_limit" then
      BitVec.ofNat width transactionCount
    else 0

/-! ## Pure transaction model -/

abbrev RegisterModel := BitVec 8 → BitVec 32

def initialMemory : RegisterModel := fun _ => 0

/-- The literal bit-vector algebra implemented by `maskedWord`. -/
def applyByteMask (old data : BitVec 32) (mask : BitVec 4) : BitVec 32 :=
  let choose (index : Nat) : BitVec 8 :=
    if mask.extractLsb' index 1 = 1#1 then data.extractLsb' (8 * index) 8
    else old.extractLsb' (8 * index) 8
  Loom.Word.insert 24 (choose 3) <|
    Loom.Word.insert 16 (choose 2) <|
      Loom.Word.insert 8 (choose 1) <| Loom.Word.insert 0 (choose 0) old

/-- Masked writes choose each byte independently.  This is the selected-byte
semantic obligation, rather than merely an equality between two flat words. -/
theorem applyByteMask_byte (old data : BitVec 32) (mask : BitVec 4)
    (index : Fin 4) :
    (applyByteMask old data mask).extractLsb' (8 * index.val) 8 =
      if mask.extractLsb' index.val 1 = 1#1 then
        data.extractLsb' (8 * index.val) 8
      else old.extractLsb' (8 * index.val) 8 := by
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by
    omega
  rcases choices with rfl | rfl | rfl | rfl
  · change (applyByteMask old data mask).extractLsb' 0 8 =
      if mask.extractLsb' 0 1 = 1#1 then data.extractLsb' 0 8
      else old.extractLsb' 0 8
    simp only [applyByteMask]
    change Loom.Word.extract 0 8 _ = _
    rw [Loom.Word.extract_insert_of_disjoint _ _ (by omega) (by omega)]
    rw [Loom.Word.extract_insert_of_disjoint _ _ (by omega) (by omega)]
    rw [Loom.Word.extract_insert_of_disjoint _ _ (by omega) (by omega)]
    rw [Loom.Word.extract_insert_self _ _ _ (by omega)]
  · change (applyByteMask old data mask).extractLsb' 8 8 =
      if mask.extractLsb' 1 1 = 1#1 then data.extractLsb' 8 8
      else old.extractLsb' 8 8
    simp only [applyByteMask]
    change Loom.Word.extract 8 8 _ = _
    rw [Loom.Word.extract_insert_of_disjoint _ _ (by omega) (by omega)]
    rw [Loom.Word.extract_insert_of_disjoint _ _ (by omega) (by omega)]
    rw [Loom.Word.extract_insert_self _ _ _ (by omega)]
  · change (applyByteMask old data mask).extractLsb' 16 8 =
      if mask.extractLsb' 2 1 = 1#1 then data.extractLsb' 16 8
      else old.extractLsb' 16 8
    simp only [applyByteMask]
    change Loom.Word.extract 16 8 _ = _
    rw [Loom.Word.extract_insert_of_disjoint _ _ (by omega) (by omega)]
    rw [Loom.Word.extract_insert_self _ _ _ (by omega)]
  · change (applyByteMask old data mask).extractLsb' 24 8 =
      if mask.extractLsb' 3 1 = 1#1 then data.extractLsb' 24 8
      else old.extractLsb' 24 8
    simp only [applyByteMask]
    change Loom.Word.extract 24 8 _ = _
    rw [Loom.Word.extract_insert_self _ _ _ (by omega)]

private theorem four_bytes_reconstruct (word : BitVec 32) :
    word.extractLsb' 24 8 ++
      (word.extractLsb' 16 8 ++
        (word.extractLsb' 8 8 ++ word.extractLsb' 0 8)) = word := by
  apply BitVec.eq_of_getLsbD_eq
  intro index inBounds
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases low24 : index < 24
  · simp only [low24, if_true]
    by_cases low16 : index < 16
    · simp only [low16, if_true]
      by_cases low8 : index < 8
      · simp [low8]
      · have arithmetic : 8 + (index - 8) = index := by omega
        have byteBound : index - 8 < 8 := by omega
        simp [low8, arithmetic, byteBound]
    · have arithmetic : 16 + (index - 16) = index := by omega
      have byteBound : index - 16 < 8 := by omega
      simp [low16, arithmetic, byteBound]
  · have arithmetic : 24 + (index - 24) = index := by omega
    have byteBound : index - 24 < 8 := by omega
    simp [low24, arithmetic, byteBound]

theorem maskedWord_correct (old data : Expr 32) (mask : Expr 4) (state : St) :
    (maskedWord old data mask).eval state =
      applyByteMask (old.eval state) (data.eval state) (mask.eval state) := by
  simp only [maskedWord, Expr.concat_eval, Expr.eval]
  let result := applyByteMask (old.eval state) (data.eval state) (mask.eval state)
  have byte0 := applyByteMask_byte (old.eval state) (data.eval state)
    (mask.eval state) (0 : Fin 4)
  have byte1 := applyByteMask_byte (old.eval state) (data.eval state)
    (mask.eval state) (1 : Fin 4)
  have byte2 := applyByteMask_byte (old.eval state) (data.eval state)
    (mask.eval state) (2 : Fin 4)
  have byte3 := applyByteMask_byte (old.eval state) (data.eval state)
    (mask.eval state) (3 : Fin 4)
  change result.extractLsb' 0 8 =
    (if (mask.eval state).extractLsb' 0 1 = 1#1 then
      (data.eval state).extractLsb' 0 8 else
      (old.eval state).extractLsb' 0 8) at byte0
  change result.extractLsb' 8 8 =
    (if (mask.eval state).extractLsb' 1 1 = 1#1 then
      (data.eval state).extractLsb' 8 8 else
      (old.eval state).extractLsb' 8 8) at byte1
  change result.extractLsb' 16 8 =
    (if (mask.eval state).extractLsb' 2 1 = 1#1 then
      (data.eval state).extractLsb' 16 8 else
      (old.eval state).extractLsb' 16 8) at byte2
  change result.extractLsb' 24 8 =
    (if (mask.eval state).extractLsb' 3 1 = 1#1 then
      (data.eval state).extractLsb' 24 8 else
      (old.eval state).extractLsb' 24 8) at byte3
  change _ = result
  rw [← byte0, ← byte1, ← byte2, ← byte3]
  exact four_bytes_reconstruct result

def applyRequest (memory : RegisterModel) (request : Request) :
    RegisterModel × Response × CommitRecord :=
  let old := memory request.addr
  let result := if request.write = 1#1 then
      applyByteMask old request.data request.mask else old
  let next := if request.write = 1#1 then
      fun address => if address = request.addr then result else memory address
    else memory
  (next,
    { client := request.client, tag := request.tag, data := result, error := 0 },
    { client := request.client, tag := request.tag, addr := request.addr,
      write := request.write, result := result })

def applyRequests : RegisterModel → List Request →
    RegisterModel × List Response × List CommitRecord
  | memory, [] => (memory, [], [])
  | memory, request :: rest =>
      let one := applyRequest memory request
      let later := applyRequests one.1 rest
      (later.1, one.2.1 :: later.2.1, one.2.2 :: later.2.2)

def committedMemory (requests : List Request) : RegisterModel :=
  (applyRequests initialMemory requests).1

def modelResponses (requests : List Request) : List Response :=
  (applyRequests initialMemory requests).2.1

def modelCommits (requests : List Request) : List CommitRecord :=
  (applyRequests initialMemory requests).2.2

@[simp] theorem applyRequest_response_client (memory : RegisterModel)
    (request : Request) : (applyRequest memory request).2.1.client = request.client := by
  simp [applyRequest]

@[simp] theorem applyRequest_response_tag (memory : RegisterModel)
    (request : Request) : (applyRequest memory request).2.1.tag = request.tag := by
  simp [applyRequest]

@[simp] theorem applyRequest_response_ok (memory : RegisterModel)
    (request : Request) : (applyRequest memory request).2.1.error = 0 := by
  simp [applyRequest]

@[simp] theorem applyRequest_commit_identity (memory : RegisterModel)
    (request : Request) :
    let record := (applyRequest memory request).2.2
    record.client = request.client ∧ record.tag = request.tag ∧
      record.addr = request.addr ∧ record.write = request.write := by
  simp [applyRequest]

private theorem applyRequests_response_length (memory : RegisterModel)
    (requests : List Request) :
    (applyRequests memory requests).2.1.length = requests.length := by
  induction requests generalizing memory with
  | nil => rfl
  | cons request rest ih =>
      simp [applyRequests, ih]

theorem modelResponses_length (requests : List Request) :
    (modelResponses requests).length = requests.length := by
  exact applyRequests_response_length initialMemory requests

def ResponseMatchesRequest (request : Request) (response : Response) : Prop :=
  response.client = request.client ∧ response.tag = request.tag ∧
    response.error = 0#1

theorem applyRequests_responses_match (memory : RegisterModel)
    (requests : List Request) :
    List.Forall₂ ResponseMatchesRequest requests
      (applyRequests memory requests).2.1 := by
  induction requests generalizing memory with
  | nil => simp [applyRequests]
  | cons request rest ih =>
      simp only [applyRequests]
      apply List.Forall₂.cons
      · simp [ResponseMatchesRequest, applyRequest]
      · exact ih (applyRequest memory request).1

theorem modelResponses_match (requests : List Request) :
    List.Forall₂ ResponseMatchesRequest requests (modelResponses requests) := by
  exact applyRequests_responses_match initialMemory requests

/-! ## Register-service action refinement

These lemmas cross the important boundary from the pure model above to the
literal action used by the service island.  They are the local step facts used
by the remaining composed-history induction. -/

def serviceRequestAt (state : St) : Request := targetRequest.deq.eval state

def serviceResultAt (state : St) : BitVec 32 :=
  let request := serviceRequestAt state
  let old := state.mems registerFile.name request.addr.toNat 32
  if request.write = 1#1 then applyByteMask old request.data request.mask else old

def serviceResponseAt (state : St) : Response :=
  let request := serviceRequestAt state
  { client := request.client, tag := request.tag, data := serviceResultAt state,
    error := 0 }

def serviceCommitAt (state : St) : CommitRecord :=
  let request := serviceRequestAt state
  { client := request.client, tag := request.tag, addr := request.addr,
    write := request.write, result := serviceResultAt state }

@[simp] theorem request_clientField_get (value : Request) :
    Request.clientField.get value = value.client := by
  simpa [Request.clientField, PackedField.get, HwPackedLayout.fieldAt,
    PackedLayout.fieldAt, instHwPackedLayoutRequest, instHwPackedRequest,
    requestLayout] using
    congrArg Request.client (HwPacked.unpack_pack value)

@[simp] theorem request_tagField_get (value : Request) :
    Request.tagField.get value = value.tag := by
  simpa [Request.tagField, PackedField.get, HwPackedLayout.fieldAt,
    PackedLayout.fieldAt, instHwPackedLayoutRequest, instHwPackedRequest,
    requestLayout] using
    congrArg Request.tag (HwPacked.unpack_pack value)

@[simp] theorem request_writeField_get (value : Request) :
    Request.writeField.get value = value.write := by
  simpa [Request.writeField, PackedField.get, HwPackedLayout.fieldAt,
    PackedLayout.fieldAt, instHwPackedLayoutRequest, instHwPackedRequest,
    requestLayout] using
    congrArg Request.write (HwPacked.unpack_pack value)

@[simp] theorem request_addrField_get (value : Request) :
    Request.addrField.get value = value.addr := by
  simpa [Request.addrField, PackedField.get, HwPackedLayout.fieldAt,
    PackedLayout.fieldAt, instHwPackedLayoutRequest, instHwPackedRequest,
    requestLayout] using
    congrArg Request.addr (HwPacked.unpack_pack value)

@[simp] theorem request_dataField_get (value : Request) :
    Request.dataField.get value = value.data := by
  simpa [Request.dataField, PackedField.get, HwPackedLayout.fieldAt,
    PackedLayout.fieldAt, instHwPackedLayoutRequest, instHwPackedRequest,
    requestLayout] using
    congrArg Request.data (HwPacked.unpack_pack value)

@[simp] theorem request_maskField_get (value : Request) :
    Request.maskField.get value = value.mask := by
  simpa [Request.maskField, PackedField.get, HwPackedLayout.fieldAt,
    PackedLayout.fieldAt, instHwPackedLayoutRequest, instHwPackedRequest,
    requestLayout] using
    congrArg Request.mask (HwPacked.unpack_pack value)

theorem serviceCommit_emits_response (state acc : St)
    (requestReady : targetRequest.bits.canDeq.eval state = 1#1)
    (responseReady : targetResponse.bits.canEnq.eval state = 1#1)
    (auditReady : audit.bits.canEnq.eval state = 1#1) :
    HwPacked.unpack ((serviceCommit.run state acc).regs
      targetResponse.bits.sourcePayloadName (HwPacked.width Response)) =
      serviceResponseAt state := by
  simp [targetRequest, PackedChan.named, Chan.canDeq, Chan.sinkPopName,
    Chan.sinkValidName, Chan.stem, Expr.eval] at requestReady
  simp only [serviceCommit, PackedChan.enq, Chan.enq]
  simp only [Act.run]
  rw [responseReady, auditReady]
  simp [Act.run, PackedChan.pop, Chan.pop, targetResponse, audit, targetRequest,
    PackedChan.named, Chan.canDeq, Chan.sinkPopName, Chan.sinkValidName,
    Chan.sourcePayloadName, Chan.sourceValidName, Chan.stem, PackedChan.deq,
    Chan.deq, Mem.write, Mem.rd, registerFile,
    responseExpr, serviceResponseAt,
    serviceResultAt, serviceRequestAt, PackedExpr.eval, PackedExpr.ofFields,
    PackedFields.bits, Expr.concat_eval, Expr.eval, PackedField.read_eval,
    maskedWord_correct, requestReady]
  change HwPacked.unpack (HwPacked.pack (serviceResponseAt state)) =
    serviceResponseAt state
  exact HwPacked.unpack_pack _

theorem serviceCommit_emits_audit (state acc : St)
    (requestReady : targetRequest.bits.canDeq.eval state = 1#1)
    (responseReady : targetResponse.bits.canEnq.eval state = 1#1)
    (auditReady : audit.bits.canEnq.eval state = 1#1) :
    HwPacked.unpack ((serviceCommit.run state acc).regs
      audit.bits.sourcePayloadName (HwPacked.width CommitRecord)) =
      serviceCommitAt state := by
  simp [targetRequest, PackedChan.named, Chan.canDeq, Chan.sinkPopName,
    Chan.sinkValidName, Chan.stem, Expr.eval] at requestReady
  simp only [serviceCommit, PackedChan.enq, Chan.enq]
  simp only [Act.run]
  rw [responseReady, auditReady]
  simp [Act.run, PackedChan.pop, Chan.pop, targetResponse, audit, targetRequest,
    PackedChan.named, Chan.canDeq, Chan.sinkPopName, Chan.sinkValidName,
    Chan.sourcePayloadName, Chan.sourceValidName, Chan.stem, PackedChan.deq,
    Chan.deq, Mem.write, Mem.rd, registerFile, commitExpr, serviceCommitAt,
    serviceResultAt, serviceRequestAt, PackedExpr.eval, PackedExpr.ofFields,
    PackedFields.bits, Expr.concat_eval, Expr.eval, PackedField.read_eval,
    maskedWord_correct, requestReady]
  change HwPacked.unpack (HwPacked.pack (serviceCommitAt state)) =
    serviceCommitAt state
  exact HwPacked.unpack_pack _

@[simp] theorem commitExpr_eval_eq_serviceCommitAt (state : St) :
    HwPacked.unpack ((commitExpr targetRequest.deq
      ((Request.writeField.read targetRequest.deq).mux
        (maskedWord (registerFile.rd (Request.addrField.read targetRequest.deq))
          (Request.dataField.read targetRequest.deq)
          (Request.maskField.read targetRequest.deq))
        (registerFile.rd (Request.addrField.read targetRequest.deq)))).bits.eval state) =
      serviceCommitAt state := by
  simp [commitExpr, serviceCommitAt, serviceResultAt, serviceRequestAt,
    PackedExpr.eval, PackedExpr.ofFields, PackedFields.bits, Expr.concat_eval,
    Expr.eval, PackedField.read_eval, maskedWord_correct, Mem.rd, registerFile,
    targetRequest, PackedChan.named, PackedChan.deq, Chan.deq,
    Chan.sinkPayloadName, Chan.stem]
  change HwPacked.unpack (HwPacked.pack (serviceCommitAt state)) =
    serviceCommitAt state
  exact HwPacked.unpack_pack _

@[simp] theorem responseExpr_eval_eq_serviceResponseAt (state : St) :
    HwPacked.unpack ((responseExpr targetRequest.deq
      ((Request.writeField.read targetRequest.deq).mux
        (maskedWord (registerFile.rd (Request.addrField.read targetRequest.deq))
          (Request.dataField.read targetRequest.deq)
          (Request.maskField.read targetRequest.deq))
        (registerFile.rd (Request.addrField.read targetRequest.deq)))).bits.eval state) =
      serviceResponseAt state := by
  simp [responseExpr, serviceResponseAt, serviceResultAt, serviceRequestAt,
    PackedExpr.eval, PackedExpr.ofFields, PackedFields.bits, Expr.concat_eval,
    Expr.eval, PackedField.read_eval, maskedWord_correct, Mem.rd, registerFile,
    targetRequest, PackedChan.named, PackedChan.deq, Chan.deq,
    Chan.sinkPayloadName, Chan.stem]
  change HwPacked.unpack (HwPacked.pack (serviceResponseAt state)) =
    serviceResponseAt state
  exact HwPacked.unpack_pack _

def serviceMemoryAt (state : St) : RegisterModel :=
  fun address => state.mems registerFile.name address.toNat 32

theorem serviceResponseAt_eq_model (state : St) :
    serviceResponseAt state =
      (applyRequest (serviceMemoryAt state) (serviceRequestAt state)).2.1 := by
  simp [serviceResponseAt, serviceResultAt, serviceMemoryAt, applyRequest]

theorem serviceCommitAt_eq_model (state : St) :
    serviceCommitAt state =
      (applyRequest (serviceMemoryAt state) (serviceRequestAt state)).2.2 := by
  simp [serviceCommitAt, serviceResultAt, serviceMemoryAt, applyRequest]

theorem serviceCommit_memory_refines (state acc : St)
    (sameMemory : serviceMemoryAt acc = serviceMemoryAt state)
    (address : BitVec 8) :
    serviceMemoryAt (serviceCommit.run state acc) address =
      (applyRequest (serviceMemoryAt state) (serviceRequestAt state)).1 address := by
  let request := targetRequest.deq
  let old := registerFile.rd (Request.addrField.read request)
  let updated := maskedWord old (Request.dataField.read request)
    (Request.maskField.read request)
  let result := Expr.mux (Request.writeField.read request) updated old
  let memoryAction : Act := .ite (Request.writeField.read request)
    (registerFile.write 0 (Request.addrField.read request) result) .skip
  let tail : Act := .seq (targetResponse.enq (responseExpr request result))
    (.seq (audit.enq (commitExpr request result))
      (.seq targetRequest.pop
        (.write 32 "commits" (.add (.reg 32 "commits") (.lit 1)))))
  have tailPreserves (acc : St) :
      (tail.run state acc).mems registerFile.name address.toNat 32 =
        acc.mems registerFile.name address.toNat 32 := by
    apply Act.run_mems_notin
    simp [tail, Act.memWrites, PackedChan.enq, Chan.enq, PackedChan.pop,
      Chan.pop, registerFile]
  have memoryEq (location : BitVec 8) :
      acc.mems registerFile.name location.toNat 32 =
        state.mems registerFile.name location.toNat 32 := by
    simpa [serviceMemoryAt] using congrFun sameMemory location
  change serviceMemoryAt ((Act.seq memoryAction tail).run state acc) address = _
  simp only [Act.run, serviceMemoryAt]
  rw [tailPreserves]
  by_cases write : (serviceRequestAt state).write = 1#1
  · by_cases sameNat : address.toNat = (serviceRequestAt state).addr.toNat
    · have same : address = (serviceRequestAt state).addr :=
        BitVec.eq_of_toNat_eq sameNat
      change (targetRequest.deq.eval state).write = 1#1 at write
      simp [memoryAction, result, updated, old, request, Act.run, Mem.write,
        Mem.rd, MemEnv.set, PackedField.read_eval, maskedWord_correct,
        Expr.eval, serviceRequestAt, serviceResultAt, serviceMemoryAt,
        applyRequest, write, sameNat, same, memoryEq, registerFile]
    · have different : address ≠ (serviceRequestAt state).addr := by
        intro same
        exact sameNat (congrArg BitVec.toNat same)
      change (targetRequest.deq.eval state).write = 1#1 at write
      change address.toNat ≠ (targetRequest.deq.eval state).addr.toNat at sameNat
      change address ≠ (targetRequest.deq.eval state).addr at different
      simp [memoryAction, result, updated, old, request, Act.run, Mem.write,
        Mem.rd, MemEnv.set, PackedField.read_eval, maskedWord_correct,
        Expr.eval, serviceRequestAt, serviceResultAt, serviceMemoryAt,
        applyRequest, write, sameNat, different, memoryEq, registerFile]
      exact memoryEq address
  · change (targetRequest.deq.eval state).write ≠ 1#1 at write
    simp [memoryAction, result, updated, old, request, Act.run, Mem.write,
      Mem.rd, MemEnv.set, PackedField.read_eval, maskedWord_correct,
      Expr.eval, serviceRequestAt, serviceResultAt, serviceMemoryAt,
      applyRequest, write, memoryEq, registerFile]
    exact memoryEq address

private theorem service_memory_support :
    service.memSupportRules registerFile.name = [serviceCommitRule] := by
  rfl

private theorem service_response_payload_support :
    service.regSupportRules targetResponse.bits.sourcePayloadName
      (HwPacked.width Response) = [serviceCommitRule] := by
  rfl

private theorem service_audit_payload_support :
    service.regSupportRules audit.bits.sourcePayloadName
      (HwPacked.width CommitRecord) = [serviceCommitRule] := by
  rfl

def sourceMaintenanceRule {w : Nat} (channel : Chan w) : Rule :=
  ⟨channel.stem ++ "source_maintenance",
    .ite channel.sourceAccepted
      (.write 1 channel.sourceValidName (.lit 0)) .skip⟩

def sinkMaintenanceRule {w : Nat} (channel : Chan w) : Rule :=
  ⟨channel.stem ++ "sink_maintenance",
    .write 1 channel.sinkPopName (.lit 0)⟩

private theorem service_response_valid_support :
    service.regSupportRules targetResponse.bits.sourceValidName 1 =
      [sourceMaintenanceRule targetResponse.bits, serviceCommitRule] := by
  rfl

private theorem service_audit_valid_support :
    service.regSupportRules audit.bits.sourceValidName 1 =
      [sourceMaintenanceRule audit.bits, serviceCommitRule] := by
  rfl

private theorem service_request_pop_support :
    service.regSupportRules targetRequest.bits.sinkPopName 1 =
      [sinkMaintenanceRule targetRequest.bits, serviceCommitRule] := by
  rfl

private theorem service_request_payload_support :
    service.regSupportRules targetRequest.bits.sinkPayloadName
      (HwPacked.width Request) = [] := by
  rfl

private theorem fabric_cpu_request_pop_support :
    fabric.regSupportRules cpuRequest.bits.sinkPopName 1 =
      [sinkMaintenanceRule cpuRequest.bits, fabricArbitrateRule] := by
  rfl

private theorem fabric_dma_request_pop_support :
    fabric.regSupportRules dmaRequest.bits.sinkPopName 1 =
      [sinkMaintenanceRule dmaRequest.bits, fabricArbitrateRule] := by
  rfl

private theorem fabric_cpu_request_payload_support :
    fabric.regSupportRules cpuRequest.bits.sinkPayloadName
      (HwPacked.width Request) = [] := by
  rfl

private theorem fabric_dma_request_payload_support :
    fabric.regSupportRules dmaRequest.bits.sinkPayloadName
      (HwPacked.width Request) = [] := by
  rfl

private theorem fabric_target_request_valid_support :
    fabric.regSupportRules targetRequest.bits.sourceValidName 1 =
      [sourceMaintenanceRule targetRequest.bits, fabricArbitrateRule] := by
  rfl

private theorem fabric_target_request_payload_support :
    fabric.regSupportRules targetRequest.bits.sourcePayloadName
      (HwPacked.width Request) = [fabricArbitrateRule] := by
  rfl

private theorem fabric_target_response_pop_support :
    fabric.regSupportRules targetResponse.bits.sinkPopName 1 =
      [sinkMaintenanceRule targetResponse.bits, fabricRouteResponseRule] := by
  rfl

private theorem fabric_target_response_payload_support :
    fabric.regSupportRules targetResponse.bits.sinkPayloadName
      (HwPacked.width Response) = [] := by
  rfl

private theorem fabric_cpu_response_valid_support :
    fabric.regSupportRules cpuResponse.bits.sourceValidName 1 =
      [sourceMaintenanceRule cpuResponse.bits, fabricRouteResponseRule] := by
  rfl

private theorem fabric_cpu_response_payload_support :
    fabric.regSupportRules cpuResponse.bits.sourcePayloadName
      (HwPacked.width Response) = [fabricRouteResponseRule] := by
  rfl

private theorem fabric_dma_response_valid_support :
    fabric.regSupportRules dmaResponse.bits.sourceValidName 1 =
      [sourceMaintenanceRule dmaResponse.bits, fabricRouteResponseRule] := by
  rfl

private theorem fabric_dma_response_payload_support :
    fabric.regSupportRules dmaResponse.bits.sourcePayloadName
      (HwPacked.width Response) = [fabricRouteResponseRule] := by
  rfl

private theorem fabric_outstanding_support :
    fabric.regSupportRules "outstanding" 1 =
      [fabricRouteResponseRule, fabricArbitrateRule] := by
  rfl

private theorem fabric_route_support :
    fabric.regSupportRules "route" 1 = [fabricArbitrateRule] := by
  rfl

@[simp] private theorem targetRequest_bits_name :
    targetRequest.bits.name = "target_request" := rfl

@[simp] private theorem registerFile_name : registerFile.name = "register_file" := rfl

@[simp] private theorem eval_lit_one (state : St) :
    Expr.eval state (Expr.lit 1#1) = 1#1 := rfl

@[simp] private theorem eval_lit_zero (state : St) :
    Expr.eval state (Expr.lit 0#1) = 0#1 := rfl

private theorem bitvec1_and_eq_one (left right : BitVec 1) :
    left &&& right = 1#1 ↔ left = 1#1 ∧ right = 1#1 := by
  have leftCases : left = 0#1 ∨ left = 1#1 := by bv_omega
  have rightCases : right = 0#1 ∨ right = 1#1 := by bv_omega
  rcases leftCases with rfl | rfl <;>
    rcases rightCases with rfl | rfl <;> decide

private theorem service_response_endpoint_not_input (state : St) (input : InEnv) :
    (state.setInputs service.inputs input).regs
      targetResponse.bits.sourceValidName 1 =
      state.regs targetResponse.bits.sourceValidName 1 ∧
    (state.setInputs service.inputs input).regs
      targetResponse.bits.sourcePayloadName (HwPacked.width Response) =
      state.regs targetResponse.bits.sourcePayloadName
        (HwPacked.width Response) := by
  constructor
  · apply state.setInputs_regs_notin
    decide
  · apply state.setInputs_regs_notin
    decide

private theorem service_audit_endpoint_not_input (state : St) (input : InEnv) :
    (state.setInputs service.inputs input).regs audit.bits.sourceValidName 1 =
      state.regs audit.bits.sourceValidName 1 ∧
    (state.setInputs service.inputs input).regs audit.bits.sourcePayloadName
        (HwPacked.width CommitRecord) =
      state.regs audit.bits.sourcePayloadName (HwPacked.width CommitRecord) := by
  constructor
  · apply state.setInputs_regs_notin
    decide
  · apply state.setInputs_regs_notin
    decide

private theorem serviceCommitRule_audit_valid_project (state acc : St) :
    (serviceCommitRule.body.run state acc).regs audit.bits.sourceValidName 1 =
      ((serviceCommitRule.body.projectRegs
        [(audit.bits.sourceValidName, 1)]).run state acc).regs
          audit.bits.sourceValidName 1 := by
  symm
  exact Act.projectRegs_run [(audit.bits.sourceValidName, 1)]
    audit.bits.sourceValidName 1 (by simp) serviceCommitRule.body state acc

private theorem serviceCommitRule_audit_payload_project (state acc : St) :
    (serviceCommitRule.body.run state acc).regs audit.bits.sourcePayloadName
        (HwPacked.width CommitRecord) =
      ((serviceCommitRule.body.projectRegs
        [(audit.bits.sourcePayloadName, HwPacked.width CommitRecord)]).run
          state acc).regs audit.bits.sourcePayloadName
            (HwPacked.width CommitRecord) := by
  symm
  exact Act.projectRegs_run
    [(audit.bits.sourcePayloadName, HwPacked.width CommitRecord)]
    audit.bits.sourcePayloadName (HwPacked.width CommitRecord) (by simp)
      serviceCommitRule.body state acc

private theorem serviceCommitRule_response_valid_project (state acc : St) :
    (serviceCommitRule.body.run state acc).regs
        targetResponse.bits.sourceValidName 1 =
      ((serviceCommitRule.body.projectRegs
        [(targetResponse.bits.sourceValidName, 1)]).run state acc).regs
          targetResponse.bits.sourceValidName 1 := by
  symm
  exact Act.projectRegs_run [(targetResponse.bits.sourceValidName, 1)]
    targetResponse.bits.sourceValidName 1 (by simp) serviceCommitRule.body
      state acc

private theorem serviceCommitRule_response_payload_project (state acc : St) :
    (serviceCommitRule.body.run state acc).regs
        targetResponse.bits.sourcePayloadName (HwPacked.width Response) =
      ((serviceCommitRule.body.projectRegs
        [(targetResponse.bits.sourcePayloadName, HwPacked.width Response)]).run
          state acc).regs targetResponse.bits.sourcePayloadName
            (HwPacked.width Response) := by
  symm
  exact Act.projectRegs_run
    [(targetResponse.bits.sourcePayloadName, HwPacked.width Response)]
    targetResponse.bits.sourcePayloadName (HwPacked.width Response) (by simp)
      serviceCommitRule.body state acc

private theorem serviceCommitRule_request_pop_project (state acc : St) :
    (serviceCommitRule.body.run state acc).regs
        targetRequest.bits.sinkPopName 1 =
      ((serviceCommitRule.body.projectRegs
        [(targetRequest.bits.sinkPopName, 1)]).run state acc).regs
          targetRequest.bits.sinkPopName 1 := by
  symm
  exact Act.projectRegs_run [(targetRequest.bits.sinkPopName, 1)]
    targetRequest.bits.sinkPopName 1 (by simp) serviceCommitRule.body state acc

theorem service_cycleOpen_memory_refines (state : St) (input : InEnv)
    (requestReady : targetRequest.bits.canDeq.eval
      (state.setInputs service.inputs input) = 1#1)
    (responseReady : targetResponse.bits.canEnq.eval
      (state.setInputs service.inputs input) = 1#1)
    (auditReady : audit.bits.canEnq.eval
      (state.setInputs service.inputs input) = 1#1) :
    serviceMemoryAt (service.cycleOpen input state) =
      (applyRequest (serviceMemoryAt state)
        (serviceRequestAt (state.setInputs service.inputs input))).1 := by
  funext address
  let poked := state.setInputs service.inputs input
  change targetRequest.canDeq.eval poked = 1#1 at requestReady
  change targetResponse.canEnq.eval poked = 1#1 at responseReady
  change audit.canEnq.eval poked = 1#1 at auditReady
  have pokedMemory : serviceMemoryAt poked = serviceMemoryAt state := by
    rfl
  have projected := service.cycle_mems_eq_support registerFile.name poked
    address.toNat 32
  change serviceMemoryAt (service.cycle poked) address = _
  change (service.cycle poked).mems registerFile.name address.toNat 32 = _
  rw [projected]
  rw [service_memory_support]
  simp only [List.foldl_cons, List.foldl_nil, serviceCommitRule, Act.run]
  rw [requestReady, responseReady, auditReady]
  simpa [poked] using
    serviceCommit_memory_refines poked poked rfl address

theorem service_cycleOpen_emits_response (state : St) (input : InEnv)
    (requestReady : targetRequest.bits.canDeq.eval
      (state.setInputs service.inputs input) = 1#1)
    (responseReady : targetResponse.bits.canEnq.eval
      (state.setInputs service.inputs input) = 1#1)
    (auditReady : audit.bits.canEnq.eval
      (state.setInputs service.inputs input) = 1#1) :
    HwPacked.unpack ((service.cycleOpen input state).regs
      targetResponse.bits.sourcePayloadName (HwPacked.width Response)) =
      serviceResponseAt (state.setInputs service.inputs input) := by
  let poked := state.setInputs service.inputs input
  change targetRequest.canDeq.eval poked = 1#1 at requestReady
  change targetResponse.canEnq.eval poked = 1#1 at responseReady
  change audit.canEnq.eval poked = 1#1 at auditReady
  have projected := service.cycle_regs_eq_support
    targetResponse.bits.sourcePayloadName (HwPacked.width Response) poked
  change HwPacked.unpack ((service.cycle poked).regs
    targetResponse.bits.sourcePayloadName (HwPacked.width Response)) = _
  rw [projected]
  rw [service_response_payload_support]
  simp only [List.foldl_cons, List.foldl_nil, serviceCommitRule, Act.run]
  rw [requestReady, responseReady, auditReady]
  simpa [poked] using
    serviceCommit_emits_response poked poked requestReady responseReady auditReady

def serviceResponsePending (state : St) : List Response :=
  if state.regs targetResponse.bits.sourceValidName 1 = 1#1 then
    [HwPacked.unpack (state.regs targetResponse.bits.sourcePayloadName
      (HwPacked.width Response))]
  else []

def serviceResponseProduced (state : St) : List Response :=
  if targetRequest.bits.canDeq.eval state = 1#1 ∧
      targetResponse.bits.canEnq.eval state = 1#1 ∧
      audit.bits.canEnq.eval state = 1#1 then
    [serviceResponseAt state]
  else []

def serviceResponseAccepted (state : St) : List Response :=
  if targetResponse.bits.sourceAccepted.eval state = 1#1 then
    serviceResponsePending state
  else []

theorem service_cycleOpen_response_ledger (state : St) (input : InEnv)
    (acceptedLegal : targetResponse.bits.sourceAccepted.eval
      (state.setInputs service.inputs input) = 1#1 →
      state.regs targetResponse.bits.sourceValidName 1 = 1#1) :
    serviceResponsePending state ++
        serviceResponseProduced (state.setInputs service.inputs input) =
      serviceResponseAccepted (state.setInputs service.inputs input) ++
        serviceResponsePending (service.cycleOpen input state) := by
  classical
  let poked := state.setInputs service.inputs input
  have validProjected := service.cycle_regs_eq_support
    targetResponse.bits.sourceValidName 1 poked
  have payloadProjected := service.cycle_regs_eq_support
    targetResponse.bits.sourcePayloadName (HwPacked.width Response) poked
  change _ ++ serviceResponseProduced poked =
    serviceResponseAccepted poked ++ serviceResponsePending (service.cycle poked)
  unfold serviceResponsePending serviceResponseProduced serviceResponseAccepted
  rw [validProjected, payloadProjected, service_response_valid_support,
    service_response_payload_support]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [serviceCommitRule_response_valid_project,
    serviceCommitRule_response_payload_project]
  simp only [sourceMaintenanceRule, serviceCommitRule, Act.run]
  have endpointStable := service_response_endpoint_not_input state input
  have pokedValid := endpointStable.1
  have pokedPayload := endpointStable.2
  change poked.regs targetResponse.bits.sourceValidName 1 =
    state.regs targetResponse.bits.sourceValidName 1 at pokedValid
  change poked.regs targetResponse.bits.sourcePayloadName
      (HwPacked.width Response) =
    state.regs targetResponse.bits.sourcePayloadName
      (HwPacked.width Response) at pokedPayload
  clear validProjected payloadProjected endpointStable
  simp only [PackedChan.canEnq, PackedChan.canDeq] at *
  simp only [targetResponse, audit, PackedChan.named] at *
  by_cases accepted : targetResponse.bits.sourceAccepted.eval poked = 1#1 <;>
  by_cases valid : state.regs targetResponse.bits.sourceValidName 1 = 1#1 <;>
  by_cases requestReady : targetRequest.bits.canDeq.eval poked = 1#1 <;>
  by_cases responseReady : targetResponse.bits.canEnq.eval poked = 1#1 <;>
  by_cases auditReady : audit.bits.canEnq.eval poked = 1#1 <;>
    simp [serviceResponsePending, serviceResponseProduced,
      serviceResponseAccepted, accepted, valid, requestReady, responseReady,
      auditReady, serviceCommit, PackedChan.enq, PackedChan.canEnq, Chan.enq,
      Act.run, audit, targetResponse, PackedChan.named, Act.projectRegs,
      Act.smartSeq, Act.smartIte, PackedChan.pop, Chan.pop, Mem.write,
      pokedValid, pokedPayload, Chan.sourceValidName, Chan.sourcePayloadName,
      Chan.sourceAcceptedName, Chan.sinkPopName, Chan.stem, Chan.canEnq,
      Chan.sourceValid, Chan.sourceAccepted, Chan.sourceReady,
      responseExpr_eval_eq_serviceResponseAt] at *
  all_goals simp_all [targetResponse, PackedChan.named, Act.run, Expr.eval]
  all_goals simp_all [bitvec1_and_eq_one]

theorem service_cycleOpen_emits_audit (state : St) (input : InEnv)
    (requestReady : targetRequest.bits.canDeq.eval
      (state.setInputs service.inputs input) = 1#1)
    (responseReady : targetResponse.bits.canEnq.eval
      (state.setInputs service.inputs input) = 1#1)
    (auditReady : audit.bits.canEnq.eval
      (state.setInputs service.inputs input) = 1#1) :
    HwPacked.unpack ((service.cycleOpen input state).regs
      audit.bits.sourcePayloadName (HwPacked.width CommitRecord)) =
      serviceCommitAt (state.setInputs service.inputs input) := by
  let poked := state.setInputs service.inputs input
  change targetRequest.canDeq.eval poked = 1#1 at requestReady
  change targetResponse.canEnq.eval poked = 1#1 at responseReady
  change audit.canEnq.eval poked = 1#1 at auditReady
  have projected := service.cycle_regs_eq_support audit.bits.sourcePayloadName
    (HwPacked.width CommitRecord) poked
  change HwPacked.unpack ((service.cycle poked).regs
    audit.bits.sourcePayloadName (HwPacked.width CommitRecord)) = _
  rw [projected]
  rw [service_audit_payload_support]
  simp only [List.foldl_cons, List.foldl_nil, serviceCommitRule, Act.run]
  rw [requestReady, responseReady, auditReady]
  simpa [poked] using
    serviceCommit_emits_audit poked poked requestReady responseReady auditReady

def serviceAuditPending (state : St) : List CommitRecord :=
  if state.regs audit.bits.sourceValidName 1 = 1#1 then
    [HwPacked.unpack (state.regs audit.bits.sourcePayloadName
      (HwPacked.width CommitRecord))]
  else []

def serviceAuditProduced (state : St) : List CommitRecord :=
  if targetRequest.bits.canDeq.eval state = 1#1 ∧
      targetResponse.bits.canEnq.eval state = 1#1 ∧
      audit.bits.canEnq.eval state = 1#1 then
    [serviceCommitAt state]
  else []

def serviceAuditAccepted (state : St) : List CommitRecord :=
  if audit.bits.sourceAccepted.eval state = 1#1 then
    serviceAuditPending state
  else []

theorem service_cycleOpen_audit_ledger (state : St) (input : InEnv)
    (acceptedLegal : audit.bits.sourceAccepted.eval
      (state.setInputs service.inputs input) = 1#1 →
      state.regs audit.bits.sourceValidName 1 = 1#1) :
    serviceAuditPending state ++
        serviceAuditProduced (state.setInputs service.inputs input) =
      serviceAuditAccepted (state.setInputs service.inputs input) ++
        serviceAuditPending (service.cycleOpen input state) := by
  classical
  let poked := state.setInputs service.inputs input
  have validProjected := service.cycle_regs_eq_support
    audit.bits.sourceValidName 1 poked
  have payloadProjected := service.cycle_regs_eq_support
    audit.bits.sourcePayloadName (HwPacked.width CommitRecord) poked
  change _ ++ serviceAuditProduced poked =
    serviceAuditAccepted poked ++ serviceAuditPending (service.cycle poked)
  unfold serviceAuditPending serviceAuditProduced serviceAuditAccepted
  rw [validProjected, payloadProjected, service_audit_valid_support,
    service_audit_payload_support]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [serviceCommitRule_audit_valid_project,
    serviceCommitRule_audit_payload_project]
  simp only [sourceMaintenanceRule, serviceCommitRule, Act.run]
  have endpointStable := service_audit_endpoint_not_input state input
  have pokedValid := endpointStable.1
  have pokedPayload := endpointStable.2
  change poked.regs audit.bits.sourceValidName 1 =
    state.regs audit.bits.sourceValidName 1 at pokedValid
  change poked.regs audit.bits.sourcePayloadName (HwPacked.width CommitRecord) =
    state.regs audit.bits.sourcePayloadName
      (HwPacked.width CommitRecord) at pokedPayload
  clear validProjected payloadProjected endpointStable
  simp only [PackedChan.canEnq, PackedChan.canDeq] at *
  simp only [targetResponse, audit, PackedChan.named] at *
  by_cases accepted : audit.bits.sourceAccepted.eval poked = 1#1 <;>
  by_cases valid : state.regs audit.bits.sourceValidName 1 = 1#1 <;>
  by_cases requestReady : targetRequest.bits.canDeq.eval poked = 1#1 <;>
  by_cases responseReady : targetResponse.bits.canEnq.eval poked = 1#1 <;>
  by_cases auditReady : audit.bits.canEnq.eval poked = 1#1 <;>
    simp [serviceAuditPending, serviceAuditProduced, serviceAuditAccepted,
      accepted, valid, requestReady, responseReady, auditReady, serviceCommit,
      PackedChan.enq, PackedChan.canEnq, Chan.enq, Act.run, audit,
      PackedChan.named, Act.projectRegs, Act.smartSeq, Act.smartIte,
      targetResponse, PackedChan.pop, Chan.pop, Mem.write,
      pokedValid, pokedPayload, Chan.sourceValidName,
      Chan.sourcePayloadName, Chan.sourceAcceptedName, Chan.sinkPopName,
      Chan.stem, Chan.canEnq, Chan.sourceValid, Chan.sourceAccepted,
      Chan.sourceReady, commitExpr_eval_eq_serviceCommitAt] at *
  all_goals simp_all [audit, PackedChan.named, Act.run, Expr.eval]
  all_goals simp_all [bitvec1_and_eq_one]

theorem service_cycleOpen_request_pop (state : St) (input : InEnv) :
    (service.cycleOpen input state).regs targetRequest.bits.sinkPopName 1 =
      if targetRequest.bits.canDeq.eval
          (state.setInputs service.inputs input) = 1#1 ∧
        targetResponse.bits.canEnq.eval
          (state.setInputs service.inputs input) = 1#1 ∧
        audit.bits.canEnq.eval (state.setInputs service.inputs input) = 1#1
      then 1#1 else 0#1 := by
  let poked := state.setInputs service.inputs input
  have projected := service.cycle_regs_eq_support
    targetRequest.bits.sinkPopName 1 poked
  change (service.cycle poked).regs targetRequest.bits.sinkPopName 1 = _
  rw [projected, service_request_pop_support]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [serviceCommitRule_request_pop_project]
  simp only [sinkMaintenanceRule, serviceCommitRule, Act.run]
  clear projected
  change _ = if targetRequest.bits.canDeq.eval poked = 1#1 ∧
      targetResponse.bits.canEnq.eval poked = 1#1 ∧
      audit.bits.canEnq.eval poked = 1#1 then 1#1 else 0#1
  simp only [targetRequest, targetResponse, audit, PackedChan.named] at *
  by_cases requestReady : targetRequest.bits.canDeq.eval poked = 1#1 <;>
  by_cases responseReady : targetResponse.bits.canEnq.eval poked = 1#1 <;>
  by_cases auditReady : audit.bits.canEnq.eval poked = 1#1 <;>
    simp [requestReady, responseReady, auditReady, serviceCommit,
      PackedChan.enq, PackedChan.canEnq, PackedChan.canDeq, Chan.enq,
      PackedChan.pop, Chan.pop, Act.run,
      Act.projectRegs, Act.smartSeq, Act.smartIte, targetRequest,
      targetResponse, audit, PackedChan.named, Mem.write,
      Chan.sourceValidName, Chan.sourcePayloadName, Chan.sinkPopName,
      Chan.stem] at *
  all_goals simp_all

theorem service_cycleOpen_request_payload (state : St) (input : InEnv) :
    (service.cycleOpen input state).regs targetRequest.bits.sinkPayloadName
        (HwPacked.width Request) =
      input targetRequest.bits.sinkPayloadName (HwPacked.width Request) := by
  let poked := state.setInputs service.inputs input
  have projected := service.cycle_regs_eq_support
    targetRequest.bits.sinkPayloadName (HwPacked.width Request) poked
  change (service.cycle poked).regs targetRequest.bits.sinkPayloadName
      (HwPacked.width Request) = _
  rw [projected, service_request_payload_support]
  rfl

/-! ## Literal fabric arbitration and routing refinement -/

inductive FabricClient
  | cpu
  | dma
  deriving DecidableEq, Repr

def fabricGrantChoice (state : St) : Option FabricClient :=
  if (Expr.and (.not (.reg 1 "hold_arbitration"))
      (.not (.reg 1 "outstanding"))).eval state = 1#1 then
    if targetRequest.bits.canEnq.eval state = 1#1 then
      if (Expr.and cpuRequest.bits.canDeq dmaRequest.bits.canDeq).eval state = 1#1 then
        if (Expr.eq (.reg 1 "round_robin") (.lit 0#1)).eval state = 1#1 then
          some .cpu else some .dma
      else if cpuRequest.bits.canDeq.eval state = 1#1 then some .cpu
      else if dmaRequest.bits.canDeq.eval state = 1#1 then some .dma
      else none
    else none
  else none

def fabricGrantBits? (state : St) : Option (BitVec (HwPacked.width Request)) :=
  match fabricGrantChoice state with
  | some .cpu => some (cpuRequest.bits.deq.eval state)
  | some .dma => some (dmaRequest.bits.deq.eval state)
  | none => none

def fabricGrantRequest? (state : St) : Option Request :=
  (fabricGrantBits? state).map HwPacked.unpack

theorem fabricGrantChoice_some_canEnq (state : St) (client : FabricClient)
    (granted : fabricGrantChoice state = some client) :
    targetRequest.bits.canEnq.eval state = 1#1 := by
  unfold fabricGrantChoice at granted
  repeat' first
    | split at granted <;> rename_i condition
  all_goals simp_all

theorem fabricGrantChoice_cpu_canDeq (state : St)
    (granted : fabricGrantChoice state = some .cpu) :
    cpuRequest.bits.canDeq.eval state = 1#1 := by
  unfold fabricGrantChoice at granted
  repeat' first
    | split at granted <;> rename_i condition
  all_goals simp_all [Expr.eval, bitvec1_and_eq_one]

theorem fabricGrantChoice_dma_canDeq (state : St)
    (granted : fabricGrantChoice state = some .dma) :
    dmaRequest.bits.canDeq.eval state = 1#1 := by
  unfold fabricGrantChoice at granted
  repeat' first
    | split at granted <;> rename_i condition
  all_goals simp_all [Expr.eval, bitvec1_and_eq_one]

theorem fabricArbitrateRule_payload (state acc : St) :
    (fabricArbitrateRule.body.run state acc).regs
        targetRequest.bits.sourcePayloadName (HwPacked.width Request) =
      match fabricGrantBits? state with
      | some request => request
      | none => acc.regs targetRequest.bits.sourcePayloadName
          (HwPacked.width Request) := by
  unfold fabricArbitrateRule fabricGrantBits? fabricGrantChoice
  simp only [Act.run]
  repeat' first
    | split <;> rename_i condition
  all_goals simp_all [fabricGrant, PackedChan.enq, PackedChan.pop,
    PackedChan.canEnq, PackedChan.canDeq, PackedChan.deq, PackedExpr.eval,
    Chan.enq, Chan.pop, Act.run,
    cpuRequest, dmaRequest, targetRequest, PackedChan.named, Chan.stem,
    Chan.sourcePayloadName, Chan.sourceValidName, Chan.sinkPopName,
    Expr.eval, bitvec1_and_eq_one]
  all_goals bv_decide

set_option maxHeartbeats 800000 in
theorem fabricArbitrateRule_control (state acc : St) :
    let next := fabricArbitrateRule.body.run state acc
    let choice := fabricGrantChoice state
    next.regs cpuRequest.bits.sinkPopName 1 =
        (if choice = some .cpu then 1#1 else acc.regs
          cpuRequest.bits.sinkPopName 1) ∧
      next.regs dmaRequest.bits.sinkPopName 1 =
        (if choice = some .dma then 1#1 else acc.regs
          dmaRequest.bits.sinkPopName 1) ∧
      next.regs targetRequest.bits.sourceValidName 1 =
        (if choice.isSome then 1#1 else acc.regs
          targetRequest.bits.sourceValidName 1) ∧
      next.regs "outstanding" 1 =
        (if choice.isSome then 1#1 else acc.regs "outstanding" 1) ∧
      next.regs "route" 1 =
        (match choice with
        | some .cpu => 0#1
        | some .dma => 1#1
        | none => acc.regs "route" 1) := by
  unfold fabricArbitrateRule fabricGrantChoice
  simp only [Act.run]
  repeat' first
    | split <;> rename_i condition
  all_goals simp_all [fabricGrant, PackedChan.enq, PackedChan.pop,
    PackedChan.canEnq, PackedChan.canDeq, PackedChan.deq, PackedExpr.eval,
    Chan.enq, Chan.pop, Act.run, cpuRequest, dmaRequest, targetRequest,
    PackedChan.named, Chan.stem, Chan.sourcePayloadName,
    Chan.sourceValidName, Chan.sinkPopName, Expr.eval, bitvec1_and_eq_one]
  all_goals bv_decide

theorem fabric_cycleOpen_cpu_request_pop (state : St) (input : InEnv) :
    (fabric.cycleOpen input state).regs cpuRequest.bits.sinkPopName 1 =
      if fabricGrantChoice (state.setInputs fabric.inputs input) = some .cpu
      then 1#1 else 0#1 := by
  let poked := state.setInputs fabric.inputs input
  have projected := fabric.cycle_regs_eq_support
    cpuRequest.bits.sinkPopName 1 poked
  change (fabric.cycle poked).regs cpuRequest.bits.sinkPopName 1 = _
  rw [projected, fabric_cpu_request_pop_support]
  simp only [List.foldl_cons, List.foldl_nil]
  let maintained := sinkMaintenanceRule cpuRequest.bits |>.body.run poked poked
  have control := fabricArbitrateRule_control poked maintained
  change (fabricArbitrateRule.body.run poked maintained).regs
      cpuRequest.bits.sinkPopName 1 = _
  rw [control.1]
  simp [maintained, sinkMaintenanceRule, Act.run, poked]

theorem fabric_cycleOpen_dma_request_pop (state : St) (input : InEnv) :
    (fabric.cycleOpen input state).regs dmaRequest.bits.sinkPopName 1 =
      if fabricGrantChoice (state.setInputs fabric.inputs input) = some .dma
      then 1#1 else 0#1 := by
  let poked := state.setInputs fabric.inputs input
  have projected := fabric.cycle_regs_eq_support
    dmaRequest.bits.sinkPopName 1 poked
  change (fabric.cycle poked).regs dmaRequest.bits.sinkPopName 1 = _
  rw [projected, fabric_dma_request_pop_support]
  simp only [List.foldl_cons, List.foldl_nil]
  let maintained := sinkMaintenanceRule dmaRequest.bits |>.body.run poked poked
  have control := fabricArbitrateRule_control poked maintained
  change (fabricArbitrateRule.body.run poked maintained).regs
      dmaRequest.bits.sinkPopName 1 = _
  rw [control.2.1]
  simp [maintained, sinkMaintenanceRule, Act.run, poked]

theorem fabric_cycleOpen_cpu_request_payload (state : St) (input : InEnv) :
    (fabric.cycleOpen input state).regs cpuRequest.bits.sinkPayloadName
        (HwPacked.width Request) =
      input cpuRequest.bits.sinkPayloadName (HwPacked.width Request) := by
  let poked := state.setInputs fabric.inputs input
  have projected := fabric.cycle_regs_eq_support
    cpuRequest.bits.sinkPayloadName (HwPacked.width Request) poked
  change (fabric.cycle poked).regs cpuRequest.bits.sinkPayloadName
      (HwPacked.width Request) = _
  rw [projected, fabric_cpu_request_payload_support]
  rfl

theorem fabric_cycleOpen_dma_request_payload (state : St) (input : InEnv) :
    (fabric.cycleOpen input state).regs dmaRequest.bits.sinkPayloadName
        (HwPacked.width Request) =
      input dmaRequest.bits.sinkPayloadName (HwPacked.width Request) := by
  let poked := state.setInputs fabric.inputs input
  have projected := fabric.cycle_regs_eq_support
    dmaRequest.bits.sinkPayloadName (HwPacked.width Request) poked
  change (fabric.cycle poked).regs dmaRequest.bits.sinkPayloadName
      (HwPacked.width Request) = _
  rw [projected, fabric_dma_request_payload_support]
  rfl

theorem fabric_cycleOpen_target_request_payload (state : St) (input : InEnv) :
    (fabric.cycleOpen input state).regs targetRequest.bits.sourcePayloadName
        (HwPacked.width Request) =
      match fabricGrantBits? (state.setInputs fabric.inputs input) with
      | some request => request
      | none => state.regs targetRequest.bits.sourcePayloadName
          (HwPacked.width Request) := by
  let poked := state.setInputs fabric.inputs input
  have projected := fabric.cycle_regs_eq_support
    targetRequest.bits.sourcePayloadName (HwPacked.width Request) poked
  change (fabric.cycle poked).regs targetRequest.bits.sourcePayloadName
      (HwPacked.width Request) = _
  rw [projected, fabric_target_request_payload_support]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [fabricArbitrateRule_payload]
  rfl

theorem fabric_cycleOpen_target_request_valid (state : St) (input : InEnv) :
    (fabric.cycleOpen input state).regs targetRequest.bits.sourceValidName 1 =
      if (fabricGrantChoice (state.setInputs fabric.inputs input)).isSome
      then 1#1
      else if targetRequest.bits.sourceAccepted.eval
          (state.setInputs fabric.inputs input) = 1#1
        then 0#1 else state.regs targetRequest.bits.sourceValidName 1 := by
  let poked := state.setInputs fabric.inputs input
  have projected := fabric.cycle_regs_eq_support
    targetRequest.bits.sourceValidName 1 poked
  change (fabric.cycle poked).regs targetRequest.bits.sourceValidName 1 = _
  rw [projected, fabric_target_request_valid_support]
  simp only [List.foldl_cons, List.foldl_nil]
  let maintained := sourceMaintenanceRule targetRequest.bits |>.body.run poked poked
  have control := fabricArbitrateRule_control poked maintained
  change (fabricArbitrateRule.body.run poked maintained).regs
      targetRequest.bits.sourceValidName 1 = _
  rw [control.2.2.1]
  have stable : poked.regs targetRequest.bits.sourceValidName 1 =
      state.regs targetRequest.bits.sourceValidName 1 := by rfl
  change poked.regs "__loom_chan_target_request_src_valid" 1 =
      state.regs "__loom_chan_target_request_src_valid" 1 at stable
  by_cases granted : (fabricGrantChoice poked).isSome = true
  · simp [granted, poked]
  · by_cases accepted : targetRequest.bits.sourceAccepted.eval poked = 1#1
    · change targetRequest.bits.sourceAccepted.eval
        (state.setInputs fabric.inputs input) = 1#1 at accepted
      have accepted' : (({ name := "target_request", depth := 4 } :
          Chan (HwPacked.width Request)).sourceAccepted.eval
            (state.setInputs fabric.inputs input)) = 1#1 := by
        simpa [targetRequest, PackedChan.named] using accepted
      simp [granted, accepted', maintained, sourceMaintenanceRule, Act.run,
        poked, targetRequest, PackedChan.named, Chan.stem,
        Chan.sourceValidName]
    · change targetRequest.bits.sourceAccepted.eval
        (state.setInputs fabric.inputs input) ≠ 1#1 at accepted
      have accepted' : (({ name := "target_request", depth := 4 } :
          Chan (HwPacked.width Request)).sourceAccepted.eval
            (state.setInputs fabric.inputs input)) ≠ 1#1 := by
        simpa [targetRequest, PackedChan.named] using accepted
      simp [granted, accepted', maintained, sourceMaintenanceRule, Act.run,
        stable, poked, targetRequest, PackedChan.named, Chan.stem,
        Chan.sourceValidName]

def fabricTargetRequestPending (state : St) : List Request :=
  if state.regs targetRequest.bits.sourceValidName 1 = 1#1 then
    [HwPacked.unpack (state.regs targetRequest.bits.sourcePayloadName
      (HwPacked.width Request))]
  else []

def fabricTargetRequestProduced (state : St) : List Request :=
  (fabricGrantBits? state).toList.map HwPacked.unpack

def fabricTargetRequestAccepted (state : St) : List Request :=
  if targetRequest.bits.sourceAccepted.eval state = 1#1 then
    fabricTargetRequestPending state
  else []

/-- Literal fabric grant conservation at the registered target-request source.
This simultaneously proves that one arbitration firing cannot forward two
requests: the produced observation is an `Option` and therefore has length at
most one. -/
theorem fabric_cycleOpen_target_request_ledger (state : St) (input : InEnv)
    (acceptedLegal : targetRequest.bits.sourceAccepted.eval
      (state.setInputs fabric.inputs input) = 1#1 →
      state.regs targetRequest.bits.sourceValidName 1 = 1#1) :
    fabricTargetRequestPending state ++
        fabricTargetRequestProduced (state.setInputs fabric.inputs input) =
      fabricTargetRequestAccepted (state.setInputs fabric.inputs input) ++
        fabricTargetRequestPending (fabric.cycleOpen input state) := by
  let poked := state.setInputs fabric.inputs input
  have validNext := fabric_cycleOpen_target_request_valid state input
  have payloadNext := fabric_cycleOpen_target_request_payload state input
  have stableValid : poked.regs targetRequest.bits.sourceValidName 1 =
      state.regs targetRequest.bits.sourceValidName 1 := by rfl
  have stablePayload : poked.regs targetRequest.bits.sourcePayloadName
      (HwPacked.width Request) =
      state.regs targetRequest.bits.sourcePayloadName
        (HwPacked.width Request) := by rfl
  change (fabric.cycle poked).regs targetRequest.bits.sourceValidName 1 = _
    at validNext
  change (fabric.cycle poked).regs targetRequest.bits.sourcePayloadName
      (HwPacked.width Request) = _ at payloadNext
  change fabricTargetRequestPending state ++ fabricTargetRequestProduced poked =
    fabricTargetRequestAccepted poked ++
      fabricTargetRequestPending (fabric.cycle poked)
  by_cases accepted : targetRequest.bits.sourceAccepted.eval poked = 1#1
  · have valid : state.regs targetRequest.bits.sourceValidName 1 = 1#1 :=
      acceptedLegal accepted
    cases grant : fabricGrantBits? poked with
    | none =>
        have choiceNone : fabricGrantChoice poked = none := by
          cases choice : fabricGrantChoice poked with
          | none => rfl
          | some client =>
              cases client <;> simp [fabricGrantBits?, choice] at grant
        simp [fabricTargetRequestPending, fabricTargetRequestProduced,
          fabricTargetRequestAccepted, accepted, valid, stableValid,
          stablePayload, validNext, payloadNext, poked, choiceNone, grant] at *
    | some request =>
        have choiceSome : (fabricGrantChoice poked).isSome = true := by
          cases choice : fabricGrantChoice poked with
          | none => simp [fabricGrantBits?, choice] at grant
          | some client => simp
        simp [fabricTargetRequestPending, fabricTargetRequestProduced,
          fabricTargetRequestAccepted, accepted, valid, stableValid,
          stablePayload, validNext, payloadNext, poked, choiceSome, grant] at *
  · cases grant : fabricGrantBits? poked with
    | none =>
        have choiceNone : fabricGrantChoice poked = none := by
          cases choice : fabricGrantChoice poked with
          | none => rfl
          | some client =>
              cases client <;> simp [fabricGrantBits?, choice] at grant
        simp [fabricTargetRequestPending, fabricTargetRequestProduced,
          fabricTargetRequestAccepted, accepted, stableValid, stablePayload,
          validNext, payloadNext, poked, choiceNone, grant] at *
    | some request =>
        have choiceSome : (fabricGrantChoice poked).isSome = true := by
          cases choice : fabricGrantChoice poked with
          | none => simp [fabricGrantBits?, choice] at grant
          | some client => simp
        obtain ⟨client, choiceValue⟩ :
            ∃ client, fabricGrantChoice poked = some client := by
          cases choice : fabricGrantChoice poked with
          | none => simp [choice] at choiceSome
          | some client => exact ⟨client, rfl⟩
        have targetReady :=
          fabricGrantChoice_some_canEnq poked client choiceValue
        have oldInvalid : state.regs
            targetRequest.bits.sourceValidName 1 = 0#1 := by
          have acceptedZero : poked.regs
              targetRequest.bits.sourceAcceptedName 1 = 0#1 := by
            change poked.regs targetRequest.bits.sourceAcceptedName 1 ≠ 1#1
              at accepted
            bv_omega
          have pokedInvalid :=
            targetRequest.bits.sourceValid_zero_of_canEnq_notAccepted poked
              targetReady acceptedZero
          simpa using pokedInvalid
        simp [fabricTargetRequestPending, fabricTargetRequestProduced,
          fabricTargetRequestAccepted, accepted, stableValid, stablePayload,
          validNext, payloadNext, poked, choiceSome, grant, oldInvalid] at *

theorem fabricTargetRequestProduced_length_le_one (state : St) :
    (fabricTargetRequestProduced state).length ≤ 1 := by
  cases fabricGrantBits? state <;> simp [fabricTargetRequestProduced]

inductive FabricResponseRoute
  | cpu
  | dma
  deriving DecidableEq, Repr

def fabricResponseRouteChoice (state : St) : Option FabricResponseRoute :=
  if (Expr.and (.reg 1 "outstanding") targetResponse.bits.canDeq).eval state = 1#1 then
    if (Expr.eq (.reg 1 "route") (.lit 0#1)).eval state = 1#1 then
      if cpuResponse.bits.canEnq.eval state = 1#1 then some .cpu else none
    else if dmaResponse.bits.canEnq.eval state = 1#1 then some .dma else none
  else none

def fabricRoutedResponseBits? (state : St) :
    Option (BitVec (HwPacked.width Response)) :=
  (fabricResponseRouteChoice state).map (fun _ =>
    targetResponse.bits.deq.eval state)

theorem fabricResponseRouteChoice_at_most_one (state : St) :
    fabricResponseRouteChoice state = some .cpu →
      fabricResponseRouteChoice state ≠ some .dma := by
  intro cpuRoute dmaRoute
  rw [cpuRoute] at dmaRoute
  cases dmaRoute

set_option maxHeartbeats 600000 in
theorem fabricRouteResponseRule_refines (state acc : St) :
    let next := fabricRouteResponseRule.body.run state acc
    let choice := fabricResponseRouteChoice state
    next.regs targetResponse.bits.sinkPopName 1 =
        (if choice.isSome then 1#1 else acc.regs
          targetResponse.bits.sinkPopName 1) ∧
      next.regs cpuResponse.bits.sourceValidName 1 =
        (if choice = some .cpu then 1#1 else acc.regs
          cpuResponse.bits.sourceValidName 1) ∧
      next.regs dmaResponse.bits.sourceValidName 1 =
        (if choice = some .dma then 1#1 else acc.regs
          dmaResponse.bits.sourceValidName 1) ∧
      next.regs cpuResponse.bits.sourcePayloadName (HwPacked.width Response) =
        (if choice = some .cpu then targetResponse.bits.deq.eval state
          else acc.regs cpuResponse.bits.sourcePayloadName
            (HwPacked.width Response)) ∧
      next.regs dmaResponse.bits.sourcePayloadName (HwPacked.width Response) =
        (if choice = some .dma then targetResponse.bits.deq.eval state
          else acc.regs dmaResponse.bits.sourcePayloadName
            (HwPacked.width Response)) ∧
      next.regs "outstanding" 1 =
        (if choice.isSome then 0#1 else acc.regs "outstanding" 1) := by
  unfold fabricRouteResponseRule fabricResponseRouteChoice
  simp only [Act.run]
  repeat' first
    | split <;> rename_i condition
  all_goals simp_all [PackedChan.enq, PackedChan.pop, PackedChan.canEnq,
    PackedChan.canDeq, PackedChan.deq, PackedExpr.eval, Chan.enq, Chan.pop,
    Act.run, cpuResponse, dmaResponse, targetResponse, PackedChan.named,
    Chan.stem, Chan.sourcePayloadName, Chan.sourceValidName,
    Chan.sinkPopName, Expr.eval, bitvec1_and_eq_one]
  all_goals bv_decide

theorem fabricRoutedResponseBits_length_le_one (state : St) :
    (fabricRoutedResponseBits? state).toList.length ≤ 1 := by
  cases fabricRoutedResponseBits? state <;> simp

theorem fabricRoutedResponse_payload_unchanged (state : St)
    (response : BitVec (HwPacked.width Response))
    (routed : fabricRoutedResponseBits? state = some response) :
    response = targetResponse.bits.deq.eval state := by
  unfold fabricRoutedResponseBits? at routed
  cases route : fabricResponseRouteChoice state <;> simp [route] at routed
  exact routed.symm

theorem fabricResponseRoute_cpu_saved_route (state : St)
    (routed : fabricResponseRouteChoice state = some .cpu) :
    state.regs "route" 1 = 0#1 := by
  unfold fabricResponseRouteChoice at routed
  repeat' first
    | split at routed <;> rename_i condition
  all_goals simp_all [Expr.eval]

theorem fabricResponseRoute_dma_saved_route (state : St)
    (routed : fabricResponseRouteChoice state = some .dma) :
    state.regs "route" 1 = 1#1 := by
  unfold fabricResponseRouteChoice at routed
  repeat' first
    | split at routed <;> rename_i condition
  all_goals simp_all [Expr.eval]
  all_goals bv_omega

theorem fabric_cycleOpen_target_response_pop (state : St) (input : InEnv) :
    (fabric.cycleOpen input state).regs targetResponse.bits.sinkPopName 1 =
      if (fabricResponseRouteChoice
        (state.setInputs fabric.inputs input)).isSome then 1#1 else 0#1 := by
  let poked := state.setInputs fabric.inputs input
  have projected := fabric.cycle_regs_eq_support
    targetResponse.bits.sinkPopName 1 poked
  change (fabric.cycle poked).regs targetResponse.bits.sinkPopName 1 = _
  rw [projected, fabric_target_response_pop_support]
  simp only [List.foldl_cons, List.foldl_nil]
  let maintained := sinkMaintenanceRule targetResponse.bits |>.body.run poked poked
  have refined := fabricRouteResponseRule_refines poked maintained
  change (fabricRouteResponseRule.body.run poked maintained).regs
      targetResponse.bits.sinkPopName 1 = _
  rw [refined.1]
  simp [maintained, sinkMaintenanceRule, Act.run, poked]

theorem fabric_cycleOpen_target_response_payload (state : St) (input : InEnv) :
    (fabric.cycleOpen input state).regs targetResponse.bits.sinkPayloadName
        (HwPacked.width Response) =
      input targetResponse.bits.sinkPayloadName (HwPacked.width Response) := by
  let poked := state.setInputs fabric.inputs input
  have projected := fabric.cycle_regs_eq_support
    targetResponse.bits.sinkPayloadName (HwPacked.width Response) poked
  change (fabric.cycle poked).regs targetResponse.bits.sinkPayloadName
      (HwPacked.width Response) = _
  rw [projected, fabric_target_response_payload_support]
  rfl

theorem fabric_cycleOpen_cpu_response_payload (state : St) (input : InEnv) :
    (fabric.cycleOpen input state).regs cpuResponse.bits.sourcePayloadName
        (HwPacked.width Response) =
      if fabricResponseRouteChoice (state.setInputs fabric.inputs input) = some .cpu
      then targetResponse.bits.deq.eval (state.setInputs fabric.inputs input)
      else state.regs cpuResponse.bits.sourcePayloadName
        (HwPacked.width Response) := by
  let poked := state.setInputs fabric.inputs input
  have projected := fabric.cycle_regs_eq_support
    cpuResponse.bits.sourcePayloadName (HwPacked.width Response) poked
  change (fabric.cycle poked).regs cpuResponse.bits.sourcePayloadName
      (HwPacked.width Response) = _
  rw [projected, fabric_cpu_response_payload_support]
  simp only [List.foldl_cons, List.foldl_nil]
  have refined := fabricRouteResponseRule_refines poked poked
  rw [refined.2.2.2.1]
  rfl

theorem fabric_cycleOpen_dma_response_payload (state : St) (input : InEnv) :
    (fabric.cycleOpen input state).regs dmaResponse.bits.sourcePayloadName
        (HwPacked.width Response) =
      if fabricResponseRouteChoice (state.setInputs fabric.inputs input) = some .dma
      then targetResponse.bits.deq.eval (state.setInputs fabric.inputs input)
      else state.regs dmaResponse.bits.sourcePayloadName
        (HwPacked.width Response) := by
  let poked := state.setInputs fabric.inputs input
  have projected := fabric.cycle_regs_eq_support
    dmaResponse.bits.sourcePayloadName (HwPacked.width Response) poked
  change (fabric.cycle poked).regs dmaResponse.bits.sourcePayloadName
      (HwPacked.width Response) = _
  rw [projected, fabric_dma_response_payload_support]
  simp only [List.foldl_cons, List.foldl_nil]
  have refined := fabricRouteResponseRule_refines poked poked
  rw [refined.2.2.2.2.1]
  rfl

theorem fabric_cycleOpen_cpu_response_valid (state : St) (input : InEnv) :
    (fabric.cycleOpen input state).regs cpuResponse.bits.sourceValidName 1 =
      if fabricResponseRouteChoice (state.setInputs fabric.inputs input) = some .cpu
      then 1#1
      else if cpuResponse.bits.sourceAccepted.eval
          (state.setInputs fabric.inputs input) = 1#1
        then 0#1 else state.regs cpuResponse.bits.sourceValidName 1 := by
  let poked := state.setInputs fabric.inputs input
  have projected := fabric.cycle_regs_eq_support
    cpuResponse.bits.sourceValidName 1 poked
  change (fabric.cycle poked).regs cpuResponse.bits.sourceValidName 1 = _
  rw [projected, fabric_cpu_response_valid_support]
  simp only [List.foldl_cons, List.foldl_nil]
  let maintained := sourceMaintenanceRule cpuResponse.bits |>.body.run poked poked
  have refined := fabricRouteResponseRule_refines poked maintained
  change (fabricRouteResponseRule.body.run poked maintained).regs
      cpuResponse.bits.sourceValidName 1 = _
  rw [refined.2.1]
  by_cases routed : fabricResponseRouteChoice poked = some .cpu
  · simp [routed, poked]
  · by_cases accepted : cpuResponse.bits.sourceAccepted.eval poked = 1#1
    · simp [routed, accepted, maintained, sourceMaintenanceRule, Act.run, poked]
    · have stable : poked.regs cpuResponse.bits.sourceValidName 1 =
          state.regs cpuResponse.bits.sourceValidName 1 := by rfl
      simp [routed, accepted, maintained, sourceMaintenanceRule, Act.run,
        stable, poked]

theorem fabric_cycleOpen_dma_response_valid (state : St) (input : InEnv) :
    (fabric.cycleOpen input state).regs dmaResponse.bits.sourceValidName 1 =
      if fabricResponseRouteChoice (state.setInputs fabric.inputs input) = some .dma
      then 1#1
      else if dmaResponse.bits.sourceAccepted.eval
          (state.setInputs fabric.inputs input) = 1#1
        then 0#1 else state.regs dmaResponse.bits.sourceValidName 1 := by
  let poked := state.setInputs fabric.inputs input
  have projected := fabric.cycle_regs_eq_support
    dmaResponse.bits.sourceValidName 1 poked
  change (fabric.cycle poked).regs dmaResponse.bits.sourceValidName 1 = _
  rw [projected, fabric_dma_response_valid_support]
  simp only [List.foldl_cons, List.foldl_nil]
  let maintained := sourceMaintenanceRule dmaResponse.bits |>.body.run poked poked
  have refined := fabricRouteResponseRule_refines poked maintained
  change (fabricRouteResponseRule.body.run poked maintained).regs
      dmaResponse.bits.sourceValidName 1 = _
  rw [refined.2.2.1]
  by_cases routed : fabricResponseRouteChoice poked = some .dma
  · simp [routed, poked]
  · by_cases accepted : dmaResponse.bits.sourceAccepted.eval poked = 1#1
    · simp [routed, accepted, maintained, sourceMaintenanceRule, Act.run, poked]
    · have stable : poked.regs dmaResponse.bits.sourceValidName 1 =
          state.regs dmaResponse.bits.sourceValidName 1 := by rfl
      simp [routed, accepted, maintained, sourceMaintenanceRule, Act.run,
        stable, poked]

theorem fabric_cycleOpen_outstanding (state : St) (input : InEnv) :
    (fabric.cycleOpen input state).regs "outstanding" 1 =
      if (fabricGrantChoice (state.setInputs fabric.inputs input)).isSome then
        1#1
      else if (fabricResponseRouteChoice
          (state.setInputs fabric.inputs input)).isSome then
        0#1
      else state.regs "outstanding" 1 := by
  let poked := state.setInputs fabric.inputs input
  have projected := fabric.cycle_regs_eq_support "outstanding" 1 poked
  change (fabric.cycle poked).regs "outstanding" 1 = _
  rw [projected, fabric_outstanding_support]
  simp only [List.foldl_cons, List.foldl_nil]
  let routed := fabricRouteResponseRule.body.run poked poked
  have routeControl := fabricRouteResponseRule_refines poked poked
  have grantControl := fabricArbitrateRule_control poked routed
  change (fabricArbitrateRule.body.run poked routed).regs "outstanding" 1 = _
  rw [grantControl.2.2.2.1, routeControl.2.2.2.2.2]
  rfl

theorem fabric_cycleOpen_route (state : St) (input : InEnv) :
    (fabric.cycleOpen input state).regs "route" 1 =
      match fabricGrantChoice (state.setInputs fabric.inputs input) with
      | some .cpu => 0#1
      | some .dma => 1#1
      | none => state.regs "route" 1 := by
  let poked := state.setInputs fabric.inputs input
  have projected := fabric.cycle_regs_eq_support "route" 1 poked
  change (fabric.cycle poked).regs "route" 1 = _
  rw [projected, fabric_route_support]
  simp only [List.foldl_cons, List.foldl_nil]
  have control := fabricArbitrateRule_control poked poked
  rw [control.2.2.2.2]
  rfl

theorem fabricResponseRoute_cpu_canEnq (state : St)
    (routed : fabricResponseRouteChoice state = some .cpu) :
    cpuResponse.bits.canEnq.eval state = 1#1 := by
  unfold fabricResponseRouteChoice at routed
  repeat' first
    | split at routed <;> rename_i condition
  all_goals simp_all

theorem fabricResponseRoute_dma_canEnq (state : St)
    (routed : fabricResponseRouteChoice state = some .dma) :
    dmaResponse.bits.canEnq.eval state = 1#1 := by
  unfold fabricResponseRouteChoice at routed
  repeat' first
    | split at routed <;> rename_i condition
  all_goals simp_all

def fabricResponsePending (channel : PackedChan Response) (state : St) :
    List Response :=
  if state.regs channel.bits.sourceValidName 1 = 1#1 then
    [HwPacked.unpack (state.regs channel.bits.sourcePayloadName
      (HwPacked.width Response))]
  else []

def fabricResponseProduced (client : FabricResponseRoute) (state : St) :
    List Response :=
  if fabricResponseRouteChoice state = some client then
    [targetResponse.deq.eval state]
  else []

def fabricSavedClient (state : St) : FabricClient :=
  if state.regs "route" 1 = 0#1 then .cpu else .dma

def fabricOutstandingClients (state : St) : List FabricClient :=
  if state.regs "outstanding" 1 = 1#1 then [fabricSavedClient state] else []

def fabricGrantClients (state : St) : List FabricClient :=
  (fabricGrantChoice state).toList

def responseRouteClient : FabricResponseRoute → FabricClient
  | .cpu => .cpu
  | .dma => .dma

def fabricRoutedClients (state : St) : List FabricClient :=
  (fabricResponseRouteChoice state).map responseRouteClient |>.toList

theorem fabricGrantChoice_some_outstanding_zero (state : St)
    (client : FabricClient) (granted : fabricGrantChoice state = some client) :
    state.regs "outstanding" 1 = 0#1 := by
  unfold fabricGrantChoice at granted
  repeat' first
    | split at granted <;> rename_i condition
  all_goals simp_all [Expr.eval, bitvec1_and_eq_one]
  all_goals bv_omega

theorem fabricResponseRouteChoice_some_outstanding_one (state : St)
    (route : FabricResponseRoute)
    (routed : fabricResponseRouteChoice state = some route) :
    state.regs "outstanding" 1 = 1#1 := by
  unfold fabricResponseRouteChoice at routed
  repeat' first
    | split at routed <;> rename_i condition
  all_goals simp_all [Expr.eval, bitvec1_and_eq_one]

theorem fabricResponseRouteChoice_savedClient (state : St)
    (route : FabricResponseRoute)
    (routed : fabricResponseRouteChoice state = some route) :
    fabricSavedClient state = responseRouteClient route := by
  cases route with
  | cpu =>
      simp [fabricSavedClient,
        fabricResponseRoute_cpu_saved_route state routed, responseRouteClient]
  | dma =>
      have saved := fabricResponseRoute_dma_saved_route state routed
      simp [fabricSavedClient, saved, responseRouteClient]

/- The literal `outstanding` and `route` registers form a one-entry ledger:
every grant route is consumed exactly once by a response route. -/
set_option maxHeartbeats 800000 in
set_option maxRecDepth 100000 in
theorem fabric_route_control_ledger (state : St) (input : InEnv) :
    fabricOutstandingClients state ++
        fabricGrantClients (state.setInputs fabric.inputs input) =
      fabricRoutedClients (state.setInputs fabric.inputs input) ++
        fabricOutstandingClients (fabric.cycleOpen input state) := by
  let poked := state.setInputs fabric.inputs input
  have outstandingNext := fabric_cycleOpen_outstanding state input
  have routeNext := fabric_cycleOpen_route state input
  cases granted : fabricGrantChoice poked with
  | some client =>
      have oldZero := fabricGrantChoice_some_outstanding_zero poked client granted
      have stateOldZero : state.regs "outstanding" 1 = 0#1 := by
        simpa [poked] using oldZero
      have routedNone : fabricResponseRouteChoice poked = none := by
        cases routed : fabricResponseRouteChoice poked with
        | none => rfl
        | some route =>
            have oldOne := fabricResponseRouteChoice_some_outstanding_one
              poked route routed
            rw [oldZero] at oldOne
            contradiction
      cases client <;>
        simp [fabricOutstandingClients, fabricGrantClients,
          fabricRoutedClients, fabricSavedClient, responseRouteClient, poked,
          granted, routedNone, outstandingNext, routeNext, stateOldZero]
  | none =>
      cases routed : fabricResponseRouteChoice poked with
      | some route =>
          have oldOne := fabricResponseRouteChoice_some_outstanding_one
            poked route routed
          have stateOldOne : state.regs "outstanding" 1 = 1#1 := by
            simpa [poked] using oldOne
          have saved := fabricResponseRouteChoice_savedClient poked route routed
          have stateSaved : fabricSavedClient state = responseRouteClient route := by
            simpa [fabricSavedClient, poked] using saved
          simp [fabricOutstandingClients, fabricGrantClients,
            fabricRoutedClients, poked, granted, routed, outstandingNext,
            routeNext, stateOldOne, stateSaved]
      | none =>
          have outstandingStable :
              (fabric.cycleOpen input state).regs "outstanding" 1 =
                state.regs "outstanding" 1 := by
            simpa [poked, granted, routed] using outstandingNext
          have routeStable :
              (fabric.cycleOpen input state).regs "route" 1 =
                state.regs "route" 1 := by
            simpa [poked, granted] using routeNext
          simp only [fabricGrantClients, granted, Option.toList_none,
            List.append_nil, fabricRoutedClients, routed, Option.map_none]
          unfold fabricOutstandingClients
          rw [outstandingStable]
          by_cases occupied : state.regs "outstanding" 1 = 1#1
          · simp [poked, granted, routed, occupied, fabricSavedClient,
              routeStable]
          · simp [poked, granted, routed, occupied]

def fabricGrantObservations (state : St) : List (FabricClient × Request) :=
  match fabricGrantChoice state with
  | some .cpu => [(FabricClient.cpu, cpuRequest.deq.eval state)]
  | some .dma => [(FabricClient.dma, dmaRequest.deq.eval state)]
  | none => []

def fabricRoutedResponseObservations (state : St) :
    List (FabricClient × Response) :=
  match fabricResponseRouteChoice state with
  | some .cpu => [(FabricClient.cpu, targetResponse.deq.eval state)]
  | some .dma => [(FabricClient.dma, targetResponse.deq.eval state)]
  | none => []

theorem fabricGrantObservations_clients (state : St) :
    (fabricGrantObservations state).map Prod.fst = fabricGrantClients state := by
  cases choice : fabricGrantChoice state with
  | none => simp [fabricGrantObservations, fabricGrantClients, choice]
  | some client =>
      cases client <;>
        simp [fabricGrantObservations, fabricGrantClients, choice]

theorem fabricGrantObservations_requests (state : St) :
    (fabricGrantObservations state).map Prod.snd =
      fabricTargetRequestProduced state := by
  cases choice : fabricGrantChoice state with
  | none =>
      simp [fabricGrantObservations, fabricTargetRequestProduced,
        fabricGrantBits?, choice]
  | some client =>
      cases client <;>
        simp [fabricGrantObservations, fabricTargetRequestProduced,
          fabricGrantBits?, PackedChan.deq, PackedExpr.eval, choice]

theorem fabricRoutedResponseObservations_clients (state : St) :
    (fabricRoutedResponseObservations state).map Prod.fst =
      fabricRoutedClients state := by
  cases route : fabricResponseRouteChoice state with
  | none =>
      simp [fabricRoutedResponseObservations, fabricRoutedClients, route]
  | some client =>
      cases client <;>
        simp [fabricRoutedResponseObservations, fabricRoutedClients,
          responseRouteClient, route]

theorem fabricRoutedResponseObservations_responses (state : St) :
    (fabricRoutedResponseObservations state).map Prod.snd =
      (fabricRoutedResponseBits? state).toList.map HwPacked.unpack := by
  cases route : fabricResponseRouteChoice state with
  | none =>
      simp [fabricRoutedResponseObservations, fabricRoutedResponseBits?, route]
  | some client =>
      cases client <;>
        simp [fabricRoutedResponseObservations, fabricRoutedResponseBits?,
          PackedChan.deq, PackedExpr.eval, route]

def fabricResponseAccepted (channel : PackedChan Response) (state : St) :
    List Response :=
  if channel.bits.sourceAccepted.eval state = 1#1 then
    fabricResponsePending channel state
  else []

theorem fabric_cycleOpen_cpu_response_ledger (state : St) (input : InEnv)
    (acceptedLegal : cpuResponse.bits.sourceAccepted.eval
      (state.setInputs fabric.inputs input) = 1#1 →
      state.regs cpuResponse.bits.sourceValidName 1 = 1#1) :
    fabricResponsePending cpuResponse state ++
        fabricResponseProduced .cpu (state.setInputs fabric.inputs input) =
      fabricResponseAccepted cpuResponse (state.setInputs fabric.inputs input) ++
        fabricResponsePending cpuResponse (fabric.cycleOpen input state) := by
  let poked := state.setInputs fabric.inputs input
  have validNext := fabric_cycleOpen_cpu_response_valid state input
  have payloadNext := fabric_cycleOpen_cpu_response_payload state input
  have stableValid : poked.regs cpuResponse.bits.sourceValidName 1 =
      state.regs cpuResponse.bits.sourceValidName 1 := by rfl
  have stablePayload : poked.regs cpuResponse.bits.sourcePayloadName
      (HwPacked.width Response) =
      state.regs cpuResponse.bits.sourcePayloadName
        (HwPacked.width Response) := by rfl
  change (fabric.cycle poked).regs cpuResponse.bits.sourceValidName 1 = _
    at validNext
  change (fabric.cycle poked).regs cpuResponse.bits.sourcePayloadName
      (HwPacked.width Response) = _ at payloadNext
  change fabricResponsePending cpuResponse state ++
      fabricResponseProduced .cpu poked =
    fabricResponseAccepted cpuResponse poked ++
      fabricResponsePending cpuResponse (fabric.cycle poked)
  by_cases accepted : cpuResponse.bits.sourceAccepted.eval poked = 1#1
  · have valid := acceptedLegal accepted
    by_cases routed : fabricResponseRouteChoice poked = some .cpu
    · simp [fabricResponsePending, fabricResponseProduced,
        fabricResponseAccepted, accepted, valid, routed, stableValid,
        stablePayload, validNext, payloadNext, poked, PackedChan.deq,
        PackedExpr.eval] at *
    · simp [fabricResponsePending, fabricResponseProduced,
        fabricResponseAccepted, accepted, valid, routed, stableValid,
        stablePayload, validNext, payloadNext, poked] at *
  · by_cases routed : fabricResponseRouteChoice poked = some .cpu
    · have ready := fabricResponseRoute_cpu_canEnq poked routed
      have acceptedZero : poked.regs cpuResponse.bits.sourceAcceptedName 1 = 0#1 := by
        change poked.regs cpuResponse.bits.sourceAcceptedName 1 ≠ 1#1 at accepted
        bv_omega
      have invalidPoked := cpuResponse.bits.sourceValid_zero_of_canEnq_notAccepted
        poked ready acceptedZero
      have invalid : state.regs cpuResponse.bits.sourceValidName 1 = 0#1 := by
        simpa [stableValid] using invalidPoked
      simp [fabricResponsePending, fabricResponseProduced,
        fabricResponseAccepted, accepted, invalid, routed, stableValid,
        stablePayload, validNext, payloadNext, poked, PackedChan.deq,
        PackedExpr.eval] at *
    · simp [fabricResponsePending, fabricResponseProduced,
        fabricResponseAccepted, accepted, routed, stableValid,
        stablePayload, validNext, payloadNext, poked] at *

theorem fabric_cycleOpen_dma_response_ledger (state : St) (input : InEnv)
    (acceptedLegal : dmaResponse.bits.sourceAccepted.eval
      (state.setInputs fabric.inputs input) = 1#1 →
      state.regs dmaResponse.bits.sourceValidName 1 = 1#1) :
    fabricResponsePending dmaResponse state ++
        fabricResponseProduced .dma (state.setInputs fabric.inputs input) =
      fabricResponseAccepted dmaResponse (state.setInputs fabric.inputs input) ++
        fabricResponsePending dmaResponse (fabric.cycleOpen input state) := by
  let poked := state.setInputs fabric.inputs input
  have validNext := fabric_cycleOpen_dma_response_valid state input
  have payloadNext := fabric_cycleOpen_dma_response_payload state input
  have stableValid : poked.regs dmaResponse.bits.sourceValidName 1 =
      state.regs dmaResponse.bits.sourceValidName 1 := by rfl
  have stablePayload : poked.regs dmaResponse.bits.sourcePayloadName
      (HwPacked.width Response) =
      state.regs dmaResponse.bits.sourcePayloadName
        (HwPacked.width Response) := by rfl
  change (fabric.cycle poked).regs dmaResponse.bits.sourceValidName 1 = _
    at validNext
  change (fabric.cycle poked).regs dmaResponse.bits.sourcePayloadName
      (HwPacked.width Response) = _ at payloadNext
  change fabricResponsePending dmaResponse state ++
      fabricResponseProduced .dma poked =
    fabricResponseAccepted dmaResponse poked ++
      fabricResponsePending dmaResponse (fabric.cycle poked)
  by_cases accepted : dmaResponse.bits.sourceAccepted.eval poked = 1#1
  · have valid := acceptedLegal accepted
    by_cases routed : fabricResponseRouteChoice poked = some .dma
    · simp [fabricResponsePending, fabricResponseProduced,
        fabricResponseAccepted, accepted, valid, routed, stableValid,
        stablePayload, validNext, payloadNext, poked, PackedChan.deq,
        PackedExpr.eval] at *
    · simp [fabricResponsePending, fabricResponseProduced,
        fabricResponseAccepted, accepted, valid, routed, stableValid,
        stablePayload, validNext, payloadNext, poked] at *
  · by_cases routed : fabricResponseRouteChoice poked = some .dma
    · have ready := fabricResponseRoute_dma_canEnq poked routed
      have acceptedZero : poked.regs dmaResponse.bits.sourceAcceptedName 1 = 0#1 := by
        change poked.regs dmaResponse.bits.sourceAcceptedName 1 ≠ 1#1 at accepted
        bv_omega
      have invalidPoked := dmaResponse.bits.sourceValid_zero_of_canEnq_notAccepted
        poked ready acceptedZero
      have invalid : state.regs dmaResponse.bits.sourceValidName 1 = 0#1 := by
        simpa [stableValid] using invalidPoked
      simp [fabricResponsePending, fabricResponseProduced,
        fabricResponseAccepted, accepted, invalid, routed, stableValid,
        stablePayload, validNext, payloadNext, poked, PackedChan.deq,
        PackedExpr.eval] at *
    · simp [fabricResponsePending, fabricResponseProduced,
        fabricResponseAccepted, accepted, routed, stableValid,
        stablePayload, validNext, payloadNext, poked] at *

theorem fabricGrantChoice_at_most_one (state : St) :
    fabricGrantChoice state = some .cpu →
      fabricGrantChoice state ≠ some .dma := by
  intro cpuGrant dmaGrant
  rw [cpuGrant] at dmaGrant
  cases dmaGrant

theorem service_cycleOpen_memory_preserved_of_blocked (state : St) (input : InEnv)
    (blocked : targetRequest.canDeq.eval
        (state.setInputs service.inputs input) ≠ 1#1 ∨
      targetResponse.canEnq.eval
        (state.setInputs service.inputs input) ≠ 1#1 ∨
      audit.canEnq.eval (state.setInputs service.inputs input) ≠ 1#1) :
    serviceMemoryAt (service.cycleOpen input state) = serviceMemoryAt state := by
  funext address
  let poked := state.setInputs service.inputs input
  have projected := service.cycle_mems_eq_support registerFile.name poked
    address.toNat 32
  change serviceMemoryAt (service.cycle poked) address = serviceMemoryAt state address
  change (service.cycle poked).mems registerFile.name address.toNat 32 = _
  rw [projected, service_memory_support]
  simp only [List.foldl_cons, List.foldl_nil, serviceCommitRule, Act.run]
  change targetRequest.canDeq.eval poked ≠ 1#1 ∨
    targetResponse.canEnq.eval poked ≠ 1#1 ∨
    audit.canEnq.eval poked ≠ 1#1 at blocked
  rcases blocked with requestBlocked | responseBlocked | auditBlocked
  · rw [if_neg requestBlocked]
    rfl
  · by_cases requestReady : targetRequest.canDeq.eval poked = 1#1
    · rw [if_pos requestReady, if_neg responseBlocked]
      rfl
    · rw [if_neg requestReady]
      rfl
  · by_cases requestReady : targetRequest.canDeq.eval poked = 1#1
    · by_cases responseReady : targetResponse.canEnq.eval poked = 1#1
      · rw [if_pos requestReady, if_pos responseReady, if_neg auditBlocked]
        rfl
      · rw [if_pos requestReady, if_neg responseReady]
        rfl
    · rw [if_neg requestReady]
      rfl

def systemServiceState (state : system.State) : St := state.island "service"

def systemServiceMemory (state : system.State) : RegisterModel :=
  serviceMemoryAt (systemServiceState state)

theorem system_advance_service_memory_refines (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (ticks : event.fires "mem_clk" = true)
    (requestReady : targetRequest.canDeq.eval
      ((systemServiceState state).setInputs service.inputs
        (system.islandInput event state external "service")) = 1#1)
    (responseReady : targetResponse.canEnq.eval
      ((systemServiceState state).setInputs service.inputs
        (system.islandInput event state external "service")) = 1#1)
    (auditReady : audit.canEnq.eval
      ((systemServiceState state).setInputs service.inputs
        (system.islandInput event state external "service")) = 1#1) :
    systemServiceMemory (system.advance event external state) =
      (applyRequest (systemServiceMemory state)
        (serviceRequestAt ((systemServiceState state).setInputs service.inputs
          (system.islandInput event state external "service")))).1 := by
  have found : system.findIsland? "service" =
      some ⟨"service", "mem_clk", service⟩ := by rfl
  unfold systemServiceMemory systemServiceState
  rw [System.advance_island_ticked system event external state
    ⟨"service", "mem_clk", service⟩ found ticks]
  exact service_cycleOpen_memory_refines _ _ requestReady responseReady auditReady

theorem system_advance_service_emits_response (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (ticks : event.fires "mem_clk" = true)
    (requestReady : targetRequest.canDeq.eval
      ((systemServiceState state).setInputs service.inputs
        (system.islandInput event state external "service")) = 1#1)
    (responseReady : targetResponse.canEnq.eval
      ((systemServiceState state).setInputs service.inputs
        (system.islandInput event state external "service")) = 1#1)
    (auditReady : audit.canEnq.eval
      ((systemServiceState state).setInputs service.inputs
        (system.islandInput event state external "service")) = 1#1) :
    HwPacked.unpack (((system.advance event external state).island "service").regs
      targetResponse.bits.sourcePayloadName (HwPacked.width Response)) =
      serviceResponseAt ((systemServiceState state).setInputs service.inputs
        (system.islandInput event state external "service")) := by
  have found : system.findIsland? "service" =
      some ⟨"service", "mem_clk", service⟩ := by rfl
  rw [System.advance_island_ticked system event external state
    ⟨"service", "mem_clk", service⟩ found ticks]
  exact service_cycleOpen_emits_response _ _ requestReady responseReady auditReady

theorem system_advance_service_emits_audit (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (ticks : event.fires "mem_clk" = true)
    (requestReady : targetRequest.canDeq.eval
      ((systemServiceState state).setInputs service.inputs
        (system.islandInput event state external "service")) = 1#1)
    (responseReady : targetResponse.canEnq.eval
      ((systemServiceState state).setInputs service.inputs
        (system.islandInput event state external "service")) = 1#1)
    (auditReady : audit.canEnq.eval
      ((systemServiceState state).setInputs service.inputs
        (system.islandInput event state external "service")) = 1#1) :
    HwPacked.unpack (((system.advance event external state).island "service").regs
      audit.bits.sourcePayloadName (HwPacked.width CommitRecord)) =
      serviceCommitAt ((systemServiceState state).setInputs service.inputs
        (system.islandInput event state external "service")) := by
  have found : system.findIsland? "service" =
      some ⟨"service", "mem_clk", service⟩ := by rfl
  rw [System.advance_island_ticked system event external state
    ⟨"service", "mem_clk", service⟩ found ticks]
  exact service_cycleOpen_emits_audit _ _ requestReady responseReady auditReady

def systemServiceCommitRequest? (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) : Option Request :=
  if event.fires "mem_clk" = true then
    let poked := (systemServiceState state).setInputs service.inputs
      (system.islandInput event state external "service")
    if targetRequest.canDeq.eval poked = 1#1 ∧
        targetResponse.canEnq.eval poked = 1#1 ∧
        audit.canEnq.eval poked = 1#1 then
      some (serviceRequestAt poked)
    else none
  else none

theorem system_service_commit_observations (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) (request : Request)
    (committed : systemServiceCommitRequest? state event external = some request) :
    let next := system.advance event external state
    HwPacked.unpack ((next.island "service").regs
        targetResponse.bits.sourcePayloadName (HwPacked.width Response)) =
        (applyRequest (systemServiceMemory state) request).2.1 ∧
      HwPacked.unpack ((next.island "service").regs
        audit.bits.sourcePayloadName (HwPacked.width CommitRecord)) =
        (applyRequest (systemServiceMemory state) request).2.2 ∧
      systemServiceMemory next =
        (applyRequest (systemServiceMemory state) request).1 := by
  let poked := (systemServiceState state).setInputs service.inputs
    (system.islandInput event state external "service")
  have ticks : event.fires "mem_clk" = true := by
    by_contra notTicks
    have ticksFalse : event.fires "mem_clk" ≠ true := notTicks
    simp [systemServiceCommitRequest?, ticksFalse] at committed
  have enabled : targetRequest.canDeq.eval poked = 1#1 ∧
      targetResponse.canEnq.eval poked = 1#1 ∧
      audit.canEnq.eval poked = 1#1 := by
    by_contra notEnabled
    simp [systemServiceCommitRequest?, ticks, poked, notEnabled] at committed
  have requestEq : serviceRequestAt poked = request := by
    simpa [systemServiceCommitRequest?, ticks, poked, enabled] using committed
  rcases enabled with ⟨requestReady, responseReady, auditReady⟩
  have response := system_advance_service_emits_response state event external ticks
    requestReady responseReady auditReady
  have auditRecord := system_advance_service_emits_audit state event external ticks
    requestReady responseReady auditReady
  have memory := system_advance_service_memory_refines state event external ticks
    requestReady responseReady auditReady
  have responseModel := serviceResponseAt_eq_model poked
  have auditModel := serviceCommitAt_eq_model poked
  have pokedMemory : serviceMemoryAt poked = systemServiceMemory state := by
    rfl
  rw [requestEq, pokedMemory] at responseModel auditModel
  rw [requestEq] at memory
  exact ⟨response.trans responseModel, auditRecord.trans auditModel, memory⟩

theorem system_advance_service_memory_step (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    systemServiceMemory (system.advance event external state) =
      match systemServiceCommitRequest? state event external with
      | some request => (applyRequest (systemServiceMemory state) request).1
      | none => systemServiceMemory state := by
  by_cases ticks : event.fires "mem_clk" = true
  · let poked := (systemServiceState state).setInputs service.inputs
      (system.islandInput event state external "service")
    by_cases requestReady : targetRequest.canDeq.eval poked = 1#1
    · by_cases responseReady : targetResponse.canEnq.eval poked = 1#1
      · by_cases auditReady : audit.canEnq.eval poked = 1#1
        · simp only [systemServiceCommitRequest?, ticks, if_true]
          rw [if_pos ⟨requestReady, responseReady, auditReady⟩]
          exact system_advance_service_memory_refines state event external ticks
            requestReady responseReady auditReady
        · simp only [systemServiceCommitRequest?, ticks, if_true]
          rw [if_neg (by aesop)]
          have found : system.findIsland? "service" =
              some ⟨"service", "mem_clk", service⟩ := by rfl
          unfold systemServiceMemory systemServiceState
          rw [System.advance_island_ticked system event external state
            ⟨"service", "mem_clk", service⟩ found ticks]
          exact service_cycleOpen_memory_preserved_of_blocked _ _
            (Or.inr (Or.inr auditReady))
      · simp only [systemServiceCommitRequest?, ticks, if_true]
        rw [if_neg (by aesop)]
        have found : system.findIsland? "service" =
            some ⟨"service", "mem_clk", service⟩ := by rfl
        unfold systemServiceMemory systemServiceState
        rw [System.advance_island_ticked system event external state
          ⟨"service", "mem_clk", service⟩ found ticks]
        exact service_cycleOpen_memory_preserved_of_blocked _ _
          (Or.inr (Or.inl responseReady))
    · simp only [systemServiceCommitRequest?, ticks, if_true]
      rw [if_neg (by aesop)]
      have found : system.findIsland? "service" =
          some ⟨"service", "mem_clk", service⟩ := by rfl
      unfold systemServiceMemory systemServiceState
      rw [System.advance_island_ticked system event external state
        ⟨"service", "mem_clk", service⟩ found ticks]
      exact service_cycleOpen_memory_preserved_of_blocked _ _
        (Or.inl requestReady)
  · have unticked : event.fires "mem_clk" = false :=
      Bool.eq_false_of_not_eq_true ticks
    simp only [systemServiceCommitRequest?, ticks, if_false]
    have found : system.findIsland? "service" =
        some ⟨"service", "mem_clk", service⟩ := by rfl
    unfold systemServiceMemory systemServiceState
    exact congrArg serviceMemoryAt <|
      System.advance_island_unticked system event external state
        ⟨"service", "mem_clk", service⟩ found unticked

def systemServiceCommitRequestsFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List Request
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      let next := system.advance event external state
      match systemServiceCommitRequest? state event external with
      | some request => request :: systemServiceCommitRequestsFrom inputs next rest
      | none => systemServiceCommitRequestsFrom inputs next rest

structure ServiceCommitHistory where
  requests : List Request
  responses : List Response
  auditRecords : List CommitRecord

def systemServiceCommitHistoryFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → ServiceCommitHistory
  | _, [] => ⟨[], [], []⟩
  | state, event :: rest =>
      let external := inputs state.time
      let next := system.advance event external state
      let later := systemServiceCommitHistoryFrom inputs next rest
      match systemServiceCommitRequest? state event external with
      | some request =>
          ⟨request :: later.requests,
            HwPacked.unpack ((next.island "service").regs
              targetResponse.bits.sourcePayloadName (HwPacked.width Response)) ::
              later.responses,
            HwPacked.unpack ((next.island "service").regs
              audit.bits.sourcePayloadName (HwPacked.width CommitRecord)) ::
              later.auditRecords⟩
      | none => later

@[simp] theorem serviceCommitHistory_requests (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    (systemServiceCommitHistoryFrom inputs state events).requests =
      systemServiceCommitRequestsFrom inputs state events := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemServiceCommitHistoryFrom, systemServiceCommitRequestsFrom]
      let external := inputs state.time
      let next := system.advance event external state
      cases systemServiceCommitRequest? state event external with
      | none => exact ih (system.advance event (inputs state.time) state)
      | some request =>
          exact congrArg (List.cons request)
            (ih (system.advance event (inputs state.time) state))

theorem system_service_commit_history_refines (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    let history := systemServiceCommitHistoryFrom inputs state events
    let modeled := applyRequests (systemServiceMemory state) history.requests
    history.responses = modeled.2.1 ∧
      history.auditRecords = modeled.2.2 ∧
      systemServiceMemory (system.runEventsFrom inputs state events) = modeled.1 := by
  induction events generalizing state with
  | nil => simp [systemServiceCommitHistoryFrom, System.runEventsFrom, applyRequests]
  | cons event rest ih =>
      simp only [systemServiceCommitHistoryFrom, System.runEventsFrom]
      let external := inputs state.time
      let next := system.advance event external state
      let later := systemServiceCommitHistoryFrom inputs next rest
      have laterRefines := ih next
      have memoryStep := system_advance_service_memory_step state event external
      cases committed : systemServiceCommitRequest? state event external with
      | none =>
          rw [committed] at memoryStep
          simp only at memoryStep
          dsimp only at laterRefines
          simp only
          change later.responses =
              (applyRequests (systemServiceMemory state) later.requests).2.1 ∧
            later.auditRecords =
              (applyRequests (systemServiceMemory state) later.requests).2.2 ∧
            systemServiceMemory (system.runEventsFrom inputs next rest) =
              (applyRequests (systemServiceMemory state) later.requests).1
          rw [← memoryStep]
          exact laterRefines
      | some request =>
          have observed := system_service_commit_observations state event external
            request committed
          rcases observed with ⟨response, auditRecord, nextMemory⟩
          dsimp only at laterRefines
          simp only
          change
            HwPacked.unpack ((next.island "service").regs
                targetResponse.bits.sourcePayloadName (HwPacked.width Response)) ::
                later.responses =
              (applyRequests (systemServiceMemory state)
                (request :: later.requests)).2.1 ∧
            HwPacked.unpack ((next.island "service").regs
                audit.bits.sourcePayloadName (HwPacked.width CommitRecord)) ::
                later.auditRecords =
              (applyRequests (systemServiceMemory state)
                (request :: later.requests)).2.2 ∧
            systemServiceMemory (system.runEventsFrom inputs next rest) =
              (applyRequests (systemServiceMemory state)
                (request :: later.requests)).1
          simp only [applyRequests]
          rw [response, auditRecord]
          rw [← nextMemory]
          simpa only [List.cons.injEq, true_and] using laterRefines

theorem system_runEvents_service_memory_refines (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemServiceMemory (system.runEventsFrom inputs state events) =
      (applyRequests (systemServiceMemory state)
        (systemServiceCommitRequestsFrom inputs state events)).1 := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [System.runEventsFrom, systemServiceCommitRequestsFrom]
      let external := inputs state.time
      let next := system.advance event external state
      have step := system_advance_service_memory_step state event external
      cases request? : systemServiceCommitRequest? state event external with
      | none =>
          rw [request?] at step
          change systemServiceMemory (system.runEventsFrom inputs next rest) =
            (applyRequests (systemServiceMemory state)
              (systemServiceCommitRequestsFrom inputs next rest)).1
          calc
            _ = (applyRequests (systemServiceMemory next)
                (systemServiceCommitRequestsFrom inputs next rest)).1 := ih next
            _ = _ := by rw [step]

      | some request =>
          rw [request?] at step
          change systemServiceMemory (system.runEventsFrom inputs next rest) =
            (applyRequests (applyRequest (systemServiceMemory state) request).1
              (systemServiceCommitRequestsFrom inputs next rest)).1
          calc
            _ = (applyRequests (systemServiceMemory next)
                (systemServiceCommitRequestsFrom inputs next rest)).1 := ih next
            _ = _ := by rw [step]

theorem systemServiceMemory_reset :
    systemServiceMemory system.reset = initialMemory := by
  funext address
  have found : system.findIsland? "service" =
      some ⟨"service", "mem_clk", service⟩ := by rfl
  unfold systemServiceMemory systemServiceState serviceMemoryAt initialMemory
  simp only [System.reset]
  rw [found]
  simp [service, serviceBody, PackedChan.withSink, PackedChan.withSource,
    Chan.withSink, Chan.withSource, Design.reset, registerFile, Mem.decl]

theorem reset_service_commit_history_refines (events : List NamedClockEvent) :
    let history := systemServiceCommitHistoryFrom noInputs system.reset events
    history.responses = modelResponses history.requests ∧
      history.auditRecords = modelCommits history.requests ∧
      systemServiceMemory (system.runEventsFrom noInputs system.reset events) =
        committedMemory history.requests := by
  have refined := system_service_commit_history_refines noInputs system.reset events
  rw [systemServiceMemory_reset] at refined
  exact refined

theorem serviceInput_targetResponseAccepted (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    system.islandInput event state external "service"
        targetResponse.bits.sourceAcceptedName 1 =
      if (system.connectionResult event state targetResponseConnection).accepted
      then 1#1 else 0#1 := by
  simp [System.islandInput, System.inputFor, System.connectionInput?,
    System.connectionResult,
    connectionInventory, List.findSome?, cpuRequestConnection,
    cpuResponseConnection, dmaRequestConnection, dmaResponseConnection,
    targetRequestConnection, targetResponseConnection, auditConnection,
    cpuRequest, cpuResponse, dmaRequest, dmaResponse, targetRequest,
    targetResponse, audit, PackedChan.named, Chan.sourceAcceptedName, Chan.sourceReadyName,
    Chan.sinkValidName, Chan.sinkPayloadName, Chan.stem, System.boolValue]

theorem serviceInput_auditAccepted (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    system.islandInput event state external "service"
        audit.bits.sourceAcceptedName 1 =
      if (system.connectionResult event state auditConnection).accepted
      then 1#1 else 0#1 := by
  simp [System.islandInput, System.inputFor, System.connectionInput?,
    System.connectionResult,
    connectionInventory, List.findSome?, cpuRequestConnection,
    cpuResponseConnection, dmaRequestConnection, dmaResponseConnection,
    targetRequestConnection, targetResponseConnection, auditConnection,
    cpuRequest, cpuResponse, dmaRequest, dmaResponse, targetRequest,
    targetResponse, audit, PackedChan.named,
    Chan.sourceAcceptedName, Chan.sourceReadyName, Chan.sinkValidName,
    Chan.sinkPayloadName, Chan.stem, System.boolValue]

theorem serviceInput_targetRequestValid (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    system.islandInput event state external "service"
        targetRequest.bits.sinkValidName 1 =
      if (system.channelState state targetRequestConnection).isEmpty
      then 0#1 else 1#1 := by
  simp [System.islandInput, System.inputFor, System.connectionInput?,
    System.channelState, connectionInventory, List.findSome?,
    cpuRequestConnection, cpuResponseConnection, dmaRequestConnection,
    dmaResponseConnection, targetRequestConnection, targetResponseConnection,
    auditConnection, cpuRequest, cpuResponse, dmaRequest, dmaResponse,
    targetRequest, targetResponse, audit, PackedChan.named,
    Chan.sourceAcceptedName, Chan.sourceReadyName, Chan.sinkValidName,
    Chan.sinkPayloadName, Chan.stem, System.boolValue]

theorem serviceInput_targetRequestPayload (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    system.islandInput event state external "service"
        targetRequest.bits.sinkPayloadName (HwPacked.width Request) =
      (system.channelState state targetRequestConnection).head?.getD 0 := by
  simp [System.islandInput, System.inputFor, System.connectionInput?,
    System.channelState, connectionInventory, List.findSome?,
    cpuRequestConnection, cpuResponseConnection, dmaRequestConnection,
    dmaResponseConnection, targetRequestConnection, targetResponseConnection,
    auditConnection, cpuRequest, cpuResponse, dmaRequest, dmaResponse,
    targetRequest, targetResponse, audit, PackedChan.named,
    Chan.sourceAcceptedName, Chan.sourceReadyName, Chan.sinkValidName,
    Chan.sinkPayloadName, Chan.stem, System.boolValue]

def systemFabricState (state : system.State) : St := state.island "fabric"

def systemFabricOutstandingClients (state : system.State) : List FabricClient :=
  fabricOutstandingClients (systemFabricState state)

def systemFabricGrantClientsAt (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) : List FabricClient :=
  if event.fires "cpu_fabric_clk" = true then
    fabricGrantClients ((systemFabricState state).setInputs fabric.inputs
      (system.islandInput event state external "fabric"))
  else []

def systemFabricRoutedClientsAt (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) : List FabricClient :=
  if event.fires "cpu_fabric_clk" = true then
    fabricRoutedClients ((systemFabricState state).setInputs fabric.inputs
      (system.islandInput event state external "fabric"))
  else []

theorem system_fabric_route_control_ledger_step (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    systemFabricOutstandingClients state ++
        systemFabricGrantClientsAt state event external =
      systemFabricRoutedClientsAt state event external ++
        systemFabricOutstandingClients
          (system.advance event external state) := by
  by_cases ticks : event.fires "cpu_fabric_clk" = true
  · let input := system.islandInput event state external "fabric"
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have nextIsland := System.advance_island_ticked system event external state
      ⟨"fabric", "cpu_fabric_clk", fabric⟩ found ticks
    have localLedger := fabric_route_control_ledger (systemFabricState state) input
    simpa [systemFabricOutstandingClients, systemFabricGrantClientsAt,
      systemFabricRoutedClientsAt, ticks, input, systemFabricState,
      nextIsland] using localLedger
  · have unticked : event.fires "cpu_fabric_clk" = false :=
      Bool.eq_false_of_not_eq_true ticks
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have nextIsland := System.advance_island_unticked system event external state
      ⟨"fabric", "cpu_fabric_clk", fabric⟩ found unticked
    simp [systemFabricOutstandingClients, systemFabricGrantClientsAt,
      systemFabricRoutedClientsAt, ticks, systemFabricState, nextIsland]

def systemFabricGrantClientTraceFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List FabricClient
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemFabricGrantClientsAt state event external ++
        systemFabricGrantClientTraceFrom inputs
          (system.advance event external state) rest

def systemFabricRoutedClientTraceFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List FabricClient
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemFabricRoutedClientsAt state event external ++
        systemFabricRoutedClientTraceFrom inputs
          (system.advance event external state) rest

theorem system_fabric_route_control_ledger (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemFabricOutstandingClients state ++
        systemFabricGrantClientTraceFrom inputs state events =
      systemFabricRoutedClientTraceFrom inputs state events ++
        systemFabricOutstandingClients
          (system.runEventsFrom inputs state events) := by
  induction events generalizing state with
  | nil => simp [systemFabricGrantClientTraceFrom,
      systemFabricRoutedClientTraceFrom, System.runEventsFrom]
  | cons event rest ih =>
      simp only [systemFabricGrantClientTraceFrom,
        systemFabricRoutedClientTraceFrom, System.runEventsFrom]
      let external := inputs state.time
      let next := system.advance event external state
      rw [← List.append_assoc,
        system_fabric_route_control_ledger_step state event external]
      simpa only [List.append_assoc] using
        congrArg (fun clients =>
          systemFabricRoutedClientsAt state event external ++ clients) (ih next)

@[simp] theorem systemFabricOutstandingClients_reset :
    systemFabricOutstandingClients system.reset = [] := by rfl

theorem reset_fabric_route_control_ledger (events : List NamedClockEvent) :
    systemFabricGrantClientTraceFrom noInputs system.reset events =
      systemFabricRoutedClientTraceFrom noInputs system.reset events ++
        systemFabricOutstandingClients
          (system.runEventsFrom noInputs system.reset events) := by
  simpa using system_fabric_route_control_ledger noInputs system.reset events

theorem fabricInput_targetRequestAccepted (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    system.islandInput event state external "fabric"
        targetRequest.bits.sourceAcceptedName 1 =
      if (system.connectionResult event state targetRequestConnection).accepted
      then 1#1 else 0#1 := by
  simp [System.islandInput, System.inputFor, System.connectionInput?,
    System.connectionResult, connectionInventory, List.findSome?,
    cpuRequestConnection, cpuResponseConnection, dmaRequestConnection,
    dmaResponseConnection, targetRequestConnection, targetResponseConnection,
    auditConnection, cpuRequest, cpuResponse, dmaRequest, dmaResponse,
    targetRequest, targetResponse, audit, PackedChan.named,
    Chan.sourceAcceptedName, Chan.sourceReadyName, Chan.sinkValidName,
    Chan.sinkPayloadName, Chan.stem, System.boolValue]

theorem fabricInput_cpuResponseAccepted (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    system.islandInput event state external "fabric"
        cpuResponse.bits.sourceAcceptedName 1 =
      if (system.connectionResult event state cpuResponseConnection).accepted
      then 1#1 else 0#1 := by
  simp [System.islandInput, System.inputFor, System.connectionInput?,
    System.connectionResult, connectionInventory, List.findSome?,
    cpuRequestConnection, cpuResponseConnection, dmaRequestConnection,
    dmaResponseConnection, targetRequestConnection, targetResponseConnection,
    auditConnection, cpuRequest, cpuResponse, dmaRequest, dmaResponse,
    targetRequest, targetResponse, audit, PackedChan.named,
    Chan.sourceAcceptedName, Chan.sourceReadyName, Chan.sinkValidName,
    Chan.sinkPayloadName, Chan.stem, System.boolValue]

theorem fabricInput_dmaResponseAccepted (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    system.islandInput event state external "fabric"
        dmaResponse.bits.sourceAcceptedName 1 =
      if (system.connectionResult event state dmaResponseConnection).accepted
      then 1#1 else 0#1 := by
  simp [System.islandInput, System.inputFor, System.connectionInput?,
    System.connectionResult, connectionInventory, List.findSome?,
    cpuRequestConnection, cpuResponseConnection, dmaRequestConnection,
    dmaResponseConnection, targetRequestConnection, targetResponseConnection,
    auditConnection, cpuRequest, cpuResponse, dmaRequest, dmaResponse,
    targetRequest, targetResponse, audit, PackedChan.named,
    Chan.sourceAcceptedName, Chan.sourceReadyName, Chan.sinkValidName,
    Chan.sinkPayloadName, Chan.stem, System.boolValue]

def fabricClientRequestChannel : FabricClient → PackedChan Request
  | .cpu => cpuRequest
  | .dma => dmaRequest

def fabricClientRequestConnection : FabricClient → SystemConnection
  | .cpu => cpuRequestConnection
  | .dma => dmaRequestConnection

def systemFabricClientRequestQueue (client : FabricClient)
    (state : system.State) : List (BitVec (HwPacked.width Request)) :=
  match client with
  | .cpu => system.channelState state cpuRequestConnection
  | .dma => system.channelState state dmaRequestConnection

theorem fabricInput_clientRequestValid (client : FabricClient)
    (state : system.State) (event : NamedClockEvent)
    (external : String → InEnv) :
    system.islandInput event state external "fabric"
        (fabricClientRequestChannel client).bits.sinkValidName 1 =
      if (systemFabricClientRequestQueue client state).isEmpty
      then 0#1 else 1#1 := by
  cases client <;>
    simp [fabricClientRequestChannel, fabricClientRequestConnection,
      System.islandInput, System.inputFor, System.connectionInput?,
      System.channelState, systemFabricClientRequestQueue,
      connectionInventory, List.findSome?,
      cpuRequestConnection, cpuResponseConnection, dmaRequestConnection,
      dmaResponseConnection, targetRequestConnection, targetResponseConnection,
      auditConnection, cpuRequest, cpuResponse, dmaRequest, dmaResponse,
      targetRequest, targetResponse, audit, PackedChan.named,
      Chan.sourceAcceptedName, Chan.sourceReadyName, Chan.sinkValidName,
      Chan.sinkPayloadName, Chan.stem, System.boolValue]

theorem fabricInput_clientRequestPayload (client : FabricClient)
    (state : system.State) (event : NamedClockEvent)
    (external : String → InEnv) :
    system.islandInput event state external "fabric"
        (fabricClientRequestChannel client).bits.sinkPayloadName
          (HwPacked.width Request) =
      (systemFabricClientRequestQueue client state).head?.getD 0 := by
  cases client <;>
    simp [fabricClientRequestChannel, fabricClientRequestConnection,
      System.islandInput, System.inputFor, System.connectionInput?,
      System.channelState, systemFabricClientRequestQueue,
      connectionInventory, List.findSome?,
      cpuRequestConnection, cpuResponseConnection, dmaRequestConnection,
      dmaResponseConnection, targetRequestConnection, targetResponseConnection,
      auditConnection, cpuRequest, cpuResponse, dmaRequest, dmaResponse,
      targetRequest, targetResponse, audit, PackedChan.named,
      Chan.sourceAcceptedName, Chan.sourceReadyName, Chan.sinkValidName,
      Chan.sinkPayloadName, Chan.stem, System.boolValue]

def systemFabricClientRequestPending (client : FabricClient)
    (state : system.State) : List Request :=
  let channel := fabricClientRequestChannel client
  if (systemFabricState state).regs channel.bits.sinkPopName 1 = 1#1 then
    [HwPacked.unpack ((systemFabricState state).regs
      channel.bits.sinkPayloadName (HwPacked.width Request))]
  else []

def FabricClientRequestSinkCoherent (client : FabricClient)
    (state : system.State) : Prop :=
  let channel := fabricClientRequestChannel client
  (systemFabricState state).regs channel.bits.sinkPopName 1 = 1#1 →
    (systemFabricClientRequestQueue client state).head? =
      some ((systemFabricState state).regs
        channel.bits.sinkPayloadName (HwPacked.width Request))

def systemFabricClientRequestsGrantedAt (client : FabricClient)
    (state : system.State) (event : NamedClockEvent)
    (external : String → InEnv) : List Request :=
  if event.fires "cpu_fabric_clk" = true then
    let poked := (systemFabricState state).setInputs fabric.inputs
      (system.islandInput event state external "fabric")
    if fabricGrantChoice poked = some client then
      [match client with
       | .cpu => cpuRequest.deq.eval poked
       | .dma => dmaRequest.deq.eval poked]
    else []
  else []

def systemClientRequestsDeliveredAt (client : FabricClient)
    (state : system.State) (event : NamedClockEvent) : List Request :=
  match client with
  | .cpu => (system.connectionResult event state
      cpuRequestConnection).delivered.toList.map HwPacked.unpack
  | .dma => (system.connectionResult event state
      dmaRequestConnection).delivered.toList.map HwPacked.unpack

@[simp] theorem systemFabricClientRequestPending_reset
    (client : FabricClient) :
    systemFabricClientRequestPending client system.reset = [] := by
  cases client <;> rfl

theorem fabricClientRequestSinkCoherent_reset (client : FabricClient) :
    FabricClientRequestSinkCoherent client system.reset := by
  cases client
  · intro pending
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    change (system.reset.island "fabric").regs
      cpuRequest.bits.sinkPopName 1 = 1#1 at pending
    simp only [System.reset] at pending
    rw [found] at pending
    simp [fabric, fabricBody, PackedChan.withSink, PackedChan.withSource,
      Chan.withSink, Chan.withSource, Design.reset, cpuRequest, dmaRequest,
      targetRequest, targetResponse, cpuResponse, dmaResponse,
      PackedChan.named, Chan.sinkPopName, Chan.sourceValidName,
      Chan.sourcePayloadName, Chan.stem] at pending
  · intro pending
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    change (system.reset.island "fabric").regs
      dmaRequest.bits.sinkPopName 1 = 1#1 at pending
    simp only [System.reset] at pending
    rw [found] at pending
    simp [fabric, fabricBody, PackedChan.withSink, PackedChan.withSource,
      Chan.withSink, Chan.withSource, Design.reset, cpuRequest, dmaRequest,
      targetRequest, targetResponse, cpuResponse, dmaResponse,
      PackedChan.named, Chan.sinkPopName, Chan.sourceValidName,
      Chan.sourcePayloadName, Chan.stem] at pending

theorem system_advance_fabric_client_request_pop (client : FabricClient)
    (state : system.State) (event : NamedClockEvent)
    (external : String → InEnv)
    (ticks : event.fires "cpu_fabric_clk" = true) :
    let channel := fabricClientRequestChannel client
    ((system.advance event external state).island "fabric").regs
        channel.bits.sinkPopName 1 =
      if fabricGrantChoice
          ((systemFabricState state).setInputs fabric.inputs
            (system.islandInput event state external "fabric")) = some client
      then 1#1 else 0#1 := by
  have found : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  rw [System.advance_island_ticked system event external state
    ⟨"fabric", "cpu_fabric_clk", fabric⟩ found ticks]
  cases client
  · exact fabric_cycleOpen_cpu_request_pop _ _
  · exact fabric_cycleOpen_dma_request_pop _ _

theorem system_advance_fabric_client_request_payload (client : FabricClient)
    (state : system.State) (event : NamedClockEvent)
    (external : String → InEnv)
    (ticks : event.fires "cpu_fabric_clk" = true) :
    let channel := fabricClientRequestChannel client
    ((system.advance event external state).island "fabric").regs
        channel.bits.sinkPayloadName (HwPacked.width Request) =
      (systemFabricClientRequestQueue client state).head?.getD 0 := by
  have found : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  rw [System.advance_island_ticked system event external state
    ⟨"fabric", "cpu_fabric_clk", fabric⟩ found ticks]
  cases client
  · dsimp [fabricClientRequestChannel, systemFabricClientRequestQueue]
    rw [fabric_cycleOpen_cpu_request_payload]
    exact fabricInput_clientRequestPayload .cpu state event external
  · dsimp [fabricClientRequestChannel, systemFabricClientRequestQueue]
    rw [fabric_cycleOpen_dma_request_payload]
    exact fabricInput_clientRequestPayload .dma state event external

theorem fabricInput_targetResponseValid (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    system.islandInput event state external "fabric"
        targetResponse.bits.sinkValidName 1 =
      if (system.channelState state targetResponseConnection).isEmpty
      then 0#1 else 1#1 := by
  simp [System.islandInput, System.inputFor, System.connectionInput?,
    System.channelState, connectionInventory, List.findSome?,
    cpuRequestConnection, cpuResponseConnection, dmaRequestConnection,
    dmaResponseConnection, targetRequestConnection, targetResponseConnection,
    auditConnection, cpuRequest, cpuResponse, dmaRequest, dmaResponse,
    targetRequest, targetResponse, audit, PackedChan.named,
    Chan.sourceAcceptedName, Chan.sourceReadyName, Chan.sinkValidName,
    Chan.sinkPayloadName, Chan.stem, System.boolValue]

theorem fabricInput_targetResponsePayload (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    system.islandInput event state external "fabric"
        targetResponse.bits.sinkPayloadName (HwPacked.width Response) =
      (system.channelState state targetResponseConnection).head?.getD 0 := by
  simp [System.islandInput, System.inputFor, System.connectionInput?,
    System.channelState, connectionInventory, List.findSome?,
    cpuRequestConnection, cpuResponseConnection, dmaRequestConnection,
    dmaResponseConnection, targetRequestConnection, targetResponseConnection,
    auditConnection, cpuRequest, cpuResponse, dmaRequest, dmaResponse,
    targetRequest, targetResponse, audit, PackedChan.named,
    Chan.sourceAcceptedName, Chan.sourceReadyName, Chan.sinkValidName,
    Chan.sinkPayloadName, Chan.stem, System.boolValue]

def systemFabricTargetResponsePending (state : system.State) : List Response :=
  if (systemFabricState state).regs targetResponse.bits.sinkPopName 1 = 1#1 then
    [HwPacked.unpack ((systemFabricState state).regs
      targetResponse.bits.sinkPayloadName (HwPacked.width Response))]
  else []

def FabricTargetResponseSinkCoherent (state : system.State) : Prop :=
  (systemFabricState state).regs targetResponse.bits.sinkPopName 1 = 1#1 →
    (system.channelState state targetResponseConnection).head? =
      some ((systemFabricState state).regs
        targetResponse.bits.sinkPayloadName (HwPacked.width Response))

def systemFabricResponsesRoutedAt (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) : List Response :=
  if event.fires "cpu_fabric_clk" = true then
    (fabricRoutedResponseBits? ((systemFabricState state).setInputs fabric.inputs
      (system.islandInput event state external "fabric"))).toList.map HwPacked.unpack
  else []

def systemTargetResponsesDeliveredAt (state : system.State)
    (event : NamedClockEvent) : List Response :=
  (system.connectionResult event state targetResponseConnection).delivered.toList.map
    HwPacked.unpack

@[simp] theorem systemFabricTargetResponsePending_reset :
    systemFabricTargetResponsePending system.reset = [] := by rfl

theorem fabricTargetResponseSinkCoherent_reset :
    FabricTargetResponseSinkCoherent system.reset := by
  intro pending
  have found : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  change (system.reset.island "fabric").regs
    targetResponse.bits.sinkPopName 1 = 1#1 at pending
  simp only [System.reset] at pending
  rw [found] at pending
  simp [fabric, fabricBody, PackedChan.withSink, PackedChan.withSource,
    Chan.withSink, Chan.withSource, Design.reset, targetResponse,
    targetRequest, cpuRequest, dmaRequest, cpuResponse, dmaResponse,
    PackedChan.named, Chan.sinkPopName, Chan.sourceValidName,
    Chan.sourcePayloadName, Chan.stem] at pending

theorem system_advance_fabric_target_response_pop (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (ticks : event.fires "cpu_fabric_clk" = true) :
    ((system.advance event external state).island "fabric").regs
        targetResponse.bits.sinkPopName 1 =
      if (fabricResponseRouteChoice
        ((systemFabricState state).setInputs fabric.inputs
          (system.islandInput event state external "fabric"))).isSome
      then 1#1 else 0#1 := by
  have found : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  rw [System.advance_island_ticked system event external state
    ⟨"fabric", "cpu_fabric_clk", fabric⟩ found ticks]
  exact fabric_cycleOpen_target_response_pop _ _

theorem system_advance_fabric_target_response_payload (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (ticks : event.fires "cpu_fabric_clk" = true) :
    ((system.advance event external state).island "fabric").regs
        targetResponse.bits.sinkPayloadName (HwPacked.width Response) =
      (system.channelState state targetResponseConnection).head?.getD 0 := by
  have found : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  rw [System.advance_island_ticked system event external state
    ⟨"fabric", "cpu_fabric_clk", fabric⟩ found ticks]
  rw [fabric_cycleOpen_target_response_payload]
  exact fabricInput_targetResponsePayload state event external

theorem system_targetResponse_sink_step (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (coherent : FabricTargetResponseSinkCoherent state) :
    FabricTargetResponseSinkCoherent (system.advance event external state) ∧
      systemFabricTargetResponsePending state ++
          systemFabricResponsesRoutedAt state event external =
        systemTargetResponsesDeliveredAt state event ++
          systemFabricTargetResponsePending
            (system.advance event external state) := by
  by_cases ticks : event.fires "cpu_fabric_clk" = true
  · let q := system.channelState state targetResponseConnection
    let payload := (systemFabricState state).regs
      targetResponse.bits.sinkPayloadName (HwPacked.width Response)
    let pop : Bool := (systemFabricState state).regs
      targetResponse.bits.sinkPopName 1 != 0
    let poked := (systemFabricState state).setInputs fabric.inputs
      (system.islandInput event state external "fabric")
    let consume : Bool := (fabricResponseRouteChoice poked).isSome
    let responseEvent := system.connectionEvent event state targetResponseConnection
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have eventPop : responseEvent.pop = pop := by
      simp [responseEvent, pop, System.connectionEvent,
        targetResponseConnection, found, ticks, systemFabricState, Expr.eval]
    have coherentBits : pop = true → q.head? = some payload := by
      intro pending
      have nonzero : (systemFabricState state).regs
          targetResponse.bits.sinkPopName 1 ≠ 0#1 := by simpa [pop] using pending
      have pendingOne : (systemFabricState state).regs
          targetResponse.bits.sinkPopName 1 = 1#1 := by bv_omega
      simpa [FabricClientRequestSinkCoherent, fabricClientRequestChannel,
        systemFabricClientRequestQueue, q, payload] using coherent pendingOne
    have consumeLegal : consume = true → pop = false ∧ q.isEmpty = false := by
      intro consumed
      obtain ⟨route, routeEq⟩ : ∃ route,
          fabricResponseRouteChoice poked = some route := by
        cases choiceEq : fabricResponseRouteChoice poked with
        | none => simp [consume, choiceEq] at consumed
        | some client => exact ⟨client, rfl⟩
      have ready : targetResponse.bits.canDeq.eval poked = 1#1 := by
        unfold fabricResponseRouteChoice at routeEq
        repeat' first
          | split at routeEq <;> rename_i condition
        all_goals simp_all [Expr.eval, bitvec1_and_eq_one]
      have inputValid := fabricInput_targetResponseValid state event external
      have popStable : poked.regs targetResponse.bits.sinkPopName 1 =
          (systemFabricState state).regs targetResponse.bits.sinkPopName 1 := by rfl
      have validPoked : poked.regs targetResponse.bits.sinkValidName 1 =
          system.islandInput event state external "fabric"
            targetResponse.bits.sinkValidName 1 := by rfl
      rw [← validPoked] at inputValid
      change poked.regs targetResponse.bits.sinkValidName 1 =
          (if q.isEmpty then 0#1 else 1#1) at inputValid
      have popZero : poked.regs targetResponse.bits.sinkPopName 1 = 0#1 := by
        by_contra nonzero
        have popOne : poked.regs targetResponse.bits.sinkPopName 1 = 1#1 := by
          bv_omega
        have blocked := targetResponse.bits.canDeq_zero_of_pending poked popOne
        rw [blocked] at ready
        contradiction
      constructor
      · dsimp [pop]
        rw [popStable] at popZero
        simp [popZero]
      · by_contra empty
        have emptyTrue : q.isEmpty = true := Bool.eq_true_of_not_eq_false empty
        rw [emptyTrue] at inputValid
        simp only [if_true] at inputValid
        simp [Chan.canDeq, Expr.eval, inputValid] at ready
    have localStep := targetResponse.bits.sinkStep_conservation q
      responseEvent.push pop payload consume coherentBits consumeLegal
    rw [← eventPop] at localStep
    have nextQueue : system.channelState (system.advance event external state)
        targetResponseConnection =
        (targetResponse.bits.step q responseEvent).state := by
      simpa [q, responseEvent, System.connectionResult, targetResponseConnection]
        using System.channelState_advance system event external state
          targetResponseConnection (by rfl)
    have nextPop := system_advance_fabric_target_response_pop
      state event external ticks
    have nextPayload := system_advance_fabric_target_response_payload
      state event external ticks
    constructor
    · intro pending
      change ((system.advance event external state).island "fabric").regs
        targetResponse.bits.sinkPopName 1 = 1#1 at pending
      change ((system.advance event external state).island "fabric").regs
        targetResponse.bits.sinkPopName 1 =
          if (fabricResponseRouteChoice poked).isSome then 1#1 else 0#1 at nextPop
      have consumed : consume = true := by
        rw [nextPop] at pending
        by_cases h : (fabricResponseRouteChoice poked).isSome = true
        · exact h
        · simp [h] at pending
      have headCoherent := localStep.2 consumed
      rw [nextQueue]
      change ((system.advance event external state).island "fabric").regs
        targetResponse.bits.sinkPayloadName (HwPacked.width Response) = _ at nextPayload
      change _ = some (((system.advance event external state).island
        "fabric").regs targetResponse.bits.sinkPayloadName
          (HwPacked.width Response))
      rw [nextPayload]
      simpa [q, responseEvent, Chan.sinkStep] using headCoherent
    · have inputPayload := fabricInput_targetResponsePayload state event external
      have pokedPayload : poked.regs targetResponse.bits.sinkPayloadName
          (HwPacked.width Response) = q.head?.getD 0 := by
        calc
          _ = system.islandInput event state external "fabric"
              targetResponse.bits.sinkPayloadName (HwPacked.width Response) := rfl
          _ = _ := by simpa [q] using inputPayload
      have prePendingEq :
          (Chan.sinkPending pop payload).map HwPacked.unpack =
            systemFabricTargetResponsePending state := by
        by_cases pending : (systemFabricState state).regs
            targetResponse.bits.sinkPopName 1 = 1#1
        · have popTrue : pop = true := by simp [pop, pending]
          simp [Chan.sinkPending, popTrue, systemFabricTargetResponsePending,
            pending, payload]
        · have popZero : (systemFabricState state).regs
              targetResponse.bits.sinkPopName 1 = 0#1 := by bv_omega
          have popFalse : pop = false := by simp [pop, popZero]
          simp [Chan.sinkPending, popFalse,
            systemFabricTargetResponsePending, pending]
      have routedEq :
          (if consume then [q.head?.getD 0] else []).map HwPacked.unpack =
            systemFabricResponsesRoutedAt state event external := by
        simp only [systemFabricResponsesRoutedAt, ticks, if_true]
        unfold fabricRoutedResponseBits?
        cases route : fabricResponseRouteChoice poked with
        | none => simp [consume, route]
        | some client =>
            simp only [consume, route, Option.isSome_some, if_true,
              Option.map_some, Option.toList_some, List.map_cons,
              List.map_nil]
            change [HwPacked.unpack (q.head?.getD 0)] =
              [HwPacked.unpack (poked.regs targetResponse.bits.sinkPayloadName
                (HwPacked.width Response))]
            rw [pokedPayload]
      have deliveredEq :
          (targetResponse.bits.deliveredValues q
            { push := responseEvent.push, pop := responseEvent.pop }).map
              HwPacked.unpack = systemTargetResponsesDeliveredAt state event := by
        simp only [systemTargetResponsesDeliveredAt, System.connectionResult,
          Chan.deliveredValues]
        rfl
      have nextPendingEq :
          (Chan.sinkPending (Chan.sinkStep q consume).1
              (Chan.sinkStep q consume).2).map HwPacked.unpack =
            systemFabricTargetResponsePending
              (system.advance event external state) := by
        change ((system.advance event external state).island "fabric").regs
          targetResponse.bits.sinkPopName 1 =
            if (fabricResponseRouteChoice poked).isSome then 1#1 else 0#1 at nextPop
        change ((system.advance event external state).island "fabric").regs
          targetResponse.bits.sinkPayloadName (HwPacked.width Response) = _ at nextPayload
        by_cases h : (fabricResponseRouteChoice poked).isSome = true
        · have pendingOne : ((system.advance event external state).island
              "fabric").regs targetResponse.bits.sinkPopName 1 = 1#1 := by
            simpa [h] using nextPop
          simp [Chan.sinkPending, Chan.sinkStep, consume, h,
            systemFabricTargetResponsePending, systemFabricState, pendingOne,
            nextPayload, q]
        · have pendingZero : ((system.advance event external state).island
              "fabric").regs targetResponse.bits.sinkPopName 1 = 0#1 := by
            simpa [h] using nextPop
          simp [Chan.sinkPending, Chan.sinkStep, consume, h,
            systemFabricTargetResponsePending, systemFabricState, pendingZero]
      have prePendingEventEq :
          (Chan.sinkPending responseEvent.pop payload).map HwPacked.unpack =
            systemFabricTargetResponsePending state := by
        rw [eventPop]
        exact prePendingEq
      have ledger := congrArg (List.map HwPacked.unpack) localStep.1
      simp only [List.map_append] at ledger
      change _ = (targetResponse.bits.deliveredValues q responseEvent).map
          HwPacked.unpack ++ _ at ledger
      rw [prePendingEventEq, routedEq, deliveredEq, nextPendingEq] at ledger
      exact ledger
  · have unticked : event.fires "cpu_fabric_clk" = false :=
      Bool.eq_false_of_not_eq_true ticks
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have nextIsland := System.advance_island_unticked system event external state
      ⟨"fabric", "cpu_fabric_clk", fabric⟩ found unticked
    have deliveredNone :
        (system.connectionResult event state targetResponseConnection).delivered = none := by
      simp [System.connectionResult, System.connectionEvent,
        targetResponseConnection, found, unticked, targetResponse,
        PackedChan.named, Chan.step]
    constructor
    · intro pending
      change ((system.advance event external state).island "fabric").regs
        targetResponse.bits.sinkPopName 1 = 1#1 at pending
      rw [nextIsland] at pending
      have oldHead := coherent pending
      have eventPop : (system.connectionEvent event state
          targetResponseConnection).pop = false := by
        simp [System.connectionEvent, targetResponseConnection, found, unticked]
      have stableHead := targetResponse.bits.step_head_of_no_pop
        (system.channelState state targetResponseConnection)
        (system.connectionEvent event state targetResponseConnection).push
        ((systemFabricState state).regs targetResponse.bits.sinkPayloadName
          (HwPacked.width Response)) oldHead
      have nextQueue := System.channelState_advance system event external state
        targetResponseConnection (by rfl)
      rw [nextQueue]
      change (system.connectionResult event state
          targetResponseConnection).state.head? = _
      rw [show system.connectionResult event state targetResponseConnection =
          targetResponse.bits.step (system.channelState state targetResponseConnection)
            (system.connectionEvent event state targetResponseConnection) by rfl]
      have responseEventEq : system.connectionEvent event state
          targetResponseConnection =
          { push := (system.connectionEvent event state
              targetResponseConnection).push, pop := false } := by
        cases h : system.connectionEvent event state targetResponseConnection with
        | mk push pop =>
            simp only at eventPop
            simp [h] at eventPop ⊢
            exact eventPop
      rw [responseEventEq]
      change _ = some (((system.advance event external state).island
        "fabric").regs targetResponse.bits.sinkPayloadName
          (HwPacked.width Response))
      rw [nextIsland]
      simpa [systemFabricState] using stableHead
    · simp [systemFabricResponsesRoutedAt, ticks,
        systemTargetResponsesDeliveredAt, deliveredNone,
        systemFabricTargetResponsePending, systemFabricState, nextIsland]

theorem system_cpuRequest_sink_step (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (coherent : FabricClientRequestSinkCoherent .cpu state) :
    FabricClientRequestSinkCoherent .cpu (system.advance event external state) ∧
      systemFabricClientRequestPending .cpu state ++
          systemFabricClientRequestsGrantedAt .cpu state event external =
        systemClientRequestsDeliveredAt .cpu state event ++
          systemFabricClientRequestPending .cpu
            (system.advance event external state) := by
  by_cases ticks : event.fires "cpu_fabric_clk" = true
  · let q := system.channelState state cpuRequestConnection
    let payload := (systemFabricState state).regs
      cpuRequest.bits.sinkPayloadName (HwPacked.width Request)
    let pop : Bool := (systemFabricState state).regs
      cpuRequest.bits.sinkPopName 1 != 0
    let poked := (systemFabricState state).setInputs fabric.inputs
      (system.islandInput event state external "fabric")
    let consume : Bool := fabricGrantChoice poked == some .cpu
    let requestEvent := system.connectionEvent event state cpuRequestConnection
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have eventPop : requestEvent.pop = pop := by
      simp [requestEvent, pop, System.connectionEvent,
        cpuRequestConnection, found, ticks, systemFabricState, Expr.eval]
    have coherentBits : pop = true → q.head? = some payload := by
      intro pending
      have nonzero : (systemFabricState state).regs
          cpuRequest.bits.sinkPopName 1 ≠ 0#1 := by simpa [pop] using pending
      have pendingOne : (systemFabricState state).regs
          cpuRequest.bits.sinkPopName 1 = 1#1 := by bv_omega
      simpa [q, payload] using coherent pendingOne
    have consumeLegal : consume = true → pop = false ∧ q.isEmpty = false := by
      intro consumed
      have choiceEq : fabricGrantChoice poked = some .cpu := by
        simpa [consume] using consumed
      have ready : cpuRequest.bits.canDeq.eval poked = 1#1 :=
        fabricGrantChoice_cpu_canDeq poked choiceEq
      have inputValid : system.islandInput event state external "fabric"
          cpuRequest.bits.sinkValidName 1 =
            if q.isEmpty then 0#1 else 1#1 := by
        simpa [fabricClientRequestChannel, systemFabricClientRequestQueue, q]
          using fabricInput_clientRequestValid .cpu state event external
      have popStable : poked.regs cpuRequest.bits.sinkPopName 1 =
          (systemFabricState state).regs cpuRequest.bits.sinkPopName 1 := by rfl
      have validPoked : poked.regs cpuRequest.bits.sinkValidName 1 =
          system.islandInput event state external "fabric"
            cpuRequest.bits.sinkValidName 1 := by rfl
      rw [← validPoked] at inputValid
      have popZero : poked.regs cpuRequest.bits.sinkPopName 1 = 0#1 := by
        by_contra nonzero
        have popOne : poked.regs cpuRequest.bits.sinkPopName 1 = 1#1 := by
          bv_omega
        have blocked := cpuRequest.bits.canDeq_zero_of_pending poked popOne
        rw [blocked] at ready
        contradiction
      constructor
      · dsimp [pop]
        rw [popStable] at popZero
        simp [popZero]
      · by_contra empty
        have emptyTrue : q.isEmpty = true := Bool.eq_true_of_not_eq_false empty
        rw [emptyTrue] at inputValid
        simp only [if_true] at inputValid
        simp [Chan.canDeq, Expr.eval, inputValid] at ready
    have localStep := cpuRequest.bits.sinkStep_conservation q
      requestEvent.push pop payload consume coherentBits consumeLegal
    rw [← eventPop] at localStep
    have nextQueue : system.channelState (system.advance event external state)
        cpuRequestConnection =
        (cpuRequest.bits.step q requestEvent).state := by
      simpa [q, requestEvent, System.connectionResult, cpuRequestConnection]
        using System.channelState_advance system event external state
          cpuRequestConnection (by rfl)
    have nextPop := system_advance_fabric_client_request_pop .cpu
      state event external ticks
    have nextPayload := system_advance_fabric_client_request_payload .cpu
      state event external ticks
    constructor
    · intro pending
      change ((system.advance event external state).island "fabric").regs
        cpuRequest.bits.sinkPopName 1 = 1#1 at pending
      change ((system.advance event external state).island "fabric").regs
        cpuRequest.bits.sinkPopName 1 =
          if fabricGrantChoice poked = some .cpu then 1#1 else 0#1 at nextPop
      have consumed : consume = true := by
        rw [nextPop] at pending
        by_cases h : fabricGrantChoice poked = some .cpu
        · simp [consume, h]
        · simp [h] at pending
      have headCoherent := localStep.2 consumed
      change (system.channelState (system.advance event external state)
        cpuRequestConnection).head? = _
      rw [nextQueue]
      change ((system.advance event external state).island "fabric").regs
        cpuRequest.bits.sinkPayloadName (HwPacked.width Request) = _ at nextPayload
      change _ = some (((system.advance event external state).island
        "fabric").regs cpuRequest.bits.sinkPayloadName
          (HwPacked.width Request))
      rw [nextPayload]
      simpa [q, requestEvent, Chan.sinkStep] using headCoherent
    · have inputPayload : system.islandInput event state external "fabric"
          cpuRequest.bits.sinkPayloadName (HwPacked.width Request) =
            q.head?.getD 0 := by
        simpa [fabricClientRequestChannel, systemFabricClientRequestQueue, q]
          using fabricInput_clientRequestPayload .cpu state event external
      have pokedPayload : poked.regs cpuRequest.bits.sinkPayloadName
          (HwPacked.width Request) = q.head?.getD 0 := by
        calc
          _ = system.islandInput event state external "fabric"
              cpuRequest.bits.sinkPayloadName (HwPacked.width Request) := rfl
          _ = _ := by simpa [q] using inputPayload
      have prePendingEq :
          (Chan.sinkPending pop payload).map HwPacked.unpack =
            systemFabricClientRequestPending .cpu state := by
        by_cases pending : (systemFabricState state).regs
            cpuRequest.bits.sinkPopName 1 = 1#1
        · have popTrue : pop = true := by simp [pop, pending]
          simp [Chan.sinkPending, popTrue, systemFabricClientRequestPending,
            fabricClientRequestChannel, pending, payload]
        · have popZero : (systemFabricState state).regs
              cpuRequest.bits.sinkPopName 1 = 0#1 := by bv_omega
          have popFalse : pop = false := by simp [pop, popZero]
          simp [Chan.sinkPending, popFalse,
            systemFabricClientRequestPending, fabricClientRequestChannel, pending]
      have routedEq :
          (if consume then [q.head?.getD 0] else []).map HwPacked.unpack =
            systemFabricClientRequestsGrantedAt .cpu state event external := by
        simp only [systemFabricClientRequestsGrantedAt, ticks, if_true]
        change (if consume then [q.head?.getD 0] else []).map HwPacked.unpack =
          if fabricGrantChoice poked = some .cpu then
            [cpuRequest.deq.eval poked] else []
        by_cases grant : fabricGrantChoice poked = some .cpu
        · rw [if_pos grant]
          simp only [consume, grant, beq_self_eq_true, Bool.true_eq,
            List.map_cons, List.map_nil]
          change [HwPacked.unpack (q.head?.getD 0)] =
            [HwPacked.unpack (poked.regs cpuRequest.bits.sinkPayloadName
              (HwPacked.width Request))]
          rw [pokedPayload]
        · simp [consume, grant]
      have deliveredEq :
          (cpuRequest.bits.deliveredValues q
            { push := requestEvent.push, pop := requestEvent.pop }).map
              HwPacked.unpack = systemClientRequestsDeliveredAt .cpu state event := by
        simp only [systemClientRequestsDeliveredAt, System.connectionResult,
          Chan.deliveredValues]
        rfl
      have nextPendingEq :
          (Chan.sinkPending (Chan.sinkStep q consume).1
              (Chan.sinkStep q consume).2).map HwPacked.unpack =
            systemFabricClientRequestPending .cpu
              (system.advance event external state) := by
        change ((system.advance event external state).island "fabric").regs
          cpuRequest.bits.sinkPopName 1 =
            if fabricGrantChoice poked = some .cpu then 1#1 else 0#1 at nextPop
        change ((system.advance event external state).island "fabric").regs
          cpuRequest.bits.sinkPayloadName (HwPacked.width Request) = _ at nextPayload
        by_cases h : fabricGrantChoice poked = some .cpu
        · have pendingOne : ((system.advance event external state).island
              "fabric").regs cpuRequest.bits.sinkPopName 1 = 1#1 := by
            simpa [h] using nextPop
          simp only [Chan.sinkStep, consume, h, beq_self_eq_true,
            Chan.sinkPending, if_true, List.map_cons, List.map_nil]
          unfold systemFabricClientRequestPending
          dsimp [fabricClientRequestChannel]
          unfold systemFabricState
          rw [if_pos pendingOne, nextPayload]
          rfl
        · have pendingZero : ((system.advance event external state).island
              "fabric").regs cpuRequest.bits.sinkPopName 1 = 0#1 := by
            simpa [h] using nextPop
          unfold systemFabricClientRequestPending
          dsimp [fabricClientRequestChannel]
          unfold systemFabricState
          rw [if_neg (by bv_omega : ((system.advance event external state).island
            "fabric").regs cpuRequest.bits.sinkPopName 1 ≠ 1#1)]
          simp [Chan.sinkStep, Chan.sinkPending, consume, h]
      have prePendingEventEq :
          (Chan.sinkPending requestEvent.pop payload).map HwPacked.unpack =
            systemFabricClientRequestPending .cpu state := by
        rw [eventPop]
        exact prePendingEq
      have ledger := congrArg (List.map HwPacked.unpack) localStep.1
      simp only [List.map_append] at ledger
      change _ = (cpuRequest.bits.deliveredValues q requestEvent).map
          HwPacked.unpack ++ _ at ledger
      rw [prePendingEventEq, routedEq, deliveredEq, nextPendingEq] at ledger
      exact ledger
  · have unticked : event.fires "cpu_fabric_clk" = false :=
      Bool.eq_false_of_not_eq_true ticks
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have nextIsland := System.advance_island_unticked system event external state
      ⟨"fabric", "cpu_fabric_clk", fabric⟩ found unticked
    have deliveredNone :
        (system.connectionResult event state cpuRequestConnection).delivered = none := by
      simp [System.connectionResult, System.connectionEvent,
        cpuRequestConnection, found, unticked, cpuRequest,
        PackedChan.named, Chan.step]
    constructor
    · intro pending
      change ((system.advance event external state).island "fabric").regs
        cpuRequest.bits.sinkPopName 1 = 1#1 at pending
      rw [nextIsland] at pending
      have oldHead : (system.channelState state cpuRequestConnection).head? =
          some ((systemFabricState state).regs
            cpuRequest.bits.sinkPayloadName (HwPacked.width Request)) := by
        simpa [FabricClientRequestSinkCoherent, fabricClientRequestChannel,
          systemFabricClientRequestQueue] using coherent pending
      have eventPop : (system.connectionEvent event state
          cpuRequestConnection).pop = false := by
        simp [System.connectionEvent, cpuRequestConnection, found, unticked]
      have stableHead := cpuRequest.bits.step_head_of_no_pop
        (system.channelState state cpuRequestConnection)
        (system.connectionEvent event state cpuRequestConnection).push
        ((systemFabricState state).regs cpuRequest.bits.sinkPayloadName
          (HwPacked.width Request)) oldHead
      have nextQueue := System.channelState_advance system event external state
        cpuRequestConnection (by rfl)
      change (system.channelState (system.advance event external state)
        cpuRequestConnection).head? = _
      rw [nextQueue]
      change (system.connectionResult event state
          cpuRequestConnection).state.head? = _
      rw [show system.connectionResult event state cpuRequestConnection =
          cpuRequest.bits.step (system.channelState state cpuRequestConnection)
            (system.connectionEvent event state cpuRequestConnection) by rfl]
      have requestEventEq : system.connectionEvent event state
          cpuRequestConnection =
          { push := (system.connectionEvent event state
              cpuRequestConnection).push, pop := false } := by
        cases h : system.connectionEvent event state cpuRequestConnection with
        | mk push pop =>
            simp only at eventPop
            simp [h] at eventPop ⊢
            exact eventPop
      rw [requestEventEq]
      change _ = some (((system.advance event external state).island
        "fabric").regs cpuRequest.bits.sinkPayloadName
          (HwPacked.width Request))
      rw [nextIsland]
      simpa [systemFabricState] using stableHead
    · simp [systemFabricClientRequestsGrantedAt, ticks,
        systemClientRequestsDeliveredAt, deliveredNone,
        systemFabricClientRequestPending, fabricClientRequestChannel,
        systemFabricState, nextIsland]


theorem system_dmaRequest_sink_step (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (coherent : FabricClientRequestSinkCoherent .dma state) :
    FabricClientRequestSinkCoherent .dma (system.advance event external state) ∧
      systemFabricClientRequestPending .dma state ++
          systemFabricClientRequestsGrantedAt .dma state event external =
        systemClientRequestsDeliveredAt .dma state event ++
          systemFabricClientRequestPending .dma
            (system.advance event external state) := by
  by_cases ticks : event.fires "cpu_fabric_clk" = true
  · let q := system.channelState state dmaRequestConnection
    let payload := (systemFabricState state).regs
      dmaRequest.bits.sinkPayloadName (HwPacked.width Request)
    let pop : Bool := (systemFabricState state).regs
      dmaRequest.bits.sinkPopName 1 != 0
    let poked := (systemFabricState state).setInputs fabric.inputs
      (system.islandInput event state external "fabric")
    let consume : Bool := fabricGrantChoice poked == some .dma
    let requestEvent := system.connectionEvent event state dmaRequestConnection
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have eventPop : requestEvent.pop = pop := by
      simp [requestEvent, pop, System.connectionEvent,
        dmaRequestConnection, found, ticks, systemFabricState, Expr.eval]
    have coherentBits : pop = true → q.head? = some payload := by
      intro pending
      have nonzero : (systemFabricState state).regs
          dmaRequest.bits.sinkPopName 1 ≠ 0#1 := by simpa [pop] using pending
      have pendingOne : (systemFabricState state).regs
          dmaRequest.bits.sinkPopName 1 = 1#1 := by bv_omega
      simpa [q, payload] using coherent pendingOne
    have consumeLegal : consume = true → pop = false ∧ q.isEmpty = false := by
      intro consumed
      have choiceEq : fabricGrantChoice poked = some .dma := by
        simpa [consume] using consumed
      have ready : dmaRequest.bits.canDeq.eval poked = 1#1 :=
        fabricGrantChoice_dma_canDeq poked choiceEq
      have inputValid : system.islandInput event state external "fabric"
          dmaRequest.bits.sinkValidName 1 =
            if q.isEmpty then 0#1 else 1#1 := by
        simpa [fabricClientRequestChannel, systemFabricClientRequestQueue, q]
          using fabricInput_clientRequestValid .dma state event external
      have popStable : poked.regs dmaRequest.bits.sinkPopName 1 =
          (systemFabricState state).regs dmaRequest.bits.sinkPopName 1 := by rfl
      have validPoked : poked.regs dmaRequest.bits.sinkValidName 1 =
          system.islandInput event state external "fabric"
            dmaRequest.bits.sinkValidName 1 := by rfl
      rw [← validPoked] at inputValid
      have popZero : poked.regs dmaRequest.bits.sinkPopName 1 = 0#1 := by
        by_contra nonzero
        have popOne : poked.regs dmaRequest.bits.sinkPopName 1 = 1#1 := by
          bv_omega
        have blocked := dmaRequest.bits.canDeq_zero_of_pending poked popOne
        rw [blocked] at ready
        contradiction
      constructor
      · dsimp [pop]
        rw [popStable] at popZero
        simp [popZero]
      · by_contra empty
        have emptyTrue : q.isEmpty = true := Bool.eq_true_of_not_eq_false empty
        rw [emptyTrue] at inputValid
        simp only [if_true] at inputValid
        simp [Chan.canDeq, Expr.eval, inputValid] at ready
    have localStep := dmaRequest.bits.sinkStep_conservation q
      requestEvent.push pop payload consume coherentBits consumeLegal
    rw [← eventPop] at localStep
    have nextQueue : system.channelState (system.advance event external state)
        dmaRequestConnection =
        (dmaRequest.bits.step q requestEvent).state := by
      simpa [q, requestEvent, System.connectionResult, dmaRequestConnection]
        using System.channelState_advance system event external state
          dmaRequestConnection (by rfl)
    have nextPop := system_advance_fabric_client_request_pop .dma
      state event external ticks
    have nextPayload := system_advance_fabric_client_request_payload .dma
      state event external ticks
    constructor
    · intro pending
      change ((system.advance event external state).island "fabric").regs
        dmaRequest.bits.sinkPopName 1 = 1#1 at pending
      change ((system.advance event external state).island "fabric").regs
        dmaRequest.bits.sinkPopName 1 =
          if fabricGrantChoice poked = some .dma then 1#1 else 0#1 at nextPop
      have consumed : consume = true := by
        rw [nextPop] at pending
        by_cases h : fabricGrantChoice poked = some .dma
        · simp [consume, h]
        · simp [h] at pending
      have headCoherent := localStep.2 consumed
      change (system.channelState (system.advance event external state)
        dmaRequestConnection).head? = _
      rw [nextQueue]
      change ((system.advance event external state).island "fabric").regs
        dmaRequest.bits.sinkPayloadName (HwPacked.width Request) = _ at nextPayload
      change _ = some (((system.advance event external state).island
        "fabric").regs dmaRequest.bits.sinkPayloadName
          (HwPacked.width Request))
      rw [nextPayload]
      simpa [q, requestEvent, Chan.sinkStep] using headCoherent
    · have inputPayload : system.islandInput event state external "fabric"
          dmaRequest.bits.sinkPayloadName (HwPacked.width Request) =
            q.head?.getD 0 := by
        simpa [fabricClientRequestChannel, systemFabricClientRequestQueue, q]
          using fabricInput_clientRequestPayload .dma state event external
      have pokedPayload : poked.regs dmaRequest.bits.sinkPayloadName
          (HwPacked.width Request) = q.head?.getD 0 := by
        calc
          _ = system.islandInput event state external "fabric"
              dmaRequest.bits.sinkPayloadName (HwPacked.width Request) := rfl
          _ = _ := by simpa [q] using inputPayload
      have prePendingEq :
          (Chan.sinkPending pop payload).map HwPacked.unpack =
            systemFabricClientRequestPending .dma state := by
        by_cases pending : (systemFabricState state).regs
            dmaRequest.bits.sinkPopName 1 = 1#1
        · have popTrue : pop = true := by simp [pop, pending]
          simp [Chan.sinkPending, popTrue, systemFabricClientRequestPending,
            fabricClientRequestChannel, pending, payload]
        · have popZero : (systemFabricState state).regs
              dmaRequest.bits.sinkPopName 1 = 0#1 := by bv_omega
          have popFalse : pop = false := by simp [pop, popZero]
          simp [Chan.sinkPending, popFalse,
            systemFabricClientRequestPending, fabricClientRequestChannel, pending]
      have routedEq :
          (if consume then [q.head?.getD 0] else []).map HwPacked.unpack =
            systemFabricClientRequestsGrantedAt .dma state event external := by
        simp only [systemFabricClientRequestsGrantedAt, ticks, if_true]
        change (if consume then [q.head?.getD 0] else []).map HwPacked.unpack =
          if fabricGrantChoice poked = some .dma then
            [dmaRequest.deq.eval poked] else []
        by_cases grant : fabricGrantChoice poked = some .dma
        · rw [if_pos grant]
          simp only [consume, grant, beq_self_eq_true, Bool.true_eq,
            List.map_cons, List.map_nil]
          change [HwPacked.unpack (q.head?.getD 0)] =
            [HwPacked.unpack (poked.regs dmaRequest.bits.sinkPayloadName
              (HwPacked.width Request))]
          rw [pokedPayload]
        · simp [consume, grant]
      have deliveredEq :
          (dmaRequest.bits.deliveredValues q
            { push := requestEvent.push, pop := requestEvent.pop }).map
              HwPacked.unpack = systemClientRequestsDeliveredAt .dma state event := by
        simp only [systemClientRequestsDeliveredAt, System.connectionResult,
          Chan.deliveredValues]
        rfl
      have nextPendingEq :
          (Chan.sinkPending (Chan.sinkStep q consume).1
              (Chan.sinkStep q consume).2).map HwPacked.unpack =
            systemFabricClientRequestPending .dma
              (system.advance event external state) := by
        change ((system.advance event external state).island "fabric").regs
          dmaRequest.bits.sinkPopName 1 =
            if fabricGrantChoice poked = some .dma then 1#1 else 0#1 at nextPop
        change ((system.advance event external state).island "fabric").regs
          dmaRequest.bits.sinkPayloadName (HwPacked.width Request) = _ at nextPayload
        by_cases h : fabricGrantChoice poked = some .dma
        · have pendingOne : ((system.advance event external state).island
              "fabric").regs dmaRequest.bits.sinkPopName 1 = 1#1 := by
            simpa [h] using nextPop
          simp only [Chan.sinkStep, consume, h, beq_self_eq_true,
            Chan.sinkPending, if_true, List.map_cons, List.map_nil]
          unfold systemFabricClientRequestPending
          dsimp [fabricClientRequestChannel]
          unfold systemFabricState
          rw [if_pos pendingOne, nextPayload]
          rfl
        · have pendingZero : ((system.advance event external state).island
              "fabric").regs dmaRequest.bits.sinkPopName 1 = 0#1 := by
            simpa [h] using nextPop
          unfold systemFabricClientRequestPending
          dsimp [fabricClientRequestChannel]
          unfold systemFabricState
          rw [if_neg (by bv_omega : ((system.advance event external state).island
            "fabric").regs dmaRequest.bits.sinkPopName 1 ≠ 1#1)]
          simp [Chan.sinkStep, Chan.sinkPending, consume, h]
      have prePendingEventEq :
          (Chan.sinkPending requestEvent.pop payload).map HwPacked.unpack =
            systemFabricClientRequestPending .dma state := by
        rw [eventPop]
        exact prePendingEq
      have ledger := congrArg (List.map HwPacked.unpack) localStep.1
      simp only [List.map_append] at ledger
      change _ = (dmaRequest.bits.deliveredValues q requestEvent).map
          HwPacked.unpack ++ _ at ledger
      rw [prePendingEventEq, routedEq, deliveredEq, nextPendingEq] at ledger
      exact ledger
  · have unticked : event.fires "cpu_fabric_clk" = false :=
      Bool.eq_false_of_not_eq_true ticks
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have nextIsland := System.advance_island_unticked system event external state
      ⟨"fabric", "cpu_fabric_clk", fabric⟩ found unticked
    have deliveredNone :
        (system.connectionResult event state dmaRequestConnection).delivered = none := by
      simp [System.connectionResult, System.connectionEvent,
        dmaRequestConnection, found, unticked, dmaRequest,
        PackedChan.named, Chan.step]
    constructor
    · intro pending
      change ((system.advance event external state).island "fabric").regs
        dmaRequest.bits.sinkPopName 1 = 1#1 at pending
      rw [nextIsland] at pending
      have oldHead : (system.channelState state dmaRequestConnection).head? =
          some ((systemFabricState state).regs
            dmaRequest.bits.sinkPayloadName (HwPacked.width Request)) := by
        simpa [FabricClientRequestSinkCoherent, fabricClientRequestChannel,
          systemFabricClientRequestQueue] using coherent pending
      have eventPop : (system.connectionEvent event state
          dmaRequestConnection).pop = false := by
        simp [System.connectionEvent, dmaRequestConnection, found, unticked]
      have stableHead := dmaRequest.bits.step_head_of_no_pop
        (system.channelState state dmaRequestConnection)
        (system.connectionEvent event state dmaRequestConnection).push
        ((systemFabricState state).regs dmaRequest.bits.sinkPayloadName
          (HwPacked.width Request)) oldHead
      have nextQueue := System.channelState_advance system event external state
        dmaRequestConnection (by rfl)
      change (system.channelState (system.advance event external state)
        dmaRequestConnection).head? = _
      rw [nextQueue]
      change (system.connectionResult event state
          dmaRequestConnection).state.head? = _
      rw [show system.connectionResult event state dmaRequestConnection =
          dmaRequest.bits.step (system.channelState state dmaRequestConnection)
            (system.connectionEvent event state dmaRequestConnection) by rfl]
      have requestEventEq : system.connectionEvent event state
          dmaRequestConnection =
          { push := (system.connectionEvent event state
              dmaRequestConnection).push, pop := false } := by
        cases h : system.connectionEvent event state dmaRequestConnection with
        | mk push pop =>
            simp only at eventPop
            simp [h] at eventPop ⊢
            exact eventPop
      rw [requestEventEq]
      change _ = some (((system.advance event external state).island
        "fabric").regs dmaRequest.bits.sinkPayloadName
          (HwPacked.width Request))
      rw [nextIsland]
      simpa [systemFabricState] using stableHead
    · simp [systemFabricClientRequestsGrantedAt, ticks,
        systemClientRequestsDeliveredAt, deliveredNone,
        systemFabricClientRequestPending, fabricClientRequestChannel,
        systemFabricState, nextIsland]



def systemFabricClientRequestGrantTraceFrom (client : FabricClient)
    (inputs : ExternalInputs) : system.State → List NamedClockEvent → List Request
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemFabricClientRequestsGrantedAt client state event external ++
        systemFabricClientRequestGrantTraceFrom client inputs
          (system.advance event external state) rest

def systemClientRequestDeliveredTraceFrom (client : FabricClient)
    (inputs : ExternalInputs) : system.State → List NamedClockEvent → List Request
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemClientRequestsDeliveredAt client state event ++
        systemClientRequestDeliveredTraceFrom client inputs
          (system.advance event external state) rest

theorem system_clientRequest_sink_invariant (client : FabricClient)
    (inputs : ExternalInputs) (state : system.State)
    (events : List NamedClockEvent)
    (coherent : FabricClientRequestSinkCoherent client state) :
    FabricClientRequestSinkCoherent client
        (system.runEventsFrom inputs state events) ∧
      systemFabricClientRequestPending client state ++
          systemFabricClientRequestGrantTraceFrom client inputs state events =
        systemClientRequestDeliveredTraceFrom client inputs state events ++
          systemFabricClientRequestPending client
            (system.runEventsFrom inputs state events) := by
  induction events generalizing state with
  | nil =>
      simp [System.runEventsFrom, systemFabricClientRequestGrantTraceFrom,
        systemClientRequestDeliveredTraceFrom, coherent]
  | cons event rest ih =>
      let external := inputs state.time
      let next := system.advance event external state
      have step :
          FabricClientRequestSinkCoherent client next ∧
            systemFabricClientRequestPending client state ++
                systemFabricClientRequestsGrantedAt client state event external =
              systemClientRequestsDeliveredAt client state event ++
                systemFabricClientRequestPending client next := by
        cases client
        · exact system_cpuRequest_sink_step state event external coherent
        · exact system_dmaRequest_sink_step state event external coherent
      have later := ih next step.1
      constructor
      · simpa [System.runEventsFrom, next, external] using later.1
      · simp only [systemFabricClientRequestGrantTraceFrom,
          systemClientRequestDeliveredTraceFrom, System.runEventsFrom]
        change systemFabricClientRequestPending client state ++
            (systemFabricClientRequestsGrantedAt client state event external ++
              systemFabricClientRequestGrantTraceFrom client inputs next rest) =
          (systemClientRequestsDeliveredAt client state event ++
            systemClientRequestDeliveredTraceFrom client inputs next rest) ++
              systemFabricClientRequestPending client
                (system.runEventsFrom inputs next rest)
        calc
          _ = (systemFabricClientRequestPending client state ++
                systemFabricClientRequestsGrantedAt client state event external) ++
                systemFabricClientRequestGrantTraceFrom client inputs next rest := by
              rw [List.append_assoc]
          _ = (systemClientRequestsDeliveredAt client state event ++
                systemFabricClientRequestPending client next) ++
                systemFabricClientRequestGrantTraceFrom client inputs next rest := by
              rw [step.2]
          _ = systemClientRequestsDeliveredAt client state event ++
                (systemFabricClientRequestPending client next ++
                  systemFabricClientRequestGrantTraceFrom client inputs next rest) := by
              rw [List.append_assoc]
          _ = _ := by rw [later.2, ← List.append_assoc]

theorem reset_fabric_client_request_sink_ledger (client : FabricClient)
    (events : List NamedClockEvent) :
    systemFabricClientRequestGrantTraceFrom client noInputs system.reset events =
      systemClientRequestDeliveredTraceFrom client noInputs system.reset events ++
        systemFabricClientRequestPending client
          (system.runEventsFrom noInputs system.reset events) := by
  have invariant := system_clientRequest_sink_invariant client noInputs
    system.reset events (fabricClientRequestSinkCoherent_reset client)
  simpa using invariant.2

theorem systemClientRequestDeliveredTrace_eq_fifo (client : FabricClient)
    (inputs : ExternalInputs) (state : system.State)
    (events : List NamedClockEvent) :
    systemClientRequestDeliveredTraceFrom client inputs state events =
      match client with
      | .cpu => (cpuRequest.bits.runTrace
          (system.channelState state cpuRequestConnection)
          (system.channelEventsFrom inputs cpuRequestConnection state events)).delivered.map
            HwPacked.unpack
      | .dma => (dmaRequest.bits.runTrace
          (system.channelState state dmaRequestConnection)
          (system.channelEventsFrom inputs dmaRequestConnection state events)).delivered.map
            HwPacked.unpack := by
  cases client
  · induction events generalizing state with
    | nil => rfl
    | cons event rest ih =>
        simp only [systemClientRequestDeliveredTraceFrom,
          systemClientRequestsDeliveredAt, System.channelEventsFrom,
          Chan.runTrace, List.map_append]
        let external := inputs state.time
        let next := system.advance event external state
        rw [ih next]
        rw [System.channelState_advance system event external state
          cpuRequestConnection (by rfl)]
        rfl
  · induction events generalizing state with
    | nil => rfl
    | cons event rest ih =>
        simp only [systemClientRequestDeliveredTraceFrom,
          systemClientRequestsDeliveredAt, System.channelEventsFrom,
          Chan.runTrace, List.map_append]
        let external := inputs state.time
        let next := system.advance event external state
        rw [ih next]
        rw [System.channelState_advance system event external state
          dmaRequestConnection (by rfl)]
        rfl

def systemFabricRoutedResponseTraceFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List Response
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemFabricResponsesRoutedAt state event external ++
        systemFabricRoutedResponseTraceFrom inputs
          (system.advance event external state) rest

def systemTargetResponseDeliveredTraceFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List Response
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemTargetResponsesDeliveredAt state event ++
        systemTargetResponseDeliveredTraceFrom inputs
          (system.advance event external state) rest

theorem systemTargetResponseDeliveredTrace_eq_fifo (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemTargetResponseDeliveredTraceFrom inputs state events =
      (targetResponse.bits.runTrace
        (system.channelState state targetResponseConnection)
        (system.channelEventsFrom inputs targetResponseConnection state events)).delivered.map
          HwPacked.unpack := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemTargetResponseDeliveredTraceFrom,
        System.channelEventsFrom, Chan.runTrace, List.map_append]
      let external := inputs state.time
      let next := system.advance event external state
      change systemTargetResponsesDeliveredAt state event ++
          systemTargetResponseDeliveredTraceFrom inputs next rest = _
      rw [ih next]
      rw [System.channelState_advance system event external state
        targetResponseConnection (by rfl)]
      rfl

/-- Arbitrary-schedule preservation of the target-response sink head together
with its exact finite-prefix routing ledger. -/
theorem system_targetResponse_sink_invariant (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent)
    (coherent : FabricTargetResponseSinkCoherent state) :
    FabricTargetResponseSinkCoherent
        (system.runEventsFrom inputs state events) ∧
      systemFabricTargetResponsePending state ++
          systemFabricRoutedResponseTraceFrom inputs state events =
        systemTargetResponseDeliveredTraceFrom inputs state events ++
          systemFabricTargetResponsePending
            (system.runEventsFrom inputs state events) := by
  induction events generalizing state with
  | nil =>
      simp [System.runEventsFrom, systemFabricRoutedResponseTraceFrom,
        systemTargetResponseDeliveredTraceFrom, coherent]
  | cons event rest ih =>
      let external := inputs state.time
      let next := system.advance event external state
      have step := system_targetResponse_sink_step state event external coherent
      have later := ih next step.1
      constructor
      · simpa [System.runEventsFrom, next, external] using later.1
      · simp only [systemFabricRoutedResponseTraceFrom,
          systemTargetResponseDeliveredTraceFrom, System.runEventsFrom]
        change systemFabricTargetResponsePending state ++
            (systemFabricResponsesRoutedAt state event external ++
              systemFabricRoutedResponseTraceFrom inputs next rest) =
          (systemTargetResponsesDeliveredAt state event ++
            systemTargetResponseDeliveredTraceFrom inputs next rest) ++
              systemFabricTargetResponsePending
                (system.runEventsFrom inputs next rest)
        calc
          _ = (systemFabricTargetResponsePending state ++
                systemFabricResponsesRoutedAt state event external) ++
                systemFabricRoutedResponseTraceFrom inputs next rest := by
              rw [List.append_assoc]
          _ = (systemTargetResponsesDeliveredAt state event ++
                systemFabricTargetResponsePending next) ++
                systemFabricRoutedResponseTraceFrom inputs next rest := by
              rw [step.2]
          _ = systemTargetResponsesDeliveredAt state event ++
                (systemFabricTargetResponsePending next ++
                  systemFabricRoutedResponseTraceFrom inputs next rest) := by
              rw [List.append_assoc]
          _ = _ := by rw [later.2, ← List.append_assoc]

theorem reset_fabric_target_response_sink_ledger
    (events : List NamedClockEvent) :
    systemFabricRoutedResponseTraceFrom noInputs system.reset events =
      systemTargetResponseDeliveredTraceFrom noInputs system.reset events ++
        systemFabricTargetResponsePending
          (system.runEventsFrom noInputs system.reset events) := by
  have invariant := system_targetResponse_sink_invariant noInputs system.reset events
    fabricTargetResponseSinkCoherent_reset
  simpa using invariant.2

theorem reset_fabric_routed_responses_eq_delivered_of_drained
    (events : List NamedClockEvent)
    (drained : systemFabricTargetResponsePending
      (system.runEventsFrom noInputs system.reset events) = []) :
    systemFabricRoutedResponseTraceFrom noInputs system.reset events =
      systemTargetResponseDeliveredTraceFrom noInputs system.reset events := by
  rw [reset_fabric_target_response_sink_ledger events, drained, List.append_nil]

/-- A request committed by the service but still represented by its registered
sink pop.  It remains at the FIFO head until the next `mem_clk` event. -/
def systemServiceRequestPending (state : system.State) : List Request :=
  if (systemServiceState state).regs targetRequest.bits.sinkPopName 1 = 1#1 then
    [HwPacked.unpack ((systemServiceState state).regs
      targetRequest.bits.sinkPayloadName (HwPacked.width Request))]
  else []

def systemTargetRequestsDeliveredAt (state : system.State)
    (event : NamedClockEvent) : List Request :=
  (system.connectionResult event state targetRequestConnection).delivered.toList.map
    HwPacked.unpack

/-- The outstanding registered service pop names the literal head retained by
the target-request FIFO. -/
def ServiceRequestSinkCoherent (state : system.State) : Prop :=
  (systemServiceState state).regs targetRequest.bits.sinkPopName 1 = 1#1 →
    (system.channelState state targetRequestConnection).head? =
      some ((systemServiceState state).regs
        targetRequest.bits.sinkPayloadName (HwPacked.width Request))

@[simp] theorem systemServiceRequestPending_reset :
    systemServiceRequestPending system.reset = [] := by rfl

theorem serviceRequestSinkCoherent_reset :
    ServiceRequestSinkCoherent system.reset := by
  intro pending
  have found : system.findIsland? "service" =
      some ⟨"service", "mem_clk", service⟩ := by rfl
  change (system.reset.island "service").regs
    targetRequest.bits.sinkPopName 1 = 1#1 at pending
  simp only [System.reset] at pending
  rw [found] at pending
  simp [service, serviceBody, PackedChan.withSink, PackedChan.withSource,
    Chan.withSink, Chan.withSource, Design.reset, targetRequest,
    targetResponse, audit, PackedChan.named, Chan.sinkPopName,
    Chan.sourceValidName, Chan.sourcePayloadName, Chan.stem] at pending

theorem system_advance_service_request_pop (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (ticks : event.fires "mem_clk" = true) :
    ((system.advance event external state).island "service").regs
        targetRequest.bits.sinkPopName 1 =
      if targetRequest.bits.canDeq.eval
          ((systemServiceState state).setInputs service.inputs
            (system.islandInput event state external "service")) = 1#1 ∧
        targetResponse.bits.canEnq.eval
          ((systemServiceState state).setInputs service.inputs
            (system.islandInput event state external "service")) = 1#1 ∧
        audit.bits.canEnq.eval
          ((systemServiceState state).setInputs service.inputs
            (system.islandInput event state external "service")) = 1#1
      then 1#1 else 0#1 := by
  have found : system.findIsland? "service" =
      some ⟨"service", "mem_clk", service⟩ := by rfl
  rw [System.advance_island_ticked system event external state
    ⟨"service", "mem_clk", service⟩ found ticks]
  exact service_cycleOpen_request_pop _ _

theorem system_advance_service_request_payload (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (ticks : event.fires "mem_clk" = true) :
    ((system.advance event external state).island "service").regs
        targetRequest.bits.sinkPayloadName (HwPacked.width Request) =
      (system.channelState state targetRequestConnection).head?.getD 0 := by
  have found : system.findIsland? "service" =
      some ⟨"service", "mem_clk", service⟩ := by rfl
  rw [System.advance_island_ticked system event external state
    ⟨"service", "mem_clk", service⟩ found ticks]
  rw [service_cycleOpen_request_payload]
  exact serviceInput_targetRequestPayload state event external

theorem system_targetRequest_sink_step (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (coherent : ServiceRequestSinkCoherent state) :
    ServiceRequestSinkCoherent (system.advance event external state) ∧
      systemServiceRequestPending state ++
          (systemServiceCommitRequest? state event external).toList =
        systemTargetRequestsDeliveredAt state event ++
          systemServiceRequestPending (system.advance event external state) := by
  by_cases ticks : event.fires "mem_clk" = true
  · let q := system.channelState state targetRequestConnection
    let payload := (systemServiceState state).regs
      targetRequest.bits.sinkPayloadName (HwPacked.width Request)
    let pop : Bool := (systemServiceState state).regs
      targetRequest.bits.sinkPopName 1 != 0
    let poked := (systemServiceState state).setInputs service.inputs
      (system.islandInput event state external "service")
    let enabled : Prop := targetRequest.bits.canDeq.eval poked = 1#1 ∧
      targetResponse.bits.canEnq.eval poked = 1#1 ∧
      audit.bits.canEnq.eval poked = 1#1
    let consume : Bool := decide enabled
    let requestEvent := system.connectionEvent event state targetRequestConnection
    have found : system.findIsland? "service" =
        some ⟨"service", "mem_clk", service⟩ := by rfl
    have eventPop : requestEvent.pop = pop := by
      simp [requestEvent, pop, System.connectionEvent,
        targetRequestConnection, found, ticks, systemServiceState, Expr.eval]
    have coherentBits : pop = true → q.head? = some payload := by
      intro pending
      have nonzero : (systemServiceState state).regs
          targetRequest.bits.sinkPopName 1 ≠ 0#1 := by
        simpa [pop] using pending
      have pendingOne : (systemServiceState state).regs
          targetRequest.bits.sinkPopName 1 = 1#1 := by bv_omega
      simpa [q, payload] using coherent pendingOne
    have consumeEnabled : consume = true ↔ enabled := by
      simp [consume]
    have consumeLegal : consume = true → pop = false ∧ q.isEmpty = false := by
      intro consumed
      have ready := (consumeEnabled.mp consumed).1
      have inputValid := serviceInput_targetRequestValid state event external
      have popStable : poked.regs targetRequest.bits.sinkPopName 1 =
          (systemServiceState state).regs targetRequest.bits.sinkPopName 1 := by rfl
      have validPoked : poked.regs targetRequest.bits.sinkValidName 1 =
          system.islandInput event state external "service"
            targetRequest.bits.sinkValidName 1 := by rfl
      change targetRequest.bits.canDeq.eval poked = 1#1 at ready
      rw [← validPoked] at inputValid
      change poked.regs targetRequest.bits.sinkValidName 1 =
          (if q.isEmpty then 0#1 else 1#1) at inputValid
      have popZero : poked.regs targetRequest.bits.sinkPopName 1 = 0#1 := by
        by_contra nonzero
        have popOne : poked.regs targetRequest.bits.sinkPopName 1 = 1#1 := by
          bv_omega
        have blocked := targetRequest.bits.canDeq_zero_of_pending poked popOne
        rw [blocked] at ready
        contradiction
      constructor
      · dsimp [pop]
        rw [popStable] at popZero
        simp [popZero]
      · by_contra empty
        have emptyTrue : q.isEmpty = true := Bool.eq_true_of_not_eq_false empty
        rw [emptyTrue] at inputValid
        simp only [if_true] at inputValid
        simp [PackedChan.canDeq, Chan.canDeq, Expr.eval, inputValid] at ready
    have localStep := targetRequest.bits.sinkStep_conservation q requestEvent.push
      pop payload consume coherentBits consumeLegal
    rw [← eventPop] at localStep
    have nextQueue : system.channelState (system.advance event external state)
        targetRequestConnection =
        (targetRequest.bits.step q requestEvent).state := by
      simpa [q, requestEvent, System.connectionResult, targetRequestConnection]
        using System.channelState_advance system event external state
          targetRequestConnection (by rfl)
    have nextPop := system_advance_service_request_pop state event external ticks
    have nextPayload := system_advance_service_request_payload state event external ticks
    have enabledDef : enabled = (targetRequest.bits.canDeq.eval poked = 1#1 ∧
        targetResponse.bits.canEnq.eval poked = 1#1 ∧
        audit.bits.canEnq.eval poked = 1#1) := rfl
    constructor
    · intro pending
      change ((system.advance event external state).island "service").regs
        targetRequest.bits.sinkPopName 1 = 1#1 at pending
      change ((system.advance event external state).island "service").regs
        targetRequest.bits.sinkPopName 1 = if enabled then 1#1 else 0#1 at nextPop
      have consumed : consume = true := by
        rw [nextPop] at pending
        by_cases h : enabled
        · exact consumeEnabled.mpr h
        · simp [h] at pending
      have headCoherent := localStep.2 consumed
      rw [nextQueue]
      change ((system.advance event external state).island "service").regs
        targetRequest.bits.sinkPayloadName (HwPacked.width Request) = _ at nextPayload
      change _ = some (((system.advance event external state).island
        "service").regs targetRequest.bits.sinkPayloadName
          (HwPacked.width Request))
      rw [nextPayload]
      simpa [q, requestEvent, Chan.sinkStep] using headCoherent
    · have inputPayload := serviceInput_targetRequestPayload state event external
      have pokedPayload : poked.regs targetRequest.bits.sinkPayloadName
          (HwPacked.width Request) = q.head?.getD 0 := by
        calc
          _ = system.islandInput event state external "service"
              targetRequest.bits.sinkPayloadName (HwPacked.width Request) := rfl
          _ = _ := by simpa [q] using inputPayload
      have requestValue : serviceRequestAt poked =
          HwPacked.unpack (q.head?.getD 0) := by
        simp [serviceRequestAt, PackedChan.deq, PackedExpr.eval,
          Chan.deq, Expr.eval, pokedPayload]
      have prePendingEq :
          (Chan.sinkPending pop payload).map HwPacked.unpack =
            systemServiceRequestPending state := by
        by_cases pending : (systemServiceState state).regs
            targetRequest.bits.sinkPopName 1 = 1#1
        · have popTrue : pop = true := by
            simp [pop, pending]
          simp [Chan.sinkPending, popTrue, systemServiceRequestPending,
            pending, payload]
        · have popZero : (systemServiceState state).regs
              targetRequest.bits.sinkPopName 1 = 0#1 := by bv_omega
          have popFalse : pop = false := by simp [pop, popZero]
          simp [Chan.sinkPending, popFalse, systemServiceRequestPending, pending]
      have commitEq :
          (if consume then [q.head?.getD 0] else []).map HwPacked.unpack =
            (systemServiceCommitRequest? state event external).toList := by
        simp only [systemServiceCommitRequest?, ticks, if_true]
        change _ = (if enabled then some (serviceRequestAt poked) else none).toList
        by_cases h : enabled
        · have consumed : consume = true := consumeEnabled.mpr h
          simp [consumed, h, requestValue]
        · have consumed : consume = false := by simp [consume, h]
          simp [consumed, h]
      have deliveredEq :
          (targetRequest.bits.deliveredValues q
              { push := requestEvent.push, pop := requestEvent.pop }).map
                HwPacked.unpack =
            systemTargetRequestsDeliveredAt state event := by
        simp only [systemTargetRequestsDeliveredAt, System.connectionResult,
          Chan.deliveredValues]
        rfl
      have nextPendingEq :
          (Chan.sinkPending (Chan.sinkStep q consume).1
              (Chan.sinkStep q consume).2).map HwPacked.unpack =
            systemServiceRequestPending (system.advance event external state) := by
        change ((system.advance event external state).island "service").regs
          targetRequest.bits.sinkPopName 1 = if enabled then 1#1 else 0#1 at nextPop
        change ((system.advance event external state).island "service").regs
          targetRequest.bits.sinkPayloadName (HwPacked.width Request) = _ at nextPayload
        by_cases h : enabled
        · have consumed : consume = true := consumeEnabled.mpr h
          have pendingOne : ((system.advance event external state).island
              "service").regs targetRequest.bits.sinkPopName 1 = 1#1 := by
            simpa [h] using nextPop
          simp [Chan.sinkPending, Chan.sinkStep, consumed,
            systemServiceRequestPending, systemServiceState, pendingOne,
            nextPayload, q]
        · have consumed : consume = false := by simp [consume, h]
          have pendingZero : ((system.advance event external state).island
              "service").regs targetRequest.bits.sinkPopName 1 = 0#1 := by
            simpa [h] using nextPop
          simp [Chan.sinkPending, Chan.sinkStep, consumed,
            systemServiceRequestPending, systemServiceState, pendingZero]
      have prePendingEventEq :
          (Chan.sinkPending requestEvent.pop payload).map HwPacked.unpack =
            systemServiceRequestPending state := by
        rw [eventPop]
        exact prePendingEq
      have ledger := congrArg (List.map HwPacked.unpack) localStep.1
      simp only [List.map_append] at ledger
      change _ = (targetRequest.bits.deliveredValues q requestEvent).map
          HwPacked.unpack ++ _ at ledger
      rw [prePendingEventEq, commitEq, deliveredEq, nextPendingEq] at ledger
      exact ledger
  · have unticked : event.fires "mem_clk" = false :=
      Bool.eq_false_of_not_eq_true ticks
    have found : system.findIsland? "service" =
        some ⟨"service", "mem_clk", service⟩ := by rfl
    have nextIsland := System.advance_island_unticked system event external state
      ⟨"service", "mem_clk", service⟩ found unticked
    have deliveredNone :
        (system.connectionResult event state targetRequestConnection).delivered = none := by
      simp [System.connectionResult, System.connectionEvent,
        targetRequestConnection, found, unticked, targetRequest,
        PackedChan.named, Chan.step]
    constructor
    · intro pending
      change ((system.advance event external state).island "service").regs
        targetRequest.bits.sinkPopName 1 = 1#1 at pending
      rw [nextIsland] at pending
      have oldHead := coherent pending
      have eventPop : (system.connectionEvent event state
          targetRequestConnection).pop = false := by
        simp [System.connectionEvent, targetRequestConnection, found, unticked]
      have stableHead := targetRequest.bits.step_head_of_no_pop
        (system.channelState state targetRequestConnection)
        (system.connectionEvent event state targetRequestConnection).push
        ((systemServiceState state).regs targetRequest.bits.sinkPayloadName
          (HwPacked.width Request)) oldHead
      have nextQueue := System.channelState_advance system event external state
        targetRequestConnection (by rfl)
      rw [nextQueue]
      change _ = some (((system.advance event external state).island
        "service").regs targetRequest.bits.sinkPayloadName
          (HwPacked.width Request))
      rw [nextIsland]
      change (system.connectionResult event state
          targetRequestConnection).state.head? = _
      rw [show system.connectionResult event state targetRequestConnection =
          targetRequest.bits.step (system.channelState state targetRequestConnection)
            (system.connectionEvent event state targetRequestConnection) by rfl]
      have requestEventEq : system.connectionEvent event state
          targetRequestConnection =
          { push := (system.connectionEvent event state
              targetRequestConnection).push, pop := false } := by
        cases h : system.connectionEvent event state targetRequestConnection with
        | mk push pop =>
            simp only at eventPop
            simp [h] at eventPop ⊢
            exact eventPop
      rw [requestEventEq]
      simpa [systemServiceState] using stableHead
    · simp [systemServiceCommitRequest?, ticks, systemTargetRequestsDeliveredAt,
        deliveredNone, systemServiceRequestPending, systemServiceState,
        nextIsland]

def systemTargetRequestDeliveredTraceFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List Request
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemTargetRequestsDeliveredAt state event ++
        systemTargetRequestDeliveredTraceFrom inputs
          (system.advance event external state) rest

/-- Arbitrary-schedule preservation of sink-head coherence together with the
finite-prefix request ledger.  The suffix is the literal registered pop at
the service boundary, not an abstract ghost counter. -/
theorem system_targetRequest_sink_invariant (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent)
    (coherent : ServiceRequestSinkCoherent state) :
    ServiceRequestSinkCoherent (system.runEventsFrom inputs state events) ∧
      systemServiceRequestPending state ++
          systemServiceCommitRequestsFrom inputs state events =
        systemTargetRequestDeliveredTraceFrom inputs state events ++
          systemServiceRequestPending
            (system.runEventsFrom inputs state events) := by
  induction events generalizing state with
  | nil =>
      simp [System.runEventsFrom, systemServiceCommitRequestsFrom,
        systemTargetRequestDeliveredTraceFrom, coherent]
  | cons event rest ih =>
      let external := inputs state.time
      let next := system.advance event external state
      have step := system_targetRequest_sink_step state event external coherent
      have later := ih next step.1
      constructor
      · simpa [System.runEventsFrom, next, external] using later.1
      · simp only [systemServiceCommitRequestsFrom,
          systemTargetRequestDeliveredTraceFrom, System.runEventsFrom]
        change systemServiceRequestPending state ++
            (match systemServiceCommitRequest? state event external with
              | some request => request ::
                  systemServiceCommitRequestsFrom inputs next rest
              | none => systemServiceCommitRequestsFrom inputs next rest) =
            (systemTargetRequestsDeliveredAt state event ++
              systemTargetRequestDeliveredTraceFrom inputs next rest) ++
                systemServiceRequestPending
                  (system.runEventsFrom inputs next rest)
        cases committed : systemServiceCommitRequest? state event external with
        | none =>
            rw [committed] at step
            simp only [Option.toList_none, List.append_nil] at step
            simp only
            calc
              _ = (systemTargetRequestsDeliveredAt state event ++
                    systemServiceRequestPending next) ++
                    systemServiceCommitRequestsFrom inputs next rest := by
                  rw [step.2]
              _ = systemTargetRequestsDeliveredAt state event ++
                    (systemServiceRequestPending next ++
                      systemServiceCommitRequestsFrom inputs next rest) := by
                  rw [List.append_assoc]
              _ = _ := by
                  rw [later.2, ← List.append_assoc]
        | some request =>
            rw [committed] at step
            simp only [Option.toList_some] at step
            simp only
            change systemServiceRequestPending state ++
                ([request] ++ systemServiceCommitRequestsFrom inputs next rest) = _
            calc
              _ = (systemServiceRequestPending state ++ [request]) ++
                    systemServiceCommitRequestsFrom inputs next rest := by
                  rw [List.append_assoc]
              _ = (systemTargetRequestsDeliveredAt state event ++
                    systemServiceRequestPending next) ++
                    systemServiceCommitRequestsFrom inputs next rest := by
                  rw [step.2]
              _ = systemTargetRequestsDeliveredAt state event ++
                    (systemServiceRequestPending next ++
                      systemServiceCommitRequestsFrom inputs next rest) := by
                  rw [List.append_assoc]
              _ = _ := by
                  rw [later.2, ← List.append_assoc]

theorem reset_service_request_sink_ledger (events : List NamedClockEvent) :
    systemServiceCommitRequestsFrom noInputs system.reset events =
      systemTargetRequestDeliveredTraceFrom noInputs system.reset events ++
        systemServiceRequestPending
          (system.runEventsFrom noInputs system.reset events) := by
  have invariant := system_targetRequest_sink_invariant noInputs system.reset events
    serviceRequestSinkCoherent_reset
  simpa using invariant.2

theorem reset_service_requests_eq_delivered_of_drained
    (events : List NamedClockEvent)
    (drained : systemServiceRequestPending
      (system.runEventsFrom noInputs system.reset events) = []) :
    systemServiceCommitRequestsFrom noInputs system.reset events =
      systemTargetRequestDeliveredTraceFrom noInputs system.reset events := by
  rw [reset_service_request_sink_ledger events, drained, List.append_nil]

theorem systemTargetRequestDeliveredTrace_eq_fifo (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemTargetRequestDeliveredTraceFrom inputs state events =
      (targetRequest.bits.runTrace
        (system.channelState state targetRequestConnection)
        (system.channelEventsFrom inputs targetRequestConnection state events)).delivered.map
          HwPacked.unpack := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemTargetRequestDeliveredTraceFrom,
        System.channelEventsFrom, Chan.runTrace, List.map_append]
      let external := inputs state.time
      let next := system.advance event external state
      change systemTargetRequestsDeliveredAt state event ++
          systemTargetRequestDeliveredTraceFrom inputs next rest = _
      rw [ih next]
      rw [System.channelState_advance system event external state
        targetRequestConnection (by rfl)]
      rfl

private theorem chan_accepted_implies_push {w : Nat} (channel : Chan w)
    (queue : Chan.State w) (event : Chan.Event w)
    (accepted : (channel.step queue event).accepted = true) :
    event.push.isSome = true := by
  rcases event with ⟨push, pop⟩
  cases push <;> simp [Chan.step] at accepted ⊢

private theorem targetRequest_accepted_implies_valid (state : system.State)
    (event : NamedClockEvent)
    (accepted : (system.connectionResult event state
      targetRequestConnection).accepted = true) :
    (state.island "fabric").regs
      targetRequest.bits.sourceValidName 1 = 1#1 := by
  have pushed := chan_accepted_implies_push targetRequest.bits
    (system.connectionQueue state targetRequestConnection)
    (system.connectionEvent event state targetRequestConnection) accepted
  simp [System.connectionEvent, system, targetRequestConnection] at pushed
  have nonzero : (state.island "fabric").regs
      targetRequest.bits.sourceValidName 1 ≠ 0#1 := by
    simpa [targetRequest, PackedChan.named, Chan.sourceValid,
      Chan.sourceValidName, Chan.stem, Expr.eval] using pushed.2
  bv_omega

private theorem cpuResponse_accepted_implies_valid (state : system.State)
    (event : NamedClockEvent)
    (accepted : (system.connectionResult event state
      cpuResponseConnection).accepted = true) :
    (state.island "fabric").regs cpuResponse.bits.sourceValidName 1 = 1#1 := by
  have pushed := chan_accepted_implies_push cpuResponse.bits
    (system.connectionQueue state cpuResponseConnection)
    (system.connectionEvent event state cpuResponseConnection) accepted
  simp [System.connectionEvent, system, cpuResponseConnection] at pushed
  have nonzero : (state.island "fabric").regs
      cpuResponse.bits.sourceValidName 1 ≠ 0#1 := by
    simpa [cpuResponse, PackedChan.named, Chan.sourceValid,
      Chan.sourceValidName, Chan.stem, Expr.eval] using pushed.2
  bv_omega

private theorem dmaResponse_accepted_implies_valid (state : system.State)
    (event : NamedClockEvent)
    (accepted : (system.connectionResult event state
      dmaResponseConnection).accepted = true) :
    (state.island "fabric").regs dmaResponse.bits.sourceValidName 1 = 1#1 := by
  have pushed := chan_accepted_implies_push dmaResponse.bits
    (system.connectionQueue state dmaResponseConnection)
    (system.connectionEvent event state dmaResponseConnection) accepted
  simp [System.connectionEvent, system, dmaResponseConnection] at pushed
  have nonzero : (state.island "fabric").regs
      dmaResponse.bits.sourceValidName 1 ≠ 0#1 := by
    simpa [dmaResponse, PackedChan.named, Chan.sourceValid,
      Chan.sourceValidName, Chan.stem, Expr.eval] using pushed.2
  bv_omega

def systemFabricTargetRequestPending (state : system.State) : List Request :=
  fabricTargetRequestPending (systemFabricState state)

def systemFabricTargetRequestsProducedAt (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) : List Request :=
  if event.fires "cpu_fabric_clk" = true then
    fabricTargetRequestProduced ((systemFabricState state).setInputs fabric.inputs
      (system.islandInput event state external "fabric"))
  else []

def systemTargetRequestsAcceptedAt (state : system.State)
    (event : NamedClockEvent) : List Request :=
  (targetRequest.bits.acceptedValues
    (system.connectionQueue state targetRequestConnection)
    (system.connectionEvent event state targetRequestConnection)).map HwPacked.unpack

def systemFabricResponsePending (channel : PackedChan Response)
    (state : system.State) : List Response :=
  fabricResponsePending channel (systemFabricState state)

def systemFabricResponseProducedAt (client : FabricResponseRoute)
    (state : system.State) (event : NamedClockEvent)
    (external : String → InEnv) : List Response :=
  if event.fires "cpu_fabric_clk" = true then
    fabricResponseProduced client ((systemFabricState state).setInputs
      fabric.inputs (system.islandInput event state external "fabric"))
  else []

def systemCpuResponsesAcceptedAt (state : system.State)
    (event : NamedClockEvent) : List Response :=
  (cpuResponse.bits.acceptedValues
    (system.connectionQueue state cpuResponseConnection)
    (system.connectionEvent event state cpuResponseConnection)).map HwPacked.unpack

def systemDmaResponsesAcceptedAt (state : system.State)
    (event : NamedClockEvent) : List Response :=
  (dmaResponse.bits.acceptedValues
    (system.connectionQueue state dmaResponseConnection)
    (system.connectionEvent event state dmaResponseConnection)).map HwPacked.unpack

def systemFabricGrantObservationsAt (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    List (FabricClient × Request) :=
  if event.fires "cpu_fabric_clk" = true then
    fabricGrantObservations ((systemFabricState state).setInputs fabric.inputs
      (system.islandInput event state external "fabric"))
  else []

def systemFabricRoutedResponseObservationsAt (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    List (FabricClient × Response) :=
  if event.fires "cpu_fabric_clk" = true then
    fabricRoutedResponseObservations
      ((systemFabricState state).setInputs fabric.inputs
        (system.islandInput event state external "fabric"))
  else []

theorem systemFabricGrantObservationsAt_clients (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    (systemFabricGrantObservationsAt state event external).map Prod.fst =
      systemFabricGrantClientsAt state event external := by
  by_cases ticks : event.fires "cpu_fabric_clk" = true <;>
    simp [systemFabricGrantObservationsAt, systemFabricGrantClientsAt, ticks,
      fabricGrantObservations_clients]

theorem systemFabricGrantObservationsAt_requests (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    (systemFabricGrantObservationsAt state event external).map Prod.snd =
      systemFabricTargetRequestsProducedAt state event external := by
  by_cases ticks : event.fires "cpu_fabric_clk" = true <;>
    simp [systemFabricGrantObservationsAt,
      systemFabricTargetRequestsProducedAt, ticks,
      fabricGrantObservations_requests]

theorem systemFabricRoutedResponseObservationsAt_clients
    (state : system.State) (event : NamedClockEvent)
    (external : String → InEnv) :
    (systemFabricRoutedResponseObservationsAt state event external).map Prod.fst =
      systemFabricRoutedClientsAt state event external := by
  by_cases ticks : event.fires "cpu_fabric_clk" = true <;>
    simp [systemFabricRoutedResponseObservationsAt,
      systemFabricRoutedClientsAt, ticks,
      fabricRoutedResponseObservations_clients]

theorem systemFabricRoutedResponseObservationsAt_responses
    (state : system.State) (event : NamedClockEvent)
    (external : String → InEnv) :
    (systemFabricRoutedResponseObservationsAt state event external).map Prod.snd =
      systemFabricResponsesRoutedAt state event external := by
  by_cases ticks : event.fires "cpu_fabric_clk" = true <;>
    simp [systemFabricRoutedResponseObservationsAt,
      systemFabricResponsesRoutedAt, ticks,
      fabricRoutedResponseObservations_responses]

def systemFabricGrantObservationTraceFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List (FabricClient × Request)
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemFabricGrantObservationsAt state event external ++
        systemFabricGrantObservationTraceFrom inputs
          (system.advance event external state) rest

def systemFabricRoutedResponseObservationTraceFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List (FabricClient × Response)
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemFabricRoutedResponseObservationsAt state event external ++
        systemFabricRoutedResponseObservationTraceFrom inputs
          (system.advance event external state) rest

def selectClientValues {α : Type} (client : FabricClient) :
    List (FabricClient × α) → List α :=
  List.filterMap (fun observation =>
    if observation.1 = client then some observation.2 else none)

theorem systemFabricGrantObservationsAt_select (client : FabricClient)
    (state : system.State) (event : NamedClockEvent)
    (external : String → InEnv) :
    selectClientValues client
        (systemFabricGrantObservationsAt state event external) =
      systemFabricClientRequestsGrantedAt client state event external := by
  by_cases ticks : event.fires "cpu_fabric_clk" = true
  · simp only [systemFabricGrantObservationsAt,
      systemFabricClientRequestsGrantedAt, ticks, if_true]
    let poked := (systemFabricState state).setInputs fabric.inputs
      (system.islandInput event state external "fabric")
    cases choice : fabricGrantChoice poked with
    | none => simp [fabricGrantObservations, selectClientValues, choice, poked]
    | some selected =>
        cases selected <;> cases client <;>
          simp [fabricGrantObservations, selectClientValues, choice, poked]
  · simp [systemFabricGrantObservationsAt,
      systemFabricClientRequestsGrantedAt, ticks, selectClientValues]

theorem systemFabricGrantObservationTrace_select (client : FabricClient)
    (inputs : ExternalInputs) (state : system.State)
    (events : List NamedClockEvent) :
    selectClientValues client
        (systemFabricGrantObservationTraceFrom inputs state events) =
      systemFabricClientRequestGrantTraceFrom client inputs state events := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemFabricGrantObservationTraceFrom,
        systemFabricClientRequestGrantTraceFrom, selectClientValues,
        List.filterMap_append]
      change selectClientValues client
          (systemFabricGrantObservationsAt state event (inputs state.time)) ++
          selectClientValues client
            (systemFabricGrantObservationTraceFrom inputs
              (system.advance event (inputs state.time) state) rest) = _
      rw [systemFabricGrantObservationsAt_select, ih]

theorem systemFabricGrantObservationTrace_clients (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    (systemFabricGrantObservationTraceFrom inputs state events).map Prod.fst =
      systemFabricGrantClientTraceFrom inputs state events := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemFabricGrantObservationTraceFrom,
        systemFabricGrantClientTraceFrom, List.map_append]
      rw [systemFabricGrantObservationsAt_clients, ih]

theorem systemFabricRoutedResponseObservationTrace_clients
    (inputs : ExternalInputs) (state : system.State)
    (events : List NamedClockEvent) :
    (systemFabricRoutedResponseObservationTraceFrom inputs state events).map
        Prod.fst = systemFabricRoutedClientTraceFrom inputs state events := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemFabricRoutedResponseObservationTraceFrom,
        systemFabricRoutedClientTraceFrom, List.map_append]
      rw [systemFabricRoutedResponseObservationsAt_clients, ih]

theorem systemFabricRoutedResponseObservationTrace_responses
    (inputs : ExternalInputs) (state : system.State)
    (events : List NamedClockEvent) :
    (systemFabricRoutedResponseObservationTraceFrom inputs state events).map
        Prod.snd = systemFabricRoutedResponseTraceFrom inputs state events := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemFabricRoutedResponseObservationTraceFrom,
        systemFabricRoutedResponseTraceFrom, List.map_append]
      rw [systemFabricRoutedResponseObservationsAt_responses, ih]

private theorem targetResponse_accepted_implies_valid (state : system.State)
    (event : NamedClockEvent)
    (accepted : (system.connectionResult event state
      targetResponseConnection).accepted = true) :
    (state.island "service").regs
      targetResponse.bits.sourceValidName 1 = 1#1 := by
  have pushed := chan_accepted_implies_push targetResponse.bits
    (system.connectionQueue state targetResponseConnection)
    (system.connectionEvent event state targetResponseConnection) accepted
  simp [System.connectionEvent, system, connectionInventory,
    targetResponseConnection] at pushed
  have nonzero : (state.island "service").regs
      targetResponse.bits.sourceValidName 1 ≠ 0#1 := by
    simpa [targetResponse, PackedChan.named, Chan.sourceValid,
      Chan.sourceValidName, Chan.stem, Expr.eval] using pushed.2
  bv_omega

def systemServiceResponsePending (state : system.State) : List Response :=
  serviceResponsePending (systemServiceState state)

def systemServiceResponsesProducedAt (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) : List Response :=
  if event.fires "mem_clk" = true then
    serviceResponseProduced ((systemServiceState state).setInputs service.inputs
      (system.islandInput event state external "service"))
  else []

def systemTargetResponsesAcceptedAt (state : system.State)
    (event : NamedClockEvent) : List Response :=
  (targetResponse.bits.acceptedValues
    (system.connectionQueue state targetResponseConnection)
    (system.connectionEvent event state targetResponseConnection)).map HwPacked.unpack

private theorem targetRequest_fabricAccepted_eq (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (ticks : event.fires "cpu_fabric_clk" = true) :
    fabricTargetRequestAccepted ((systemFabricState state).setInputs fabric.inputs
      (system.islandInput event state external "fabric")) =
      systemTargetRequestsAcceptedAt state event := by
  let result := system.connectionResult event state targetRequestConnection
  have inputAccepted := fabricInput_targetRequestAccepted state event external
  have acceptedPoked :
      ((systemFabricState state).setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
          targetRequest.bits.sourceAcceptedName 1 =
      system.islandInput event state external "fabric"
        targetRequest.bits.sourceAcceptedName 1 := by rfl
  have stableValid :
      ((systemFabricState state).setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
          targetRequest.bits.sourceValidName 1 =
      (systemFabricState state).regs
        targetRequest.bits.sourceValidName 1 := by rfl
  have stablePayload :
      ((systemFabricState state).setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
          targetRequest.bits.sourcePayloadName (HwPacked.width Request) =
      (systemFabricState state).regs
        targetRequest.bits.sourcePayloadName (HwPacked.width Request) := by rfl
  by_cases accepted : result.accepted = true
  · have valid := targetRequest_accepted_implies_valid state event accepted
    have acceptedInputValue : system.islandInput event state external "fabric"
        targetRequest.bits.sourceAcceptedName 1 = 1#1 := by
      rw [inputAccepted, accepted]
      rfl
    have acceptedReg := acceptedPoked.trans acceptedInputValue
    have stepAccepted : (targetRequest.bits.step
        (system.connectionQueue state targetRequestConnection)
        (system.connectionEvent event state targetRequestConnection)).accepted = true := by
      simpa [System.connectionResult, result, targetRequestConnection] using accepted
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have pushEq : (system.connectionEvent event state targetRequestConnection).push =
        some (targetRequest.bits.sourcePayload.eval (state.island "fabric")) := by
      simp [System.connectionEvent, targetRequestConnection, found, ticks,
        targetRequest, PackedChan.named, Chan.sourceValid, Chan.sourcePayload,
        Chan.sourceValidName, Chan.sourcePayloadName, Chan.stem, Expr.eval]
      have nonzero : (state.island "fabric").regs
          targetRequest.bits.sourceValidName 1 ≠ 0#1 := by bv_omega
      exact nonzero
    have acceptedReg' :
        ((state.island "fabric").setInputs fabric.inputs
          (system.islandInput event state external "fabric")).regs
            "__loom_chan_target_request_src_accepted" 1 = 1#1 := by
      simpa [systemFabricState, targetRequest, PackedChan.named,
        Chan.sourceAcceptedName, Chan.stem] using acceptedReg
    have stableValid' :
        ((state.island "fabric").setInputs fabric.inputs
          (system.islandInput event state external "fabric")).regs
            "__loom_chan_target_request_src_valid" 1 =
          (state.island "fabric").regs
            "__loom_chan_target_request_src_valid" 1 := by
      simpa [systemFabricState, targetRequest, PackedChan.named,
        Chan.sourceValidName, Chan.stem] using stableValid
    have stablePayload' :
        ((state.island "fabric").setInputs fabric.inputs
          (system.islandInput event state external "fabric")).regs
            "__loom_chan_target_request_src_payload" (HwPacked.width Request) =
          (state.island "fabric").regs
            "__loom_chan_target_request_src_payload" (HwPacked.width Request) := by
      simpa [systemFabricState, targetRequest, PackedChan.named,
        Chan.sourcePayloadName, Chan.stem] using stablePayload
    have valid' : (state.island "fabric").regs
        "__loom_chan_target_request_src_valid" 1 = 1#1 := by
      simpa [targetRequest, PackedChan.named, Chan.sourceValidName,
        Chan.stem] using valid
    have stepAccepted' : (({ name := "target_request", depth := 4 } :
        Chan (HwPacked.width Request)).step
          (system.connectionQueue state targetRequestConnection)
          (system.connectionEvent event state targetRequestConnection)).accepted = true := by
      simpa [targetRequest, PackedChan.named] using stepAccepted
    simp [fabricTargetRequestAccepted, fabricTargetRequestPending,
      systemTargetRequestsAcceptedAt, Chan.acceptedValues, stepAccepted',
      acceptedReg', stableValid', stablePayload', valid', pushEq,
      systemFabricState, targetRequest, PackedChan.named,
      Chan.sourceAccepted, Chan.sourceAcceptedName, Chan.sourceValidName,
      Chan.sourcePayload, Chan.sourcePayloadName, Chan.stem, Expr.eval]
  · have acceptedFalse : result.accepted = false :=
      Bool.eq_false_of_not_eq_true accepted
    have acceptedInputValue : system.islandInput event state external "fabric"
        targetRequest.bits.sourceAcceptedName 1 = 0#1 := by
      rw [inputAccepted, acceptedFalse]
      rfl
    have acceptedReg := acceptedPoked.trans acceptedInputValue
    have stepAccepted : (targetRequest.bits.step
        (system.connectionQueue state targetRequestConnection)
        (system.connectionEvent event state targetRequestConnection)).accepted = false := by
      simpa [System.connectionResult, result, targetRequestConnection] using
        acceptedFalse
    have stepAccepted' : (({ name := "target_request", depth := 4 } :
        Chan (HwPacked.width Request)).step
          (system.connectionQueue state targetRequestConnection)
          (system.connectionEvent event state targetRequestConnection)).accepted = false := by
      simpa [targetRequest, PackedChan.named] using stepAccepted
    have acceptedReg' :
        ((state.island "fabric").setInputs fabric.inputs
          (system.islandInput event state external "fabric")).regs
            "__loom_chan_target_request_src_accepted" 1 = 0#1 := by
      simpa [systemFabricState, targetRequest, PackedChan.named,
        Chan.sourceAcceptedName, Chan.stem] using acceptedReg
    simp [fabricTargetRequestAccepted, systemTargetRequestsAcceptedAt,
      Chan.acceptedValues, stepAccepted', acceptedReg', systemFabricState,
      targetRequest, PackedChan.named, Chan.sourceAccepted,
      Chan.sourceAcceptedName, Chan.stem, Expr.eval]

private theorem cpuResponse_fabricAccepted_eq (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (ticks : event.fires "cpu_fabric_clk" = true) :
    fabricResponseAccepted cpuResponse ((systemFabricState state).setInputs
      fabric.inputs (system.islandInput event state external "fabric")) =
      systemCpuResponsesAcceptedAt state event := by
  let result := system.connectionResult event state cpuResponseConnection
  have inputAccepted := fabricInput_cpuResponseAccepted state event external
  have acceptedPoked :
      ((systemFabricState state).setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
          cpuResponse.bits.sourceAcceptedName 1 =
      system.islandInput event state external "fabric"
        cpuResponse.bits.sourceAcceptedName 1 := by rfl
  have stableValid :
      ((systemFabricState state).setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
          cpuResponse.bits.sourceValidName 1 =
      (systemFabricState state).regs cpuResponse.bits.sourceValidName 1 := by rfl
  have stablePayload :
      ((systemFabricState state).setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
          cpuResponse.bits.sourcePayloadName (HwPacked.width Response) =
      (systemFabricState state).regs cpuResponse.bits.sourcePayloadName
        (HwPacked.width Response) := by rfl
  by_cases accepted : result.accepted = true
  · have valid := cpuResponse_accepted_implies_valid state event accepted
    have acceptedValue : system.islandInput event state external "fabric"
        cpuResponse.bits.sourceAcceptedName 1 = 1#1 := by
      rw [inputAccepted, accepted]
      rfl
    have acceptedReg := acceptedPoked.trans acceptedValue
    have stepAccepted : (cpuResponse.bits.step
        (system.connectionQueue state cpuResponseConnection)
        (system.connectionEvent event state cpuResponseConnection)).accepted = true := by
      simpa [System.connectionResult, result, cpuResponseConnection] using accepted
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have pushEq : (system.connectionEvent event state cpuResponseConnection).push =
        some (cpuResponse.bits.sourcePayload.eval (state.island "fabric")) := by
      simp [System.connectionEvent, cpuResponseConnection, found, ticks,
        cpuResponse, PackedChan.named, Chan.sourceValid, Chan.sourcePayload,
        Chan.sourceValidName, Chan.sourcePayloadName, Chan.stem, Expr.eval]
      have nonzero : (state.island "fabric").regs
          cpuResponse.bits.sourceValidName 1 ≠ 0#1 := by bv_omega
      exact nonzero
    have acceptedReg' : ((state.island "fabric").setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
        "__loom_chan_cpu_response_src_accepted" 1 = 1#1 := by
      simpa [systemFabricState, cpuResponse, PackedChan.named,
        Chan.sourceAcceptedName, Chan.stem] using acceptedReg
    have stableValid' : ((state.island "fabric").setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
        "__loom_chan_cpu_response_src_valid" 1 =
        (state.island "fabric").regs "__loom_chan_cpu_response_src_valid" 1 := by
      simpa [systemFabricState, cpuResponse, PackedChan.named,
        Chan.sourceValidName, Chan.stem] using stableValid
    have stablePayload' : ((state.island "fabric").setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
        "__loom_chan_cpu_response_src_payload" (HwPacked.width Response) =
        (state.island "fabric").regs "__loom_chan_cpu_response_src_payload"
          (HwPacked.width Response) := by
      simpa [systemFabricState, cpuResponse, PackedChan.named,
        Chan.sourcePayloadName, Chan.stem] using stablePayload
    have valid' : (state.island "fabric").regs
        "__loom_chan_cpu_response_src_valid" 1 = 1#1 := by
      simpa [cpuResponse, PackedChan.named, Chan.sourceValidName,
        Chan.stem] using valid
    have stepAccepted' : (({ name := "cpu_response", depth := 2 } :
        Chan (HwPacked.width Response)).step
          (system.connectionQueue state cpuResponseConnection)
          (system.connectionEvent event state cpuResponseConnection)).accepted = true := by
      simpa [cpuResponse, PackedChan.named] using stepAccepted
    simp [fabricResponseAccepted, fabricResponsePending,
      systemCpuResponsesAcceptedAt, Chan.acceptedValues, stepAccepted',
      acceptedReg', stableValid', stablePayload', valid', pushEq,
      systemFabricState, cpuResponse, PackedChan.named, Chan.sourceAccepted,
      Chan.sourceAcceptedName, Chan.sourceValidName, Chan.sourcePayload,
      Chan.sourcePayloadName, Chan.stem, Expr.eval]
  · have acceptedFalse : result.accepted = false :=
      Bool.eq_false_of_not_eq_true accepted
    have acceptedValue : system.islandInput event state external "fabric"
        cpuResponse.bits.sourceAcceptedName 1 = 0#1 := by
      rw [inputAccepted, acceptedFalse]
      rfl
    have acceptedReg := acceptedPoked.trans acceptedValue
    have stepAccepted : (cpuResponse.bits.step
        (system.connectionQueue state cpuResponseConnection)
        (system.connectionEvent event state cpuResponseConnection)).accepted = false := by
      simpa [System.connectionResult, result, cpuResponseConnection] using
        acceptedFalse
    have acceptedReg' : ((state.island "fabric").setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
        "__loom_chan_cpu_response_src_accepted" 1 = 0#1 := by
      simpa [systemFabricState, cpuResponse, PackedChan.named,
        Chan.sourceAcceptedName, Chan.stem] using acceptedReg
    have stepAccepted' : (({ name := "cpu_response", depth := 2 } :
        Chan (HwPacked.width Response)).step
          (system.connectionQueue state cpuResponseConnection)
          (system.connectionEvent event state cpuResponseConnection)).accepted = false := by
      simpa [cpuResponse, PackedChan.named] using stepAccepted
    simp [fabricResponseAccepted, systemCpuResponsesAcceptedAt,
      Chan.acceptedValues, stepAccepted', acceptedReg', systemFabricState,
      cpuResponse, PackedChan.named, Chan.sourceAccepted,
      Chan.sourceAcceptedName, Chan.stem, Expr.eval]

private theorem dmaResponse_fabricAccepted_eq (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (ticks : event.fires "cpu_fabric_clk" = true) :
    fabricResponseAccepted dmaResponse ((systemFabricState state).setInputs
      fabric.inputs (system.islandInput event state external "fabric")) =
      systemDmaResponsesAcceptedAt state event := by
  let result := system.connectionResult event state dmaResponseConnection
  have inputAccepted := fabricInput_dmaResponseAccepted state event external
  have acceptedPoked :
      ((systemFabricState state).setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
          dmaResponse.bits.sourceAcceptedName 1 =
      system.islandInput event state external "fabric"
        dmaResponse.bits.sourceAcceptedName 1 := by rfl
  have stableValid :
      ((systemFabricState state).setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
          dmaResponse.bits.sourceValidName 1 =
      (systemFabricState state).regs dmaResponse.bits.sourceValidName 1 := by rfl
  have stablePayload :
      ((systemFabricState state).setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
          dmaResponse.bits.sourcePayloadName (HwPacked.width Response) =
      (systemFabricState state).regs dmaResponse.bits.sourcePayloadName
        (HwPacked.width Response) := by rfl
  by_cases accepted : result.accepted = true
  · have valid := dmaResponse_accepted_implies_valid state event accepted
    have acceptedValue : system.islandInput event state external "fabric"
        dmaResponse.bits.sourceAcceptedName 1 = 1#1 := by
      rw [inputAccepted, accepted]
      rfl
    have acceptedReg := acceptedPoked.trans acceptedValue
    have stepAccepted : (dmaResponse.bits.step
        (system.connectionQueue state dmaResponseConnection)
        (system.connectionEvent event state dmaResponseConnection)).accepted = true := by
      simpa [System.connectionResult, result, dmaResponseConnection] using accepted
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have pushEq : (system.connectionEvent event state dmaResponseConnection).push =
        some (dmaResponse.bits.sourcePayload.eval (state.island "fabric")) := by
      simp [System.connectionEvent, dmaResponseConnection, found, ticks,
        dmaResponse, PackedChan.named, Chan.sourceValid, Chan.sourcePayload,
        Chan.sourceValidName, Chan.sourcePayloadName, Chan.stem, Expr.eval]
      have nonzero : (state.island "fabric").regs
          dmaResponse.bits.sourceValidName 1 ≠ 0#1 := by bv_omega
      exact nonzero
    have acceptedReg' : ((state.island "fabric").setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
        "__loom_chan_dma_response_src_accepted" 1 = 1#1 := by
      simpa [systemFabricState, dmaResponse, PackedChan.named,
        Chan.sourceAcceptedName, Chan.stem] using acceptedReg
    have stableValid' : ((state.island "fabric").setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
        "__loom_chan_dma_response_src_valid" 1 =
        (state.island "fabric").regs "__loom_chan_dma_response_src_valid" 1 := by
      simpa [systemFabricState, dmaResponse, PackedChan.named,
        Chan.sourceValidName, Chan.stem] using stableValid
    have stablePayload' : ((state.island "fabric").setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
        "__loom_chan_dma_response_src_payload" (HwPacked.width Response) =
        (state.island "fabric").regs "__loom_chan_dma_response_src_payload"
          (HwPacked.width Response) := by
      simpa [systemFabricState, dmaResponse, PackedChan.named,
        Chan.sourcePayloadName, Chan.stem] using stablePayload
    have valid' : (state.island "fabric").regs
        "__loom_chan_dma_response_src_valid" 1 = 1#1 := by
      simpa [dmaResponse, PackedChan.named, Chan.sourceValidName,
        Chan.stem] using valid
    have stepAccepted' : (({ name := "dma_response", depth := 4 } :
        Chan (HwPacked.width Response)).step
          (system.connectionQueue state dmaResponseConnection)
          (system.connectionEvent event state dmaResponseConnection)).accepted = true := by
      simpa [dmaResponse, PackedChan.named] using stepAccepted
    simp [fabricResponseAccepted, fabricResponsePending,
      systemDmaResponsesAcceptedAt, Chan.acceptedValues, stepAccepted',
      acceptedReg', stableValid', stablePayload', valid', pushEq,
      systemFabricState, dmaResponse, PackedChan.named, Chan.sourceAccepted,
      Chan.sourceAcceptedName, Chan.sourceValidName, Chan.sourcePayload,
      Chan.sourcePayloadName, Chan.stem, Expr.eval]
  · have acceptedFalse : result.accepted = false :=
      Bool.eq_false_of_not_eq_true accepted
    have acceptedValue : system.islandInput event state external "fabric"
        dmaResponse.bits.sourceAcceptedName 1 = 0#1 := by
      rw [inputAccepted, acceptedFalse]
      rfl
    have acceptedReg := acceptedPoked.trans acceptedValue
    have stepAccepted : (dmaResponse.bits.step
        (system.connectionQueue state dmaResponseConnection)
        (system.connectionEvent event state dmaResponseConnection)).accepted = false := by
      simpa [System.connectionResult, result, dmaResponseConnection] using
        acceptedFalse
    have acceptedReg' : ((state.island "fabric").setInputs fabric.inputs
        (system.islandInput event state external "fabric")).regs
        "__loom_chan_dma_response_src_accepted" 1 = 0#1 := by
      simpa [systemFabricState, dmaResponse, PackedChan.named,
        Chan.sourceAcceptedName, Chan.stem] using acceptedReg
    have stepAccepted' : (({ name := "dma_response", depth := 4 } :
        Chan (HwPacked.width Response)).step
          (system.connectionQueue state dmaResponseConnection)
          (system.connectionEvent event state dmaResponseConnection)).accepted = false := by
      simpa [dmaResponse, PackedChan.named] using stepAccepted
    simp [fabricResponseAccepted, systemDmaResponsesAcceptedAt,
      Chan.acceptedValues, stepAccepted', acceptedReg', systemFabricState,
      dmaResponse, PackedChan.named, Chan.sourceAccepted,
      Chan.sourceAcceptedName, Chan.stem, Expr.eval]

theorem system_cpuResponse_source_ledger_step (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    systemFabricResponsePending cpuResponse state ++
        systemFabricResponseProducedAt .cpu state event external =
      systemCpuResponsesAcceptedAt state event ++
        systemFabricResponsePending cpuResponse
          (system.advance event external state) := by
  by_cases ticks : event.fires "cpu_fabric_clk" = true
  · let input := system.islandInput event state external "fabric"
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have nextIsland := System.advance_island_ticked system event external state
      ⟨"fabric", "cpu_fabric_clk", fabric⟩ found ticks
    have acceptedLegal : cpuResponse.bits.sourceAccepted.eval
        ((systemFabricState state).setInputs fabric.inputs input) = 1#1 →
        (systemFabricState state).regs cpuResponse.bits.sourceValidName 1 = 1#1 := by
      intro acceptedInput
      have inputAccepted := fabricInput_cpuResponseAccepted state event external
      have acceptedPoked :
          ((systemFabricState state).setInputs fabric.inputs input).regs
              cpuResponse.bits.sourceAcceptedName 1 =
            system.islandInput event state external "fabric"
              cpuResponse.bits.sourceAcceptedName 1 := by rfl
      have acceptedEnv : system.islandInput event state external "fabric"
          cpuResponse.bits.sourceAcceptedName 1 = 1#1 := by
        calc
          _ = ((systemFabricState state).setInputs fabric.inputs input).regs
              cpuResponse.bits.sourceAcceptedName 1 := acceptedPoked.symm
          _ = 1#1 := acceptedInput
      have resultAccepted : (system.connectionResult event state
          cpuResponseConnection).accepted = true := by
        by_cases accepted : (system.connectionResult event state
            cpuResponseConnection).accepted = true
        · exact accepted
        · have acceptedFalse := Bool.eq_false_of_not_eq_true accepted
          rw [inputAccepted] at acceptedEnv
          simp [acceptedFalse] at acceptedEnv
      exact cpuResponse_accepted_implies_valid state event resultAccepted
    have localLedger := fabric_cycleOpen_cpu_response_ledger
      (systemFabricState state) input acceptedLegal
    rw [cpuResponse_fabricAccepted_eq state event external ticks] at localLedger
    simpa [systemFabricResponsePending, systemFabricResponseProducedAt,
      ticks, input, systemFabricState, nextIsland] using localLedger
  · have unticked : event.fires "cpu_fabric_clk" = false :=
      Bool.eq_false_of_not_eq_true ticks
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have nextIsland := System.advance_island_unticked system event external state
      ⟨"fabric", "cpu_fabric_clk", fabric⟩ found unticked
    have acceptedFalse : (system.connectionResult event state
        cpuResponseConnection).accepted = false := by
      simp [System.connectionResult, System.connectionEvent,
        cpuResponseConnection, found, unticked,
        cpuResponse, PackedChan.named, Chan.step]
    have stepAcceptedFalse : (cpuResponse.bits.step
        (system.connectionQueue state cpuResponseConnection)
        (system.connectionEvent event state cpuResponseConnection)).accepted = false := by
      simpa [System.connectionResult, cpuResponseConnection] using acceptedFalse
    simp [systemFabricResponsePending, systemFabricResponseProducedAt,
      ticks, systemCpuResponsesAcceptedAt, Chan.acceptedValues,
      acceptedFalse, stepAcceptedFalse, systemFabricState, nextIsland]

theorem system_dmaResponse_source_ledger_step (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    systemFabricResponsePending dmaResponse state ++
        systemFabricResponseProducedAt .dma state event external =
      systemDmaResponsesAcceptedAt state event ++
        systemFabricResponsePending dmaResponse
          (system.advance event external state) := by
  by_cases ticks : event.fires "cpu_fabric_clk" = true
  · let input := system.islandInput event state external "fabric"
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have nextIsland := System.advance_island_ticked system event external state
      ⟨"fabric", "cpu_fabric_clk", fabric⟩ found ticks
    have acceptedLegal : dmaResponse.bits.sourceAccepted.eval
        ((systemFabricState state).setInputs fabric.inputs input) = 1#1 →
        (systemFabricState state).regs dmaResponse.bits.sourceValidName 1 = 1#1 := by
      intro acceptedInput
      have inputAccepted := fabricInput_dmaResponseAccepted state event external
      have acceptedPoked :
          ((systemFabricState state).setInputs fabric.inputs input).regs
              dmaResponse.bits.sourceAcceptedName 1 =
            system.islandInput event state external "fabric"
              dmaResponse.bits.sourceAcceptedName 1 := by rfl
      have acceptedEnv : system.islandInput event state external "fabric"
          dmaResponse.bits.sourceAcceptedName 1 = 1#1 := by
        calc
          _ = ((systemFabricState state).setInputs fabric.inputs input).regs
              dmaResponse.bits.sourceAcceptedName 1 := acceptedPoked.symm
          _ = 1#1 := acceptedInput
      have resultAccepted : (system.connectionResult event state
          dmaResponseConnection).accepted = true := by
        by_cases accepted : (system.connectionResult event state
            dmaResponseConnection).accepted = true
        · exact accepted
        · have acceptedFalse := Bool.eq_false_of_not_eq_true accepted
          rw [inputAccepted] at acceptedEnv
          simp [acceptedFalse] at acceptedEnv
      exact dmaResponse_accepted_implies_valid state event resultAccepted
    have localLedger := fabric_cycleOpen_dma_response_ledger
      (systemFabricState state) input acceptedLegal
    rw [dmaResponse_fabricAccepted_eq state event external ticks] at localLedger
    simpa [systemFabricResponsePending, systemFabricResponseProducedAt,
      ticks, input, systemFabricState, nextIsland] using localLedger
  · have unticked : event.fires "cpu_fabric_clk" = false :=
      Bool.eq_false_of_not_eq_true ticks
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have nextIsland := System.advance_island_unticked system event external state
      ⟨"fabric", "cpu_fabric_clk", fabric⟩ found unticked
    have acceptedFalse : (system.connectionResult event state
        dmaResponseConnection).accepted = false := by
      simp [System.connectionResult, System.connectionEvent,
        dmaResponseConnection, found, unticked,
        dmaResponse, PackedChan.named, Chan.step]
    have stepAcceptedFalse : (dmaResponse.bits.step
        (system.connectionQueue state dmaResponseConnection)
        (system.connectionEvent event state dmaResponseConnection)).accepted = false := by
      simpa [System.connectionResult, dmaResponseConnection] using acceptedFalse
    simp [systemFabricResponsePending, systemFabricResponseProducedAt,
      ticks, systemDmaResponsesAcceptedAt, Chan.acceptedValues,
      acceptedFalse, stepAcceptedFalse, systemFabricState, nextIsland]

def systemFabricResponseTraceFrom (client : FabricResponseRoute)
    (inputs : ExternalInputs) : system.State → List NamedClockEvent → List Response
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemFabricResponseProducedAt client state event external ++
        systemFabricResponseTraceFrom client inputs
          (system.advance event external state) rest

theorem systemFabricRoutedResponseObservationsAt_select
    (route : FabricResponseRoute) (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    selectClientValues (responseRouteClient route)
        (systemFabricRoutedResponseObservationsAt state event external) =
      systemFabricResponseProducedAt route state event external := by
  by_cases ticks : event.fires "cpu_fabric_clk" = true
  · simp only [systemFabricRoutedResponseObservationsAt,
      systemFabricResponseProducedAt, ticks, if_true]
    let poked := (systemFabricState state).setInputs fabric.inputs
      (system.islandInput event state external "fabric")
    cases choice : fabricResponseRouteChoice poked with
    | none =>
        simp [fabricRoutedResponseObservations, fabricResponseProduced,
          selectClientValues, choice, poked]
    | some selected =>
        cases selected <;> cases route <;>
          simp [fabricRoutedResponseObservations, fabricResponseProduced,
            selectClientValues, responseRouteClient, choice, poked]
  · simp [systemFabricRoutedResponseObservationsAt,
      systemFabricResponseProducedAt, ticks, selectClientValues]

theorem systemFabricRoutedResponseObservationTrace_select
    (route : FabricResponseRoute) (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    selectClientValues (responseRouteClient route)
        (systemFabricRoutedResponseObservationTraceFrom inputs state events) =
      systemFabricResponseTraceFrom route inputs state events := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemFabricRoutedResponseObservationTraceFrom,
        systemFabricResponseTraceFrom, selectClientValues,
        List.filterMap_append]
      change selectClientValues (responseRouteClient route)
          (systemFabricRoutedResponseObservationsAt state event
            (inputs state.time)) ++
          selectClientValues (responseRouteClient route)
            (systemFabricRoutedResponseObservationTraceFrom inputs
              (system.advance event (inputs state.time) state) rest) = _
      rw [systemFabricRoutedResponseObservationsAt_select, ih]

def systemCpuResponseAcceptedTraceFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List Response
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemCpuResponsesAcceptedAt state event ++
        systemCpuResponseAcceptedTraceFrom inputs
          (system.advance event external state) rest

def systemDmaResponseAcceptedTraceFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List Response
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemDmaResponsesAcceptedAt state event ++
        systemDmaResponseAcceptedTraceFrom inputs
          (system.advance event external state) rest

theorem system_cpuResponse_source_ledger (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemFabricResponsePending cpuResponse state ++
        systemFabricResponseTraceFrom .cpu inputs state events =
      systemCpuResponseAcceptedTraceFrom inputs state events ++
        systemFabricResponsePending cpuResponse
          (system.runEventsFrom inputs state events) := by
  induction events generalizing state with
  | nil => simp [systemFabricResponseTraceFrom,
      systemCpuResponseAcceptedTraceFrom, System.runEventsFrom]
  | cons event rest ih =>
      simp only [systemFabricResponseTraceFrom,
        systemCpuResponseAcceptedTraceFrom, System.runEventsFrom]
      let external := inputs state.time
      let next := system.advance event external state
      rw [← List.append_assoc,
        system_cpuResponse_source_ledger_step state event external]
      simpa only [List.append_assoc] using
        congrArg (fun values => systemCpuResponsesAcceptedAt state event ++ values)
          (ih next)

theorem system_dmaResponse_source_ledger (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemFabricResponsePending dmaResponse state ++
        systemFabricResponseTraceFrom .dma inputs state events =
      systemDmaResponseAcceptedTraceFrom inputs state events ++
        systemFabricResponsePending dmaResponse
          (system.runEventsFrom inputs state events) := by
  induction events generalizing state with
  | nil => simp [systemFabricResponseTraceFrom,
      systemDmaResponseAcceptedTraceFrom, System.runEventsFrom]
  | cons event rest ih =>
      simp only [systemFabricResponseTraceFrom,
        systemDmaResponseAcceptedTraceFrom, System.runEventsFrom]
      let external := inputs state.time
      let next := system.advance event external state
      rw [← List.append_assoc,
        system_dmaResponse_source_ledger_step state event external]
      simpa only [List.append_assoc] using
        congrArg (fun values => systemDmaResponsesAcceptedAt state event ++ values)
          (ih next)

@[simp] theorem systemFabricCpuResponsePending_reset :
    systemFabricResponsePending cpuResponse system.reset = [] := by rfl

@[simp] theorem systemFabricDmaResponsePending_reset :
    systemFabricResponsePending dmaResponse system.reset = [] := by rfl

theorem systemCpuResponseAcceptedTrace_eq_fifo (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemCpuResponseAcceptedTraceFrom inputs state events =
      (cpuResponse.bits.runTrace
        (system.channelState state cpuResponseConnection)
        (system.channelEventsFrom inputs cpuResponseConnection state events)).accepted.map
          HwPacked.unpack := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemCpuResponseAcceptedTraceFrom,
        System.channelEventsFrom, Chan.runTrace, List.map_append]
      let external := inputs state.time
      let next := system.advance event external state
      change systemCpuResponsesAcceptedAt state event ++
          systemCpuResponseAcceptedTraceFrom inputs next rest = _
      rw [ih next]
      rw [System.channelState_advance system event external state
        cpuResponseConnection (by rfl)]
      rfl

theorem systemDmaResponseAcceptedTrace_eq_fifo (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemDmaResponseAcceptedTraceFrom inputs state events =
      (dmaResponse.bits.runTrace
        (system.channelState state dmaResponseConnection)
        (system.channelEventsFrom inputs dmaResponseConnection state events)).accepted.map
          HwPacked.unpack := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemDmaResponseAcceptedTraceFrom,
        System.channelEventsFrom, Chan.runTrace, List.map_append]
      let external := inputs state.time
      let next := system.advance event external state
      change systemDmaResponsesAcceptedAt state event ++
          systemDmaResponseAcceptedTraceFrom inputs next rest = _
      rw [ih next]
      rw [System.channelState_advance system event external state
        dmaResponseConnection (by rfl)]
      rfl

theorem system_targetRequest_source_ledger_step (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    systemFabricTargetRequestPending state ++
        systemFabricTargetRequestsProducedAt state event external =
      systemTargetRequestsAcceptedAt state event ++
        systemFabricTargetRequestPending
          (system.advance event external state) := by
  by_cases ticks : event.fires "cpu_fabric_clk" = true
  · let input := system.islandInput event state external "fabric"
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have nextIsland := System.advance_island_ticked system event external state
      ⟨"fabric", "cpu_fabric_clk", fabric⟩ found ticks
    have acceptedLegal : targetRequest.bits.sourceAccepted.eval
        ((systemFabricState state).setInputs fabric.inputs input) = 1#1 →
        (systemFabricState state).regs
          targetRequest.bits.sourceValidName 1 = 1#1 := by
      intro acceptedInput
      have inputAccepted := fabricInput_targetRequestAccepted state event external
      have acceptedPoked :
          ((systemFabricState state).setInputs fabric.inputs input).regs
              targetRequest.bits.sourceAcceptedName 1 =
            system.islandInput event state external "fabric"
              targetRequest.bits.sourceAcceptedName 1 := by rfl
      have acceptedEnv : system.islandInput event state external "fabric"
          targetRequest.bits.sourceAcceptedName 1 = 1#1 := by
        calc
          _ = ((systemFabricState state).setInputs fabric.inputs input).regs
              targetRequest.bits.sourceAcceptedName 1 := acceptedPoked.symm
          _ = 1#1 := acceptedInput
      have resultAccepted : (system.connectionResult event state
          targetRequestConnection).accepted = true := by
        by_cases accepted : (system.connectionResult event state
            targetRequestConnection).accepted = true
        · exact accepted
        · have acceptedFalse := Bool.eq_false_of_not_eq_true accepted
          rw [inputAccepted] at acceptedEnv
          simp [acceptedFalse] at acceptedEnv
      exact targetRequest_accepted_implies_valid state event resultAccepted
    have localLedger := fabric_cycleOpen_target_request_ledger
      (systemFabricState state) input acceptedLegal
    rw [targetRequest_fabricAccepted_eq state event external ticks] at localLedger
    simpa [systemFabricTargetRequestPending,
      systemFabricTargetRequestsProducedAt, ticks, input, systemFabricState,
      nextIsland] using localLedger
  · have unticked : event.fires "cpu_fabric_clk" = false :=
      Bool.eq_false_of_not_eq_true ticks
    have found : system.findIsland? "fabric" =
        some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
    have nextIsland := System.advance_island_unticked system event external state
      ⟨"fabric", "cpu_fabric_clk", fabric⟩ found unticked
    have acceptedFalse : (system.connectionResult event state
        targetRequestConnection).accepted = false := by
      simp [System.connectionResult, System.connectionEvent,
        targetRequestConnection, found, unticked,
        targetRequest, PackedChan.named, Chan.step]
    have stepAcceptedFalse : (targetRequest.bits.step
        (system.connectionQueue state targetRequestConnection)
        (system.connectionEvent event state targetRequestConnection)).accepted = false := by
      simpa [System.connectionResult, targetRequestConnection] using acceptedFalse
    simp [systemFabricTargetRequestPending,
      systemFabricTargetRequestsProducedAt, ticks,
      systemTargetRequestsAcceptedAt, Chan.acceptedValues,
      acceptedFalse, stepAcceptedFalse, systemFabricState, nextIsland]

def systemFabricTargetRequestTraceFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List Request
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemFabricTargetRequestsProducedAt state event external ++
        systemFabricTargetRequestTraceFrom inputs
          (system.advance event external state) rest

def systemTargetRequestAcceptedTraceFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List Request
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemTargetRequestsAcceptedAt state event ++
        systemTargetRequestAcceptedTraceFrom inputs
          (system.advance event external state) rest

theorem systemFabricGrantObservationTrace_requests (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    (systemFabricGrantObservationTraceFrom inputs state events).map Prod.snd =
      systemFabricTargetRequestTraceFrom inputs state events := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemFabricGrantObservationTraceFrom,
        systemFabricTargetRequestTraceFrom, List.map_append]
      rw [systemFabricGrantObservationsAt_requests, ih]

theorem system_targetRequest_source_ledger (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemFabricTargetRequestPending state ++
        systemFabricTargetRequestTraceFrom inputs state events =
      systemTargetRequestAcceptedTraceFrom inputs state events ++
        systemFabricTargetRequestPending
          (system.runEventsFrom inputs state events) := by
  induction events generalizing state with
  | nil => simp [systemFabricTargetRequestTraceFrom,
      systemTargetRequestAcceptedTraceFrom, System.runEventsFrom]
  | cons event rest ih =>
      simp only [systemFabricTargetRequestTraceFrom,
        systemTargetRequestAcceptedTraceFrom, System.runEventsFrom]
      let external := inputs state.time
      let next := system.advance event external state
      rw [← List.append_assoc,
        system_targetRequest_source_ledger_step state event external]
      simpa only [List.append_assoc] using
        congrArg (fun values => systemTargetRequestsAcceptedAt state event ++ values)
          (ih next)

@[simp] theorem systemFabricTargetRequestPending_reset :
    systemFabricTargetRequestPending system.reset = [] := by rfl

theorem systemTargetRequestAcceptedTrace_eq_fifo (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemTargetRequestAcceptedTraceFrom inputs state events =
      (targetRequest.bits.runTrace
        (system.channelState state targetRequestConnection)
        (system.channelEventsFrom inputs targetRequestConnection state events)).accepted.map
          HwPacked.unpack := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemTargetRequestAcceptedTraceFrom,
        System.channelEventsFrom, Chan.runTrace, List.map_append]
      let external := inputs state.time
      let next := system.advance event external state
      change systemTargetRequestsAcceptedAt state event ++
          systemTargetRequestAcceptedTraceFrom inputs next rest = _
      rw [ih next]
      rw [System.channelState_advance system event external state
        targetRequestConnection (by rfl)]
      rfl

private theorem targetResponse_serviceAccepted_eq (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (ticks : event.fires "mem_clk" = true) :
    serviceResponseAccepted ((systemServiceState state).setInputs service.inputs
      (system.islandInput event state external "service")) =
      systemTargetResponsesAcceptedAt state event := by
  let result := system.connectionResult event state targetResponseConnection
  have inputAccepted := serviceInput_targetResponseAccepted state event external
  by_cases accepted : result.accepted = true
  · have valid := targetResponse_accepted_implies_valid state event accepted
    have found : system.findIsland? "service" =
        some ⟨"service", "mem_clk", service⟩ := by rfl
    have valid' : (state.island "service").regs
        "__loom_chan_target_response_src_valid" 1 = 1#1 := by
      simpa [targetResponse, PackedChan.named, Chan.sourceValidName,
        Chan.stem] using valid
    have nonzero : (state.island "service").regs
        "__loom_chan_target_response_src_valid" 1 ≠ 0#1 := by bv_omega
    have pushEq : (system.connectionEvent event state targetResponseConnection).push =
        some (targetResponse.bits.sourcePayload.eval (state.island "service")) := by
      simp [System.connectionEvent, targetResponseConnection, found, ticks,
        targetResponse, PackedChan.named, Chan.sourceValid, Chan.sourcePayload,
        Chan.sourceValidName, Chan.sourcePayloadName, Chan.stem, Expr.eval]
      exact nonzero
    have endpointStable := service_response_endpoint_not_input
      (systemServiceState state)
      (system.islandInput event state external "service")
    rcases endpointStable with ⟨stableValid, stablePayload⟩
    have acceptedPoked :
        ((systemServiceState state).setInputs service.inputs
          (system.islandInput event state external "service")).regs
            targetResponse.bits.sourceAcceptedName 1 =
        system.islandInput event state external "service"
          targetResponse.bits.sourceAcceptedName 1 := by rfl
    have stepAccepted : (targetResponse.bits.step
        (system.connectionQueue state targetResponseConnection)
        (system.connectionEvent event state targetResponseConnection)).accepted = true := by
      simpa [System.connectionResult, result, targetResponseConnection] using accepted
    have stepAccepted' : (({ name := "target_response", depth := 4 } :
        Chan (HwPacked.width Response)).step
          (system.connectionQueue state targetResponseConnection)
          (system.connectionEvent event state targetResponseConnection)).accepted = true := by
      simpa [targetResponse, PackedChan.named] using stepAccepted
    have acceptedInputValue : system.islandInput event state external "service"
        targetResponse.bits.sourceAcceptedName 1 = 1#1 := by
      rw [inputAccepted, accepted]
      rfl
    have acceptedReg :
        ((state.island "service").setInputs service.inputs
          (system.islandInput event state external "service")).regs
            "__loom_chan_target_response_src_accepted" 1 = 1#1 := by
      have := acceptedPoked.trans acceptedInputValue
      simpa [systemServiceState, targetResponse, PackedChan.named,
        Chan.sourceAcceptedName, Chan.stem] using this
    have stableValid' :
        ((state.island "service").setInputs service.inputs
          (system.islandInput event state external "service")).regs
            "__loom_chan_target_response_src_valid" 1 =
          (state.island "service").regs
            "__loom_chan_target_response_src_valid" 1 := by
      simpa [systemServiceState, targetResponse, PackedChan.named,
        Chan.sourceValidName, Chan.stem] using stableValid
    have stablePayload' :
        ((state.island "service").setInputs service.inputs
          (system.islandInput event state external "service")).regs
            "__loom_chan_target_response_src_payload" (HwPacked.width Response) =
          (state.island "service").regs
            "__loom_chan_target_response_src_payload" (HwPacked.width Response) := by
      simpa [systemServiceState, targetResponse, PackedChan.named,
        Chan.sourcePayloadName, Chan.stem] using stablePayload
    simp [serviceResponseAccepted, serviceResponsePending,
      systemTargetResponsesAcceptedAt, Chan.acceptedValues, stepAccepted',
      acceptedReg, stableValid', stablePayload', valid', pushEq,
      systemServiceState, targetResponse, PackedChan.named,
      Chan.sourceAccepted, Chan.sourceAcceptedName, Chan.sourceValidName,
      Chan.sourcePayload, Chan.sourcePayloadName, Chan.stem, Expr.eval]
  · have acceptedFalse : result.accepted = false := Bool.eq_false_of_not_eq_true accepted
    have acceptedPoked :
        ((systemServiceState state).setInputs service.inputs
          (system.islandInput event state external "service")).regs
            targetResponse.bits.sourceAcceptedName 1 =
        system.islandInput event state external "service"
          targetResponse.bits.sourceAcceptedName 1 := by rfl
    have stepAccepted : (targetResponse.bits.step
        (system.connectionQueue state targetResponseConnection)
        (system.connectionEvent event state targetResponseConnection)).accepted = false := by
      simpa [System.connectionResult, result, targetResponseConnection] using
        acceptedFalse
    have stepAccepted' : (({ name := "target_response", depth := 4 } :
        Chan (HwPacked.width Response)).step
          (system.connectionQueue state targetResponseConnection)
          (system.connectionEvent event state targetResponseConnection)).accepted = false := by
      simpa [targetResponse, PackedChan.named] using stepAccepted
    have acceptedInputValue : system.islandInput event state external "service"
        targetResponse.bits.sourceAcceptedName 1 = 0#1 := by
      rw [inputAccepted, acceptedFalse]
      rfl
    have acceptedReg :
        ((state.island "service").setInputs service.inputs
          (system.islandInput event state external "service")).regs
            "__loom_chan_target_response_src_accepted" 1 = 0#1 := by
      have := acceptedPoked.trans acceptedInputValue
      simpa [systemServiceState, targetResponse, PackedChan.named,
        Chan.sourceAcceptedName, Chan.stem] using this
    simp [serviceResponseAccepted, systemTargetResponsesAcceptedAt,
      Chan.acceptedValues, stepAccepted', acceptedReg, systemServiceState,
      targetResponse, PackedChan.named,
      Chan.sourceAccepted, Chan.sourceAcceptedName, Chan.stem, Expr.eval]

theorem system_targetResponse_source_ledger_step (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    systemServiceResponsePending state ++
        systemServiceResponsesProducedAt state event external =
      systemTargetResponsesAcceptedAt state event ++
        systemServiceResponsePending (system.advance event external state) := by
  by_cases ticks : event.fires "mem_clk" = true
  · let input := system.islandInput event state external "service"
    have found : system.findIsland? "service" =
        some ⟨"service", "mem_clk", service⟩ := by rfl
    have nextIsland := System.advance_island_ticked system event external state
      ⟨"service", "mem_clk", service⟩ found ticks
    have acceptedLegal : targetResponse.bits.sourceAccepted.eval
        ((systemServiceState state).setInputs service.inputs input) = 1#1 →
        (systemServiceState state).regs
          targetResponse.bits.sourceValidName 1 = 1#1 := by
      intro acceptedInput
      have inputAccepted := serviceInput_targetResponseAccepted state event external
      have acceptedPoked :
          ((systemServiceState state).setInputs service.inputs input).regs
              targetResponse.bits.sourceAcceptedName 1 =
            system.islandInput event state external "service"
              targetResponse.bits.sourceAcceptedName 1 := by rfl
      have acceptedEnv : system.islandInput event state external "service"
          targetResponse.bits.sourceAcceptedName 1 = 1#1 := by
        calc
          _ = ((systemServiceState state).setInputs service.inputs input).regs
              targetResponse.bits.sourceAcceptedName 1 := acceptedPoked.symm
          _ = 1#1 := acceptedInput
      have resultAccepted : (system.connectionResult event state
          targetResponseConnection).accepted = true := by
        by_cases accepted : (system.connectionResult event state
            targetResponseConnection).accepted = true
        · exact accepted
        · have acceptedFalse := Bool.eq_false_of_not_eq_true accepted
          rw [inputAccepted] at acceptedEnv
          simp [acceptedFalse] at acceptedEnv
      exact targetResponse_accepted_implies_valid state event resultAccepted
    have localLedger := service_cycleOpen_response_ledger
      (systemServiceState state) input acceptedLegal
    rw [targetResponse_serviceAccepted_eq state event external ticks] at localLedger
    simpa [systemServiceResponsePending, systemServiceResponsesProducedAt,
      ticks, input, systemServiceState, nextIsland] using localLedger
  · have unticked : event.fires "mem_clk" = false :=
      Bool.eq_false_of_not_eq_true ticks
    have found : system.findIsland? "service" =
        some ⟨"service", "mem_clk", service⟩ := by rfl
    have nextIsland := System.advance_island_unticked system event external state
      ⟨"service", "mem_clk", service⟩ found unticked
    have acceptedFalse : (system.connectionResult event state
        targetResponseConnection).accepted = false := by
      simp [System.connectionResult, System.connectionEvent,
        targetResponseConnection, found, unticked,
        targetResponse, PackedChan.named, Chan.step]
    have stepAcceptedFalse : (targetResponse.bits.step
        (system.connectionQueue state targetResponseConnection)
        (system.connectionEvent event state targetResponseConnection)).accepted = false := by
      simpa [System.connectionResult, targetResponseConnection] using acceptedFalse
    simp [systemServiceResponsePending, systemServiceResponsesProducedAt,
      ticks, systemTargetResponsesAcceptedAt, Chan.acceptedValues,
      System.connectionResult, acceptedFalse, stepAcceptedFalse,
      systemServiceState, nextIsland]

def systemServiceResponseTraceFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List Response
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemServiceResponsesProducedAt state event external ++
        systemServiceResponseTraceFrom inputs
          (system.advance event external state) rest

def systemTargetResponseAcceptedTraceFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List Response
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemTargetResponsesAcceptedAt state event ++
        systemTargetResponseAcceptedTraceFrom inputs
          (system.advance event external state) rest

/-- Finite-prefix endpoint conservation across an arbitrary named-clock
schedule.  The suffix is the literal source endpoint state at the cut. -/
theorem system_targetResponse_source_ledger (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemServiceResponsePending state ++
        systemServiceResponseTraceFrom inputs state events =
      systemTargetResponseAcceptedTraceFrom inputs state events ++
        systemServiceResponsePending
          (system.runEventsFrom inputs state events) := by
  induction events generalizing state with
  | nil => simp [systemServiceResponseTraceFrom,
      systemTargetResponseAcceptedTraceFrom, System.runEventsFrom]
  | cons event rest ih =>
      simp only [systemServiceResponseTraceFrom,
        systemTargetResponseAcceptedTraceFrom, System.runEventsFrom]
      let external := inputs state.time
      let next := system.advance event external state
      rw [← List.append_assoc,
        system_targetResponse_source_ledger_step state event external]
      simpa only [List.append_assoc] using
        congrArg (fun values => systemTargetResponsesAcceptedAt state event ++ values)
          (ih next)

theorem systemTargetResponseAcceptedTrace_eq_fifo (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemTargetResponseAcceptedTraceFrom inputs state events =
      (targetResponse.bits.runTrace
        (system.channelState state targetResponseConnection)
        (system.channelEventsFrom inputs targetResponseConnection state events)).accepted.map
          HwPacked.unpack := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemTargetResponseAcceptedTraceFrom,
        System.channelEventsFrom, Chan.runTrace, List.map_append]
      let external := inputs state.time
      let next := system.advance event external state
      change systemTargetResponsesAcceptedAt state event ++
          systemTargetResponseAcceptedTraceFrom inputs next rest = _
      rw [ih next]
      rw [System.channelState_advance system event external state
        targetResponseConnection (by rfl)]
      rfl

theorem systemServiceResponsesProducedAt_eq_commitObservation
    (state : system.State) (event : NamedClockEvent)
    (external : String → InEnv) :
    systemServiceResponsesProducedAt state event external =
      match systemServiceCommitRequest? state event external with
      | some _ =>
          [HwPacked.unpack (((system.advance event external state).island
            "service").regs targetResponse.bits.sourcePayloadName
              (HwPacked.width Response))]
      | none => [] := by
  by_cases ticks : event.fires "mem_clk" = true
  · let poked := (systemServiceState state).setInputs service.inputs
      (system.islandInput event state external "service")
    by_cases enabled : targetRequest.bits.canDeq.eval poked = 1#1 ∧
        targetResponse.bits.canEnq.eval poked = 1#1 ∧
        audit.bits.canEnq.eval poked = 1#1
    · rcases enabled with ⟨requestReady, responseReady, auditReady⟩
      have emitted := system_advance_service_emits_response state event external
        ticks requestReady responseReady auditReady
      simp only [systemServiceResponsesProducedAt, ticks, if_true,
        systemServiceCommitRequest?, serviceResponseProduced,
        PackedChan.canDeq, PackedChan.canEnq]
      rw [if_pos ⟨requestReady, responseReady, auditReady⟩,
        if_pos ⟨requestReady, responseReady, auditReady⟩]
      exact congrArg List.singleton emitted.symm
    · simp [systemServiceResponsesProducedAt, systemServiceCommitRequest?,
        serviceResponseProduced, PackedChan.canDeq, PackedChan.canEnq,
        ticks, poked, enabled]
  · simp [systemServiceResponsesProducedAt, systemServiceCommitRequest?, ticks]

theorem systemServiceResponseTrace_eq_history (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemServiceResponseTraceFrom inputs state events =
      (systemServiceCommitHistoryFrom inputs state events).responses := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemServiceResponseTraceFrom,
        systemServiceCommitHistoryFrom]
      let external := inputs state.time
      let next := system.advance event external state
      rw [systemServiceResponsesProducedAt_eq_commitObservation
        state event external]
      cases committed : systemServiceCommitRequest? state event external with
      | none =>
          simp only
          exact ih next
      | some request =>
          simp only [List.singleton_append]
          exact congrArg (List.cons (HwPacked.unpack
            ((next.island "service").regs
              targetResponse.bits.sourcePayloadName
                (HwPacked.width Response)))) (ih next)

@[simp] theorem systemServiceResponsePending_reset :
    systemServiceResponsePending system.reset = [] := by rfl

private theorem audit_accepted_implies_valid (state : system.State)
    (event : NamedClockEvent)
    (accepted : (system.connectionResult event state
      auditConnection).accepted = true) :
    (state.island "service").regs audit.bits.sourceValidName 1 = 1#1 := by
  have pushed := chan_accepted_implies_push audit.bits
    (system.connectionQueue state auditConnection)
    (system.connectionEvent event state auditConnection) accepted
  simp [System.connectionEvent, system, connectionInventory,
    auditConnection] at pushed
  have nonzero : (state.island "service").regs
      audit.bits.sourceValidName 1 ≠ 0#1 := by
    simpa [audit, PackedChan.named, Chan.sourceValid,
      Chan.sourceValidName, Chan.stem, Expr.eval] using pushed.2
  bv_omega

def systemServiceAuditPending (state : system.State) : List CommitRecord :=
  serviceAuditPending (systemServiceState state)

def systemServiceAuditProducedAt (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) : List CommitRecord :=
  if event.fires "mem_clk" = true then
    serviceAuditProduced ((systemServiceState state).setInputs service.inputs
      (system.islandInput event state external "service"))
  else []

def systemAuditAcceptedAt (state : system.State)
    (event : NamedClockEvent) : List CommitRecord :=
  (audit.bits.acceptedValues
    (system.connectionQueue state auditConnection)
    (system.connectionEvent event state auditConnection)).map HwPacked.unpack

private theorem audit_serviceAccepted_eq (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv)
    (ticks : event.fires "mem_clk" = true) :
    serviceAuditAccepted ((systemServiceState state).setInputs service.inputs
      (system.islandInput event state external "service")) =
      systemAuditAcceptedAt state event := by
  let result := system.connectionResult event state auditConnection
  have inputAccepted := serviceInput_auditAccepted state event external
  by_cases accepted : result.accepted = true
  · have valid := audit_accepted_implies_valid state event accepted
    have found : system.findIsland? "service" =
        some ⟨"service", "mem_clk", service⟩ := by rfl
    have valid' : (state.island "service").regs
        "__loom_chan_audit_src_valid" 1 = 1#1 := by
      simpa [audit, PackedChan.named, Chan.sourceValidName, Chan.stem] using valid
    have nonzero : (state.island "service").regs
        "__loom_chan_audit_src_valid" 1 ≠ 0#1 := by bv_omega
    have pushEq : (system.connectionEvent event state auditConnection).push =
        some (audit.bits.sourcePayload.eval (state.island "service")) := by
      simp [System.connectionEvent, auditConnection, found, ticks, valid,
        audit, PackedChan.named,
        Chan.sourceValid, Chan.sourcePayload, Chan.sourceValidName,
        Chan.sourcePayloadName, Chan.stem, Expr.eval]
      exact nonzero
    have endpointStable := service_audit_endpoint_not_input
      (systemServiceState state)
      (system.islandInput event state external "service")
    rcases endpointStable with ⟨stableValid, stablePayload⟩
    have acceptedPoked :
        ((systemServiceState state).setInputs service.inputs
          (system.islandInput event state external "service")).regs
            audit.bits.sourceAcceptedName 1 =
        system.islandInput event state external "service"
          audit.bits.sourceAcceptedName 1 := by rfl
    have stepAccepted : (audit.bits.step
        (system.connectionQueue state auditConnection)
        (system.connectionEvent event state auditConnection)).accepted = true := by
      simpa [System.connectionResult, result, auditConnection] using accepted
    have stepAccepted' : (({ name := "audit", depth := 4 } :
        Chan (HwPacked.width CommitRecord)).step
          (system.connectionQueue state auditConnection)
          (system.connectionEvent event state auditConnection)).accepted = true := by
      simpa [audit, PackedChan.named] using stepAccepted
    have acceptedInputValue : system.islandInput event state external "service"
        audit.bits.sourceAcceptedName 1 = 1#1 := by
      rw [inputAccepted]
      rw [accepted]
      rfl
    have acceptedReg :
        ((state.island "service").setInputs service.inputs
          (system.islandInput event state external "service")).regs
            audit.bits.sourceAcceptedName 1 = 1#1 := by
      simpa [systemServiceState] using acceptedPoked.trans acceptedInputValue
    have stableValid' :
        ((state.island "service").setInputs service.inputs
          (system.islandInput event state external "service")).regs
            audit.bits.sourceValidName 1 =
          (state.island "service").regs audit.bits.sourceValidName 1 := by
      simpa [systemServiceState] using stableValid
    have stablePayload' :
        ((state.island "service").setInputs service.inputs
          (system.islandInput event state external "service")).regs
            audit.bits.sourcePayloadName (HwPacked.width CommitRecord) =
          (state.island "service").regs audit.bits.sourcePayloadName
            (HwPacked.width CommitRecord) := by
      simpa [systemServiceState] using stablePayload
    have acceptedReg' :
        ((state.island "service").setInputs service.inputs
          (system.islandInput event state external "service")).regs
            "__loom_chan_audit_src_accepted" 1 = 1#1 := by
      simpa [audit, PackedChan.named, Chan.sourceAcceptedName, Chan.stem] using
        acceptedReg
    have stableValid'' :
        ((state.island "service").setInputs service.inputs
          (system.islandInput event state external "service")).regs
            "__loom_chan_audit_src_valid" 1 =
          (state.island "service").regs "__loom_chan_audit_src_valid" 1 := by
      simpa [audit, PackedChan.named, Chan.sourceValidName, Chan.stem] using
        stableValid'
    have stablePayload'' :
        ((state.island "service").setInputs service.inputs
          (system.islandInput event state external "service")).regs
            "__loom_chan_audit_src_payload" (HwPacked.width CommitRecord) =
          (state.island "service").regs "__loom_chan_audit_src_payload"
            (HwPacked.width CommitRecord) := by
      simpa [audit, PackedChan.named, Chan.sourcePayloadName, Chan.stem] using
        stablePayload'
    simp [serviceAuditAccepted, serviceAuditPending, systemAuditAcceptedAt,
      Chan.acceptedValues, System.connectionResult, result, stepAccepted',
      acceptedReg', stableValid'', stablePayload'', valid', pushEq,
      systemServiceState, audit,
      PackedChan.named, Chan.sourceAccepted, Chan.sourceAcceptedName,
      Chan.sourceValidName, Chan.sourcePayload, Chan.sourcePayloadName,
      Chan.stem, Expr.eval]
  · have acceptedFalse : result.accepted = false :=
      Bool.eq_false_of_not_eq_true accepted
    have acceptedPoked :
        ((systemServiceState state).setInputs service.inputs
          (system.islandInput event state external "service")).regs
            audit.bits.sourceAcceptedName 1 =
        system.islandInput event state external "service"
          audit.bits.sourceAcceptedName 1 := by rfl
    have stepAccepted : (audit.bits.step
        (system.connectionQueue state auditConnection)
        (system.connectionEvent event state auditConnection)).accepted = false := by
      simpa [System.connectionResult, result, auditConnection] using acceptedFalse
    have stepAccepted' : (({ name := "audit", depth := 4 } :
        Chan (HwPacked.width CommitRecord)).step
          (system.connectionQueue state auditConnection)
          (system.connectionEvent event state auditConnection)).accepted = false := by
      simpa [audit, PackedChan.named] using stepAccepted
    have acceptedInputValue : system.islandInput event state external "service"
        audit.bits.sourceAcceptedName 1 = 0#1 := by
      rw [inputAccepted]
      rw [acceptedFalse]
      rfl
    have acceptedReg :
        ((state.island "service").setInputs service.inputs
          (system.islandInput event state external "service")).regs
            audit.bits.sourceAcceptedName 1 = 0#1 := by
      simpa [systemServiceState] using acceptedPoked.trans acceptedInputValue
    have acceptedReg' :
        ((state.island "service").setInputs service.inputs
          (system.islandInput event state external "service")).regs
            "__loom_chan_audit_src_accepted" 1 = 0#1 := by
      simpa [audit, PackedChan.named, Chan.sourceAcceptedName, Chan.stem] using
        acceptedReg
    simp [serviceAuditAccepted, systemAuditAcceptedAt, Chan.acceptedValues,
      System.connectionResult, result, stepAccepted', acceptedReg',
      systemServiceState, audit, PackedChan.named, Chan.sourceAccepted,
      Chan.sourceAcceptedName, Chan.stem, Expr.eval]

theorem system_audit_source_ledger_step (state : system.State)
    (event : NamedClockEvent) (external : String → InEnv) :
    systemServiceAuditPending state ++
        systemServiceAuditProducedAt state event external =
      systemAuditAcceptedAt state event ++
        systemServiceAuditPending (system.advance event external state) := by
  by_cases ticks : event.fires "mem_clk" = true
  · let input := system.islandInput event state external "service"
    have found : system.findIsland? "service" =
        some ⟨"service", "mem_clk", service⟩ := by rfl
    have nextIsland := System.advance_island_ticked system event external state
      ⟨"service", "mem_clk", service⟩ found ticks
    have acceptedLegal : audit.bits.sourceAccepted.eval
        ((systemServiceState state).setInputs service.inputs input) = 1#1 →
        (systemServiceState state).regs audit.bits.sourceValidName 1 = 1#1 := by
      intro acceptedInput
      have inputAccepted := serviceInput_auditAccepted state event external
      have acceptedPoked :
          ((systemServiceState state).setInputs service.inputs input).regs
              audit.bits.sourceAcceptedName 1 =
            system.islandInput event state external "service"
              audit.bits.sourceAcceptedName 1 := by rfl
      have acceptedEnv : system.islandInput event state external "service"
          audit.bits.sourceAcceptedName 1 = 1#1 := by
        calc
          _ = ((systemServiceState state).setInputs service.inputs input).regs
              audit.bits.sourceAcceptedName 1 := acceptedPoked.symm
          _ = 1#1 := acceptedInput
      have resultAccepted : (system.connectionResult event state
          auditConnection).accepted = true := by
        by_cases accepted : (system.connectionResult event state
            auditConnection).accepted = true
        · exact accepted
        · have acceptedFalse := Bool.eq_false_of_not_eq_true accepted
          rw [inputAccepted] at acceptedEnv
          simp [acceptedFalse] at acceptedEnv
      exact audit_accepted_implies_valid state event resultAccepted
    have localLedger := service_cycleOpen_audit_ledger
      (systemServiceState state) input acceptedLegal
    rw [audit_serviceAccepted_eq state event external ticks] at localLedger
    simpa [systemServiceAuditPending, systemServiceAuditProducedAt, ticks,
      input, systemServiceState, nextIsland] using localLedger
  · have unticked : event.fires "mem_clk" = false :=
      Bool.eq_false_of_not_eq_true ticks
    have found : system.findIsland? "service" =
        some ⟨"service", "mem_clk", service⟩ := by rfl
    have nextIsland := System.advance_island_unticked system event external state
      ⟨"service", "mem_clk", service⟩ found unticked
    have acceptedFalse : (system.connectionResult event state
        auditConnection).accepted = false := by
      simp [System.connectionResult, System.connectionEvent, auditConnection,
        found, unticked, audit, PackedChan.named, Chan.step]
    have stepAcceptedFalse : (audit.bits.step
        (system.connectionQueue state auditConnection)
        (system.connectionEvent event state auditConnection)).accepted = false := by
      simpa [System.connectionResult, auditConnection] using acceptedFalse
    simp [systemServiceAuditPending, systemServiceAuditProducedAt, ticks,
      systemAuditAcceptedAt, Chan.acceptedValues, System.connectionResult,
      acceptedFalse, stepAcceptedFalse, systemServiceState, nextIsland]

def systemServiceAuditTraceFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List CommitRecord
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemServiceAuditProducedAt state event external ++
        systemServiceAuditTraceFrom inputs
          (system.advance event external state) rest

def systemAuditAcceptedTraceFrom (inputs : ExternalInputs) :
    system.State → List NamedClockEvent → List CommitRecord
  | _, [] => []
  | state, event :: rest =>
      let external := inputs state.time
      systemAuditAcceptedAt state event ++
        systemAuditAcceptedTraceFrom inputs
          (system.advance event external state) rest

theorem system_audit_source_ledger (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemServiceAuditPending state ++
        systemServiceAuditTraceFrom inputs state events =
      systemAuditAcceptedTraceFrom inputs state events ++
        systemServiceAuditPending
          (system.runEventsFrom inputs state events) := by
  induction events generalizing state with
  | nil => simp [systemServiceAuditTraceFrom, systemAuditAcceptedTraceFrom,
      System.runEventsFrom]
  | cons event rest ih =>
      simp only [systemServiceAuditTraceFrom, systemAuditAcceptedTraceFrom,
        System.runEventsFrom]
      let external := inputs state.time
      let next := system.advance event external state
      rw [← List.append_assoc,
        system_audit_source_ledger_step state event external]
      simpa only [List.append_assoc] using
        congrArg (fun values => systemAuditAcceptedAt state event ++ values)
          (ih next)

theorem systemAuditAcceptedTrace_eq_fifo (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemAuditAcceptedTraceFrom inputs state events =
      (audit.bits.runTrace (system.channelState state auditConnection)
        (system.channelEventsFrom inputs auditConnection state events)).accepted.map
          HwPacked.unpack := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemAuditAcceptedTraceFrom, System.channelEventsFrom,
        Chan.runTrace, List.map_append]
      let external := inputs state.time
      let next := system.advance event external state
      change systemAuditAcceptedAt state event ++
          systemAuditAcceptedTraceFrom inputs next rest = _
      rw [ih next]
      rw [System.channelState_advance system event external state
        auditConnection (by rfl)]
      rfl

theorem systemServiceAuditProducedAt_eq_commitObservation
    (state : system.State) (event : NamedClockEvent)
    (external : String → InEnv) :
    systemServiceAuditProducedAt state event external =
      match systemServiceCommitRequest? state event external with
      | some _ =>
          [HwPacked.unpack (((system.advance event external state).island
            "service").regs audit.bits.sourcePayloadName
              (HwPacked.width CommitRecord))]
      | none => [] := by
  by_cases ticks : event.fires "mem_clk" = true
  · let poked := (systemServiceState state).setInputs service.inputs
      (system.islandInput event state external "service")
    by_cases enabled : targetRequest.bits.canDeq.eval poked = 1#1 ∧
        targetResponse.bits.canEnq.eval poked = 1#1 ∧
        audit.bits.canEnq.eval poked = 1#1
    · rcases enabled with ⟨requestReady, responseReady, auditReady⟩
      have emitted := system_advance_service_emits_audit state event external
        ticks requestReady responseReady auditReady
      simp only [systemServiceAuditProducedAt, ticks, if_true,
        systemServiceCommitRequest?, serviceAuditProduced,
        PackedChan.canDeq, PackedChan.canEnq]
      rw [if_pos ⟨requestReady, responseReady, auditReady⟩,
        if_pos ⟨requestReady, responseReady, auditReady⟩]
      exact congrArg List.singleton emitted.symm
    · simp [systemServiceAuditProducedAt, systemServiceCommitRequest?,
        serviceAuditProduced, PackedChan.canDeq, PackedChan.canEnq,
        ticks, poked, enabled]
  · simp [systemServiceAuditProducedAt, systemServiceCommitRequest?, ticks]

theorem systemServiceAuditTrace_eq_history (inputs : ExternalInputs)
    (state : system.State) (events : List NamedClockEvent) :
    systemServiceAuditTraceFrom inputs state events =
      (systemServiceCommitHistoryFrom inputs state events).auditRecords := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [systemServiceAuditTraceFrom,
        systemServiceCommitHistoryFrom]
      let external := inputs state.time
      let next := system.advance event external state
      rw [systemServiceAuditProducedAt_eq_commitObservation state event external]
      cases committed : systemServiceCommitRequest? state event external with
      | none =>
          simp only
          exact ih next
      | some request =>
          simp only [List.singleton_append]
          exact congrArg (List.cons (HwPacked.unpack
            ((next.island "service").regs audit.bits.sourcePayloadName
              (HwPacked.width CommitRecord)))) (ih next)

@[simp] theorem systemServiceAuditPending_reset :
    systemServiceAuditPending system.reset = [] := by rfl

/-! ## Exact channel observations and generic FIFO laws -/

def channelEvents (connection : SystemConnection) (events : List NamedClockEvent) :=
  system.channelEventsFrom noInputs connection system.reset events

def acceptedBits (connection : SystemConnection) (events : List NamedClockEvent) :=
  (connection.chan.runTrace [] (channelEvents connection events)).accepted

def deliveredBits (connection : SystemConnection) (events : List NamedClockEvent) :=
  (connection.chan.runTrace [] (channelEvents connection events)).delivered

def acceptedCpuRequests (events : List NamedClockEvent) : List Request :=
  (acceptedBits cpuRequestConnection events).map HwPacked.unpack

def acceptedDmaRequests (events : List NamedClockEvent) : List Request :=
  (acceptedBits dmaRequestConnection events).map HwPacked.unpack

def serviceRequests (events : List NamedClockEvent) : List Request :=
  (deliveredBits targetRequestConnection events).map HwPacked.unpack

def serviceResponses (events : List NamedClockEvent) : List Response :=
  (acceptedBits targetResponseConnection events).map HwPacked.unpack

def fabricTargetResponses (events : List NamedClockEvent) : List Response :=
  (deliveredBits targetResponseConnection events).map HwPacked.unpack

def deliveredCpuResponses (events : List NamedClockEvent) : List Response :=
  (deliveredBits cpuResponseConnection events).map HwPacked.unpack

def deliveredDmaResponses (events : List NamedClockEvent) : List Response :=
  (deliveredBits dmaResponseConnection events).map HwPacked.unpack

def acceptedAuditRecords (events : List NamedClockEvent) : List CommitRecord :=
  (acceptedBits auditConnection events).map HwPacked.unpack

def deliveredAuditRecords (events : List NamedClockEvent) : List CommitRecord :=
  (deliveredBits auditConnection events).map HwPacked.unpack

def fabricGrantedRequests (events : List NamedClockEvent) : List Request :=
  systemFabricTargetRequestTraceFrom noInputs system.reset events

def fabricCpuGrantedRequests (events : List NamedClockEvent) : List Request :=
  systemFabricClientRequestGrantTraceFrom .cpu noInputs system.reset events

def fabricDmaGrantedRequests (events : List NamedClockEvent) : List Request :=
  systemFabricClientRequestGrantTraceFrom .dma noInputs system.reset events

def fabricCpuRoutedResponses (events : List NamedClockEvent) : List Response :=
  systemFabricResponseTraceFrom .cpu noInputs system.reset events

def fabricDmaRoutedResponses (events : List NamedClockEvent) : List Response :=
  systemFabricResponseTraceFrom .dma noInputs system.reset events

/-- Responses consumed from the target-response endpoint, before partitioning
them by the saved CPU/DMA route. -/
def fabricRoutedResponses (events : List NamedClockEvent) : List Response :=
  systemFabricRoutedResponseTraceFrom noInputs system.reset events

def fabricGrantedClients (events : List NamedClockEvent) : List FabricClient :=
  systemFabricGrantClientTraceFrom noInputs system.reset events

def fabricResponseRoutedClients
    (events : List NamedClockEvent) : List FabricClient :=
  systemFabricRoutedClientTraceFrom noInputs system.reset events

def fabricGrantHistory (events : List NamedClockEvent) :
    List (FabricClient × Request) :=
  systemFabricGrantObservationTraceFrom noInputs system.reset events

def fabricRoutedResponseHistory (events : List NamedClockEvent) :
    List (FabricClient × Response) :=
  systemFabricRoutedResponseObservationTraceFrom noInputs system.reset events

theorem fabricGrantHistory_clients (events : List NamedClockEvent) :
    (fabricGrantHistory events).map Prod.fst = fabricGrantedClients events := by
  exact systemFabricGrantObservationTrace_clients noInputs system.reset events

theorem fabricGrantHistory_requests (events : List NamedClockEvent) :
    (fabricGrantHistory events).map Prod.snd = fabricGrantedRequests events := by
  exact systemFabricGrantObservationTrace_requests noInputs system.reset events

theorem fabricGrantHistory_cpuRequests (events : List NamedClockEvent) :
    selectClientValues .cpu (fabricGrantHistory events) =
      fabricCpuGrantedRequests events := by
  exact systemFabricGrantObservationTrace_select .cpu noInputs system.reset events

theorem fabricGrantHistory_dmaRequests (events : List NamedClockEvent) :
    selectClientValues .dma (fabricGrantHistory events) =
      fabricDmaGrantedRequests events := by
  exact systemFabricGrantObservationTrace_select .dma noInputs system.reset events

theorem fabricRoutedResponseHistory_clients (events : List NamedClockEvent) :
    (fabricRoutedResponseHistory events).map Prod.fst =
      fabricResponseRoutedClients events := by
  exact systemFabricRoutedResponseObservationTrace_clients
    noInputs system.reset events

theorem fabricRoutedResponseHistory_responses (events : List NamedClockEvent) :
    (fabricRoutedResponseHistory events).map Prod.snd =
      fabricRoutedResponses events := by
  exact systemFabricRoutedResponseObservationTrace_responses
    noInputs system.reset events

theorem fabricRoutedResponseHistory_cpu (events : List NamedClockEvent) :
    selectClientValues .cpu (fabricRoutedResponseHistory events) =
      fabricCpuRoutedResponses events := by
  exact systemFabricRoutedResponseObservationTrace_select
    .cpu noInputs system.reset events

theorem fabricRoutedResponseHistory_dma (events : List NamedClockEvent) :
    selectClientValues .dma (fabricRoutedResponseHistory events) =
      fabricDmaRoutedResponses events := by
  exact systemFabricRoutedResponseObservationTrace_select
    .dma noInputs system.reset events

theorem reset_fabric_grant_route_client_ledger
    (events : List NamedClockEvent) :
    fabricGrantedClients events =
      fabricResponseRoutedClients events ++
        systemFabricOutstandingClients
          (system.runEventsFrom noInputs system.reset events) := by
  simpa [fabricGrantedClients, fabricResponseRoutedClients] using
    reset_fabric_route_control_ledger events

theorem reset_fabric_grant_clients_eq_routed_of_idle
    (events : List NamedClockEvent)
    (idle : systemFabricOutstandingClients
      (system.runEventsFrom noInputs system.reset events) = []) :
    fabricGrantedClients events = fabricResponseRoutedClients events := by
  simpa [idle] using reset_fabric_grant_route_client_ledger events

theorem reset_fabric_target_response_sink_ledger_public
    (events : List NamedClockEvent) :
    fabricRoutedResponses events =
      fabricTargetResponses events ++
        systemFabricTargetResponsePending
          (system.runEventsFrom noInputs system.reset events) := by
  have ledger := reset_fabric_target_response_sink_ledger events
  have delivered := systemTargetResponseDeliveredTrace_eq_fifo
    noInputs system.reset events
  have resetQueue := System.channelState_reset system
    targetResponseConnection (by rfl)
  rw [resetQueue] at delivered
  simpa [fabricRoutedResponses, fabricTargetResponses, deliveredBits,
    channelEvents] using ledger.trans (congrArg (fun values => values ++
      systemFabricTargetResponsePending
        (system.runEventsFrom noInputs system.reset events)) delivered)

theorem reset_fabric_cpu_request_sink_ledger
    (events : List NamedClockEvent) :
    fabricCpuGrantedRequests events =
      (deliveredBits cpuRequestConnection events).map HwPacked.unpack ++
        systemFabricClientRequestPending .cpu
          (system.runEventsFrom noInputs system.reset events) := by
  have ledger := reset_fabric_client_request_sink_ledger .cpu events
  have delivered := systemClientRequestDeliveredTrace_eq_fifo .cpu
    noInputs system.reset events
  have resetQueue := System.channelState_reset system
    cpuRequestConnection (by rfl)
  rw [resetQueue] at delivered
  simpa [fabricCpuGrantedRequests, deliveredBits, channelEvents] using
    ledger.trans (congrArg (fun values => values ++
      systemFabricClientRequestPending .cpu
        (system.runEventsFrom noInputs system.reset events)) delivered)

theorem reset_fabric_dma_request_sink_ledger
    (events : List NamedClockEvent) :
    fabricDmaGrantedRequests events =
      (deliveredBits dmaRequestConnection events).map HwPacked.unpack ++
        systemFabricClientRequestPending .dma
          (system.runEventsFrom noInputs system.reset events) := by
  have ledger := reset_fabric_client_request_sink_ledger .dma events
  have delivered := systemClientRequestDeliveredTrace_eq_fifo .dma
    noInputs system.reset events
  have resetQueue := System.channelState_reset system
    dmaRequestConnection (by rfl)
  rw [resetQueue] at delivered
  simpa [fabricDmaGrantedRequests, deliveredBits, channelEvents] using
    ledger.trans (congrArg (fun values => values ++
      systemFabricClientRequestPending .dma
        (system.runEventsFrom noInputs system.reset events)) delivered)

theorem reset_fabric_cpu_response_source_ledger
    (events : List NamedClockEvent) :
    fabricCpuRoutedResponses events =
      (acceptedBits cpuResponseConnection events).map HwPacked.unpack ++
        systemFabricResponsePending cpuResponse
          (system.runEventsFrom noInputs system.reset events) := by
  have ledger := system_cpuResponse_source_ledger noInputs system.reset events
  rw [systemFabricCpuResponsePending_reset] at ledger
  have accepted := systemCpuResponseAcceptedTrace_eq_fifo
    noInputs system.reset events
  have resetQueue := System.channelState_reset system
    cpuResponseConnection (by rfl)
  rw [resetQueue] at accepted
  simpa [fabricCpuRoutedResponses, acceptedBits, channelEvents] using
    ledger.trans (congrArg (fun values => values ++
      systemFabricResponsePending cpuResponse
        (system.runEventsFrom noInputs system.reset events)) accepted)

theorem reset_fabric_dma_response_source_ledger
    (events : List NamedClockEvent) :
    fabricDmaRoutedResponses events =
      (acceptedBits dmaResponseConnection events).map HwPacked.unpack ++
        systemFabricResponsePending dmaResponse
          (system.runEventsFrom noInputs system.reset events) := by
  have ledger := system_dmaResponse_source_ledger noInputs system.reset events
  rw [systemFabricDmaResponsePending_reset] at ledger
  have accepted := systemDmaResponseAcceptedTrace_eq_fifo
    noInputs system.reset events
  have resetQueue := System.channelState_reset system
    dmaResponseConnection (by rfl)
  rw [resetQueue] at accepted
  simpa [fabricDmaRoutedResponses, acceptedBits, channelEvents] using
    ledger.trans (congrArg (fun values => values ++
      systemFabricResponsePending dmaResponse
        (system.runEventsFrom noInputs system.reset events)) accepted)

/-- Every literal fabric grant has either entered the target-request FIFO or
remains in the registered source endpoint at this finite cut. -/
theorem reset_fabric_target_request_source_ledger
    (events : List NamedClockEvent) :
    fabricGrantedRequests events =
      (acceptedBits targetRequestConnection events).map HwPacked.unpack ++
        systemFabricTargetRequestPending
          (system.runEventsFrom noInputs system.reset events) := by
  have ledger := system_targetRequest_source_ledger
    noInputs system.reset events
  rw [systemFabricTargetRequestPending_reset] at ledger
  have accepted := systemTargetRequestAcceptedTrace_eq_fifo
    noInputs system.reset events
  have resetQueue := System.channelState_reset system
    targetRequestConnection (by rfl)
  rw [resetQueue] at accepted
  simpa [fabricGrantedRequests, acceptedBits, channelEvents] using
    ledger.trans (congrArg (fun values => values ++
      systemFabricTargetRequestPending
        (system.runEventsFrom noInputs system.reset events)) accepted)

/-- Exact finite-prefix target-request sink ledger in the public trace
vocabulary used by the rest of the gauntlet. -/
theorem reset_service_request_ledger (events : List NamedClockEvent) :
    (systemServiceCommitHistoryFrom noInputs system.reset events).requests =
      serviceRequests events ++
        systemServiceRequestPending
          (system.runEventsFrom noInputs system.reset events) := by
  rw [serviceCommitHistory_requests]
  have ledger := reset_service_request_sink_ledger events
  have delivered := systemTargetRequestDeliveredTrace_eq_fifo
    noInputs system.reset events
  have resetQueue := System.channelState_reset system
    targetRequestConnection (by rfl)
  rw [resetQueue] at delivered
  simpa [serviceRequests, deliveredBits, channelEvents] using
    ledger.trans (congrArg (fun values => values ++
      systemServiceRequestPending
        (system.runEventsFrom noInputs system.reset events)) delivered)

theorem reset_service_requests_eq_trace_of_drained
    (events : List NamedClockEvent)
    (drained : systemServiceRequestPending
      (system.runEventsFrom noInputs system.reset events) = []) :
    (systemServiceCommitHistoryFrom noInputs system.reset events).requests =
      serviceRequests events := by
  simpa [drained] using reset_service_request_ledger events

/-- Every response produced by an actual service commit has either entered
the target-response FIFO in order or remains in the one-entry source endpoint
at this exact finite cut. -/
theorem reset_service_response_source_ledger
    (events : List NamedClockEvent) :
    (systemServiceCommitHistoryFrom noInputs system.reset events).responses =
      serviceResponses events ++
        systemServiceResponsePending
          (system.runEventsFrom noInputs system.reset events) := by
  have ledger := system_targetResponse_source_ledger
    noInputs system.reset events
  rw [systemServiceResponsePending_reset,
    systemServiceResponseTrace_eq_history] at ledger
  have accepted := systemTargetResponseAcceptedTrace_eq_fifo
    noInputs system.reset events
  have resetQueue := System.channelState_reset system
    targetResponseConnection (by rfl)
  rw [resetQueue] at accepted
  simpa [serviceResponses, acceptedBits, channelEvents] using
    ledger.trans (congrArg (fun values => values ++
      systemServiceResponsePending
        (system.runEventsFrom noInputs system.reset events)) accepted)
theorem reset_service_audit_source_ledger (events : List NamedClockEvent) :
    (systemServiceCommitHistoryFrom noInputs system.reset events).auditRecords =
      acceptedAuditRecords events ++
        systemServiceAuditPending
          (system.runEventsFrom noInputs system.reset events) := by
  have ledger := system_audit_source_ledger noInputs system.reset events
  rw [systemServiceAuditPending_reset,
    systemServiceAuditTrace_eq_history] at ledger
  have accepted := systemAuditAcceptedTrace_eq_fifo
    noInputs system.reset events
  have resetQueue := System.channelState_reset system auditConnection (by rfl)
  rw [resetQueue] at accepted
  simpa [acceptedAuditRecords, acceptedBits, channelEvents] using
    ledger.trans (congrArg (fun values => values ++
      systemServiceAuditPending
        (system.runEventsFrom noInputs system.reset events)) accepted)

private theorem traceConservation (connection : SystemConnection)
    (found : system.connections.find? (fun candidate =>
      candidate.chan.name == connection.chan.name) = some connection)
    (events : List NamedClockEvent) :
    acceptedBits connection events = deliveredBits connection events ++
      System.channelState (system.runEventsFrom noInputs system.reset events)
        connection := by
  have resetQueue := System.channelState_reset system connection found
  have conserved :=
    System.channelTraceConservation system noInputs connection found system.reset events
  rw [resetQueue] at conserved
  simpa [acceptedBits, deliveredBits, channelEvents] using conserved

theorem cpuRequest_trace_conservation (events : List NamedClockEvent) :
    acceptedBits cpuRequestConnection events =
      deliveredBits cpuRequestConnection events ++
        System.channelState (system.runEventsFrom noInputs system.reset events)
          cpuRequestConnection := traceConservation _ (by rfl) events

theorem cpuResponse_trace_conservation (events : List NamedClockEvent) :
    acceptedBits cpuResponseConnection events =
      deliveredBits cpuResponseConnection events ++
        System.channelState (system.runEventsFrom noInputs system.reset events)
          cpuResponseConnection := traceConservation _ (by rfl) events

theorem dmaRequest_trace_conservation (events : List NamedClockEvent) :
    acceptedBits dmaRequestConnection events =
      deliveredBits dmaRequestConnection events ++
        System.channelState (system.runEventsFrom noInputs system.reset events)
          dmaRequestConnection := traceConservation _ (by rfl) events

def systemUngrantedClientRequests (client : FabricClient)
    (state : system.State) : List Request :=
  ((systemFabricClientRequestQueue client state).drop
    (systemFabricClientRequestPending client state).length).map HwPacked.unpack

theorem clientRequest_fifo_eq_pending_ungranted (client : FabricClient)
    (state : system.State)
    (coherent : FabricClientRequestSinkCoherent client state) :
    (systemFabricClientRequestQueue client state).map HwPacked.unpack =
      systemFabricClientRequestPending client state ++
        systemUngrantedClientRequests client state := by
  let channel := fabricClientRequestChannel client
  by_cases pending : (systemFabricState state).regs
      channel.bits.sinkPopName 1 = 1#1
  · have pendingEq : systemFabricClientRequestPending client state =
        [HwPacked.unpack ((systemFabricState state).regs
          channel.bits.sinkPayloadName (HwPacked.width Request))] := by
      simp [systemFabricClientRequestPending, channel, pending]
    have head := coherent pending
    cases queueEq : systemFabricClientRequestQueue client state with
    | nil => simp [queueEq] at head
    | cons first rest =>
        have firstEq : first = (systemFabricState state).regs
            channel.bits.sinkPayloadName (HwPacked.width Request) := by
          simpa [queueEq] using head
        rw [pendingEq]
        simp [systemUngrantedClientRequests, queueEq, firstEq, pendingEq]
  · have pendingEq : systemFabricClientRequestPending client state = [] := by
      simp [systemFabricClientRequestPending, channel, pending]
    rw [pendingEq]
    unfold systemUngrantedClientRequests
    rw [pendingEq]
    rfl

theorem reset_cpu_accepted_request_ledger (events : List NamedClockEvent) :
    acceptedCpuRequests events =
      fabricCpuGrantedRequests events ++
        systemUngrantedClientRequests .cpu
          (system.runEventsFrom noInputs system.reset events) := by
  let final := system.runEventsFrom noInputs system.reset events
  have invariant := system_clientRequest_sink_invariant .cpu noInputs
    system.reset events (fabricClientRequestSinkCoherent_reset .cpu)
  have split := clientRequest_fifo_eq_pending_ungranted .cpu final invariant.1
  have fifo := congrArg (List.map (HwPacked.unpack :
      BitVec (HwPacked.width Request) → Request))
    (cpuRequest_trace_conservation events)
  simp only [List.map_append] at fifo
  unfold acceptedCpuRequests
  rw [fifo]
  change (deliveredBits cpuRequestConnection events).map HwPacked.unpack ++ _ = _
  rw [show (System.channelState final cpuRequestConnection).map HwPacked.unpack =
      systemFabricClientRequestPending .cpu final ++
        systemUngrantedClientRequests .cpu final by
      simpa [final, systemFabricClientRequestQueue] using split]
  rw [← List.append_assoc, ← reset_fabric_cpu_request_sink_ledger]

theorem reset_dma_accepted_request_ledger (events : List NamedClockEvent) :
    acceptedDmaRequests events =
      fabricDmaGrantedRequests events ++
        systemUngrantedClientRequests .dma
          (system.runEventsFrom noInputs system.reset events) := by
  let final := system.runEventsFrom noInputs system.reset events
  have invariant := system_clientRequest_sink_invariant .dma noInputs
    system.reset events (fabricClientRequestSinkCoherent_reset .dma)
  have split := clientRequest_fifo_eq_pending_ungranted .dma final invariant.1
  have fifo := congrArg (List.map (HwPacked.unpack :
      BitVec (HwPacked.width Request) → Request))
    (dmaRequest_trace_conservation events)
  simp only [List.map_append] at fifo
  unfold acceptedDmaRequests
  rw [fifo]
  change (deliveredBits dmaRequestConnection events).map HwPacked.unpack ++ _ = _
  rw [show (System.channelState final dmaRequestConnection).map HwPacked.unpack =
      systemFabricClientRequestPending .dma final ++
        systemUngrantedClientRequests .dma final by
      simpa [final, systemFabricClientRequestQueue] using split]
  rw [← List.append_assoc, ← reset_fabric_dma_request_sink_ledger]

theorem reset_cpu_accepted_requests_eq_grants_of_drained
    (events : List NamedClockEvent)
    (drained : systemUngrantedClientRequests .cpu
      (system.runEventsFrom noInputs system.reset events) = []) :
    acceptedCpuRequests events = fabricCpuGrantedRequests events := by
  simpa [drained] using reset_cpu_accepted_request_ledger events

theorem reset_dma_accepted_requests_eq_grants_of_drained
    (events : List NamedClockEvent)
    (drained : systemUngrantedClientRequests .dma
      (system.runEventsFrom noInputs system.reset events) = []) :
    acceptedDmaRequests events = fabricDmaGrantedRequests events := by
  simpa [drained] using reset_dma_accepted_request_ledger events

theorem reset_cpu_accepted_requests_eq_grant_history_of_drained
    (events : List NamedClockEvent)
    (drained : systemUngrantedClientRequests .cpu
      (system.runEventsFrom noInputs system.reset events) = []) :
    acceptedCpuRequests events =
      selectClientValues .cpu (fabricGrantHistory events) := by
  calc
    _ = fabricCpuGrantedRequests events :=
      reset_cpu_accepted_requests_eq_grants_of_drained events drained
    _ = _ := (fabricGrantHistory_cpuRequests events).symm

theorem reset_dma_accepted_requests_eq_grant_history_of_drained
    (events : List NamedClockEvent)
    (drained : systemUngrantedClientRequests .dma
      (system.runEventsFrom noInputs system.reset events) = []) :
    acceptedDmaRequests events =
      selectClientValues .dma (fabricGrantHistory events) := by
  calc
    _ = fabricDmaGrantedRequests events :=
      reset_dma_accepted_requests_eq_grants_of_drained events drained
    _ = _ := (fabricGrantHistory_dmaRequests events).symm

theorem dmaResponse_trace_conservation (events : List NamedClockEvent) :
    acceptedBits dmaResponseConnection events =
      deliveredBits dmaResponseConnection events ++
        System.channelState (system.runEventsFrom noInputs system.reset events)
          dmaResponseConnection := traceConservation _ (by rfl) events

theorem reset_fabric_cpu_response_transport_ledger
    (events : List NamedClockEvent) :
    fabricCpuRoutedResponses events =
      deliveredCpuResponses events ++
        (System.channelState
          (system.runEventsFrom noInputs system.reset events)
          cpuResponseConnection).map HwPacked.unpack ++
        systemFabricResponsePending cpuResponse
          (system.runEventsFrom noInputs system.reset events) := by
  rw [reset_fabric_cpu_response_source_ledger]
  have fifo := congrArg (List.map (HwPacked.unpack :
      BitVec (HwPacked.width Response) → Response))
    (cpuResponse_trace_conservation events)
  simpa [deliveredCpuResponses, List.map_append, List.append_assoc] using
    congrArg (fun responses => responses ++
      systemFabricResponsePending cpuResponse
        (system.runEventsFrom noInputs system.reset events)) fifo

theorem reset_fabric_dma_response_transport_ledger
    (events : List NamedClockEvent) :
    fabricDmaRoutedResponses events =
      deliveredDmaResponses events ++
        (System.channelState
          (system.runEventsFrom noInputs system.reset events)
          dmaResponseConnection).map HwPacked.unpack ++
        systemFabricResponsePending dmaResponse
          (system.runEventsFrom noInputs system.reset events) := by
  rw [reset_fabric_dma_response_source_ledger]
  have fifo := congrArg (List.map (HwPacked.unpack :
      BitVec (HwPacked.width Response) → Response))
    (dmaResponse_trace_conservation events)
  simpa [deliveredDmaResponses, List.map_append, List.append_assoc] using
    congrArg (fun responses => responses ++
      systemFabricResponsePending dmaResponse
        (system.runEventsFrom noInputs system.reset events)) fifo

theorem reset_fabric_cpu_responses_eq_delivered_of_drained
    (events : List NamedClockEvent)
    (fifoDrained : System.channelState
      (system.runEventsFrom noInputs system.reset events)
      cpuResponseConnection = [])
    (sourceDrained : systemFabricResponsePending cpuResponse
      (system.runEventsFrom noInputs system.reset events) = []) :
    fabricCpuRoutedResponses events = deliveredCpuResponses events := by
  simpa [fifoDrained, sourceDrained] using
    reset_fabric_cpu_response_transport_ledger events

theorem reset_fabric_dma_responses_eq_delivered_of_drained
    (events : List NamedClockEvent)
    (fifoDrained : System.channelState
      (system.runEventsFrom noInputs system.reset events)
      dmaResponseConnection = [])
    (sourceDrained : systemFabricResponsePending dmaResponse
      (system.runEventsFrom noInputs system.reset events) = []) :
    fabricDmaRoutedResponses events = deliveredDmaResponses events := by
  simpa [fifoDrained, sourceDrained] using
    reset_fabric_dma_response_transport_ledger events

theorem targetRequest_trace_conservation (events : List NamedClockEvent) :
    acceptedBits targetRequestConnection events =
      deliveredBits targetRequestConnection events ++
        System.channelState (system.runEventsFrom noInputs system.reset events)
          targetRequestConnection := traceConservation _ (by rfl) events

def systemUncommittedTargetRequests (state : system.State) : List Request :=
  ((system.channelState state targetRequestConnection).drop
    (systemServiceRequestPending state).length).map HwPacked.unpack

theorem targetRequest_fifo_eq_pending_uncommitted (state : system.State)
    (coherent : ServiceRequestSinkCoherent state) :
    (system.channelState state targetRequestConnection).map HwPacked.unpack =
      systemServiceRequestPending state ++
        systemUncommittedTargetRequests state := by
  by_cases pending : (systemServiceState state).regs
      targetRequest.bits.sinkPopName 1 = 1#1
  · have pendingEq : systemServiceRequestPending state =
        [HwPacked.unpack ((systemServiceState state).regs
          targetRequest.bits.sinkPayloadName (HwPacked.width Request))] := by
      simp [systemServiceRequestPending, pending]
    have head := coherent pending
    cases queueEq : system.channelState state targetRequestConnection with
    | nil => simp [queueEq] at head
    | cons first rest =>
        have firstEq : first = (systemServiceState state).regs
            targetRequest.bits.sinkPayloadName (HwPacked.width Request) := by
          simpa [queueEq] using head
        rw [pendingEq]
        simp [systemUncommittedTargetRequests, queueEq, firstEq, pendingEq]
  · have pendingEq : systemServiceRequestPending state = [] := by
      simp [systemServiceRequestPending, pending]
    rw [pendingEq]
    unfold systemUncommittedTargetRequests
    rw [pendingEq]
    rfl

/-- End-to-end request ledger from literal fabric arbitration through both the
target FIFO and the registered service sink. -/
theorem reset_fabric_service_request_ledger (events : List NamedClockEvent) :
    fabricGrantedRequests events =
      (systemServiceCommitHistoryFrom noInputs system.reset events).requests ++
        systemUncommittedTargetRequests
          (system.runEventsFrom noInputs system.reset events) ++
        systemFabricTargetRequestPending
          (system.runEventsFrom noInputs system.reset events) := by
  let final := system.runEventsFrom noInputs system.reset events
  have invariant := system_targetRequest_sink_invariant noInputs system.reset
    events serviceRequestSinkCoherent_reset
  have split := targetRequest_fifo_eq_pending_uncommitted final invariant.1
  rw [reset_fabric_target_request_source_ledger]
  have fifo := congrArg (List.map (HwPacked.unpack :
      BitVec (HwPacked.width Request) → Request))
    (targetRequest_trace_conservation events)
  have service := reset_service_request_ledger events
  simp only [List.map_append] at fifo
  rw [fifo]
  change serviceRequests events ++ _ ++ _ = _
  rw [split]
  rw [← List.append_assoc, ← service]

theorem reset_fabric_requests_eq_service_of_drained
    (events : List NamedClockEvent)
    (fifoDrained : systemUncommittedTargetRequests
      (system.runEventsFrom noInputs system.reset events) = [])
    (sourceDrained : systemFabricTargetRequestPending
      (system.runEventsFrom noInputs system.reset events) = []) :
    fabricGrantedRequests events =
      (systemServiceCommitHistoryFrom noInputs system.reset events).requests := by
  simpa [fifoDrained, sourceDrained] using
    reset_fabric_service_request_ledger events

theorem targetResponse_trace_conservation (events : List NamedClockEvent) :
    acceptedBits targetResponseConnection events =
      deliveredBits targetResponseConnection events ++
        System.channelState (system.runEventsFrom noInputs system.reset events)
          targetResponseConnection := traceConservation _ (by rfl) events

/-- End-to-end finite-prefix response ledger through both storage layers of
the service-to-fabric route. -/
theorem reset_service_response_transport_ledger
    (events : List NamedClockEvent) :
    (systemServiceCommitHistoryFrom noInputs system.reset events).responses =
      fabricTargetResponses events ++
        (System.channelState
          (system.runEventsFrom noInputs system.reset events)
          targetResponseConnection).map HwPacked.unpack ++
        systemServiceResponsePending
          (system.runEventsFrom noInputs system.reset events) := by
  rw [reset_service_response_source_ledger]
  have fifo := congrArg (List.map (HwPacked.unpack :
      BitVec (HwPacked.width Response) → Response))
    (targetResponse_trace_conservation events)
  simpa [serviceResponses, fabricTargetResponses, List.map_append,
    List.append_assoc] using congrArg (fun responses => responses ++
      systemServiceResponsePending
        (system.runEventsFrom noInputs system.reset events)) fifo

/-- Target-response FIFO occupancy not already represented by the fabric's
registered sink pop. -/
def systemUnroutedTargetResponses (state : system.State) : List Response :=
  ((system.channelState state targetResponseConnection).drop
    (systemFabricTargetResponsePending state).length).map HwPacked.unpack

theorem targetResponse_fifo_eq_pending_unrouted (state : system.State)
    (coherent : FabricTargetResponseSinkCoherent state) :
    (system.channelState state targetResponseConnection).map HwPacked.unpack =
      systemFabricTargetResponsePending state ++
        systemUnroutedTargetResponses state := by
  by_cases pending : (systemFabricState state).regs
      targetResponse.bits.sinkPopName 1 = 1#1
  · have pendingEq : systemFabricTargetResponsePending state =
        [HwPacked.unpack ((systemFabricState state).regs
          targetResponse.bits.sinkPayloadName (HwPacked.width Response))] := by
      simp [systemFabricTargetResponsePending, pending]
    have head := coherent pending
    cases queueEq : system.channelState state targetResponseConnection with
    | nil => simp [queueEq] at head
    | cons first rest =>
        have firstEq : first = (systemFabricState state).regs
            targetResponse.bits.sinkPayloadName (HwPacked.width Response) := by
          simpa [queueEq] using head
        rw [pendingEq]
        simp [systemUnroutedTargetResponses, queueEq, firstEq, pendingEq]
  · have pendingEq : systemFabricTargetResponsePending state = [] := by
      simp [systemFabricTargetResponsePending, pending]
    rw [pendingEq]
    unfold systemUnroutedTargetResponses
    rw [pendingEq]
    rfl

/-- End-to-end response ledger from literal service commits to the fabric
route point, with non-overlapping endpoint and FIFO suffixes. -/
theorem reset_service_fabric_response_ledger (events : List NamedClockEvent) :
    (systemServiceCommitHistoryFrom noInputs system.reset events).responses =
      fabricRoutedResponses events ++
        systemUnroutedTargetResponses
          (system.runEventsFrom noInputs system.reset events) ++
        systemServiceResponsePending
          (system.runEventsFrom noInputs system.reset events) := by
  let final := system.runEventsFrom noInputs system.reset events
  have invariant := system_targetResponse_sink_invariant noInputs system.reset
    events fabricTargetResponseSinkCoherent_reset
  have split := targetResponse_fifo_eq_pending_unrouted final invariant.1
  rw [reset_service_response_transport_ledger]
  change fabricTargetResponses events ++ _ ++ _ = _
  rw [split]
  rw [← List.append_assoc,
    ← reset_fabric_target_response_sink_ledger_public]

theorem reset_service_responses_eq_routed_of_drained
    (events : List NamedClockEvent)
    (fifoDrained : systemUnroutedTargetResponses
      (system.runEventsFrom noInputs system.reset events) = [])
    (sourceDrained : systemServiceResponsePending
      (system.runEventsFrom noInputs system.reset events) = []) :
    (systemServiceCommitHistoryFrom noInputs system.reset events).responses =
      fabricRoutedResponses events := by
  simpa [fifoDrained, sourceDrained] using
    reset_service_fabric_response_ledger events

theorem pairs_eq_zip_projections {α β : Type} (values : List (α × β)) :
    List.zip (values.map Prod.fst) (values.map Prod.snd) = values := by
  induction values with
  | nil => rfl
  | cons value rest => simp [*]

def modelRoutedResponseHistory
    (grants : List (FabricClient × Request)) : List (FabricClient × Response) :=
  List.zip (grants.map Prod.fst) (modelResponses (grants.map Prod.snd))

def modelClientResponses (client : FabricClient)
    (grants : List (FabricClient × Request)) : List Response :=
  selectClientValues client (modelRoutedResponseHistory grants)

def RoutedResponseMatchesGrant
    (grant : FabricClient × Request) (routed : FabricClient × Response) : Prop :=
  routed.1 = grant.1 ∧ ResponseMatchesRequest grant.2 routed.2

theorem zip_routes_preserves_matches (clients : List FabricClient)
    (requests : List Request) (responses : List Response)
    (related : List.Forall₂ ResponseMatchesRequest requests responses) :
    List.Forall₂ RoutedResponseMatchesGrant
      (List.zip clients requests) (List.zip clients responses) := by
  induction related generalizing clients with
  | nil => simp
  | cons matched rest ih =>
      cases clients with
      | nil => simp
      | cons client clients =>
          simp only [List.zip_cons_cons]
          apply List.Forall₂.cons
          · exact ⟨rfl, matched⟩
          · exact ih clients

theorem modelRoutedResponseHistory_matches
    (grants : List (FabricClient × Request)) :
    List.Forall₂ RoutedResponseMatchesGrant grants
      (modelRoutedResponseHistory grants) := by
  unfold modelRoutedResponseHistory
  have related := zip_routes_preserves_matches (grants.map Prod.fst)
    (grants.map Prod.snd) (modelResponses (grants.map Prod.snd))
      (modelResponses_match (grants.map Prod.snd))
  rw [pairs_eq_zip_projections grants] at related
  exact related

/-- On a fully serviced fabric cut, literal response-route observations are
exactly the register-service model applied to literal tagged grant
observations.  The first component is physical route metadata; the response
payload remains the service's unchanged client/tag/data/error record. -/
theorem reset_fabric_routed_history_refines_model_of_drained
    (events : List NamedClockEvent)
    (requestFifoDrained : systemUncommittedTargetRequests
      (system.runEventsFrom noInputs system.reset events) = [])
    (requestSourceDrained : systemFabricTargetRequestPending
      (system.runEventsFrom noInputs system.reset events) = [])
    (responseFifoDrained : systemUnroutedTargetResponses
      (system.runEventsFrom noInputs system.reset events) = [])
    (responseSourceDrained : systemServiceResponsePending
      (system.runEventsFrom noInputs system.reset events) = [])
    (fabricIdle : systemFabricOutstandingClients
      (system.runEventsFrom noInputs system.reset events) = []) :
    fabricRoutedResponseHistory events =
      modelRoutedResponseHistory (fabricGrantHistory events) := by
  let history := systemServiceCommitHistoryFrom noInputs system.reset events
  have requestEq := reset_fabric_requests_eq_service_of_drained events
    requestFifoDrained requestSourceDrained
  have responseEq := reset_service_responses_eq_routed_of_drained events
    responseFifoDrained responseSourceDrained
  have refined := (reset_service_commit_history_refines events).1
  have routedValues : fabricRoutedResponses events =
      modelResponses (fabricGrantedRequests events) := by
    calc
      _ = history.responses := responseEq.symm
      _ = modelResponses history.requests := refined
      _ = modelResponses (fabricGrantedRequests events) := by rw [requestEq]
  rw [← pairs_eq_zip_projections (fabricRoutedResponseHistory events)]
  unfold modelRoutedResponseHistory
  rw [fabricRoutedResponseHistory_clients,
    fabricRoutedResponseHistory_responses,
    fabricGrantHistory_clients, fabricGrantHistory_requests,
    reset_fabric_grant_clients_eq_routed_of_idle events fabricIdle,
    routedValues]

theorem reset_fabric_routed_history_matches_grants_of_drained
    (events : List NamedClockEvent)
    (requestFifoDrained : systemUncommittedTargetRequests
      (system.runEventsFrom noInputs system.reset events) = [])
    (requestSourceDrained : systemFabricTargetRequestPending
      (system.runEventsFrom noInputs system.reset events) = [])
    (responseFifoDrained : systemUnroutedTargetResponses
      (system.runEventsFrom noInputs system.reset events) = [])
    (responseSourceDrained : systemServiceResponsePending
      (system.runEventsFrom noInputs system.reset events) = [])
    (fabricIdle : systemFabricOutstandingClients
      (system.runEventsFrom noInputs system.reset events) = []) :
    List.Forall₂ RoutedResponseMatchesGrant
      (fabricGrantHistory events) (fabricRoutedResponseHistory events) := by
  rw [reset_fabric_routed_history_refines_model_of_drained events
    requestFifoDrained requestSourceDrained responseFifoDrained
    responseSourceDrained fabricIdle]
  exact modelRoutedResponseHistory_matches _

theorem reset_cpu_delivered_responses_refine_grants_of_drained
    (events : List NamedClockEvent)
    (requestFifoDrained : systemUncommittedTargetRequests
      (system.runEventsFrom noInputs system.reset events) = [])
    (requestSourceDrained : systemFabricTargetRequestPending
      (system.runEventsFrom noInputs system.reset events) = [])
    (responseFifoDrained : systemUnroutedTargetResponses
      (system.runEventsFrom noInputs system.reset events) = [])
    (responseSourceDrained : systemServiceResponsePending
      (system.runEventsFrom noInputs system.reset events) = [])
    (fabricIdle : systemFabricOutstandingClients
      (system.runEventsFrom noInputs system.reset events) = [])
    (clientFifoDrained : System.channelState
      (system.runEventsFrom noInputs system.reset events)
      cpuResponseConnection = [])
    (clientSourceDrained : systemFabricResponsePending cpuResponse
      (system.runEventsFrom noInputs system.reset events) = []) :
    deliveredCpuResponses events =
      modelClientResponses .cpu (fabricGrantHistory events) := by
  have modeled := reset_fabric_routed_history_refines_model_of_drained events
    requestFifoDrained requestSourceDrained responseFifoDrained
    responseSourceDrained fabricIdle
  have delivered := reset_fabric_cpu_responses_eq_delivered_of_drained events
    clientFifoDrained clientSourceDrained
  unfold modelClientResponses
  calc
    deliveredCpuResponses events = fabricCpuRoutedResponses events := delivered.symm
    _ = selectClientValues .cpu (fabricRoutedResponseHistory events) :=
      (fabricRoutedResponseHistory_cpu events).symm
    _ = selectClientValues .cpu
        (modelRoutedResponseHistory (fabricGrantHistory events)) := by rw [modeled]

theorem reset_dma_delivered_responses_refine_grants_of_drained
    (events : List NamedClockEvent)
    (requestFifoDrained : systemUncommittedTargetRequests
      (system.runEventsFrom noInputs system.reset events) = [])
    (requestSourceDrained : systemFabricTargetRequestPending
      (system.runEventsFrom noInputs system.reset events) = [])
    (responseFifoDrained : systemUnroutedTargetResponses
      (system.runEventsFrom noInputs system.reset events) = [])
    (responseSourceDrained : systemServiceResponsePending
      (system.runEventsFrom noInputs system.reset events) = [])
    (fabricIdle : systemFabricOutstandingClients
      (system.runEventsFrom noInputs system.reset events) = [])
    (clientFifoDrained : System.channelState
      (system.runEventsFrom noInputs system.reset events)
      dmaResponseConnection = [])
    (clientSourceDrained : systemFabricResponsePending dmaResponse
      (system.runEventsFrom noInputs system.reset events) = []) :
    deliveredDmaResponses events =
      modelClientResponses .dma (fabricGrantHistory events) := by
  have modeled := reset_fabric_routed_history_refines_model_of_drained events
    requestFifoDrained requestSourceDrained responseFifoDrained
    responseSourceDrained fabricIdle
  have delivered := reset_fabric_dma_responses_eq_delivered_of_drained events
    clientFifoDrained clientSourceDrained
  unfold modelClientResponses
  calc
    deliveredDmaResponses events = fabricDmaRoutedResponses events := delivered.symm
    _ = selectClientValues .dma (fabricRoutedResponseHistory events) :=
      (fabricRoutedResponseHistory_dma events).symm
    _ = selectClientValues .dma
        (modelRoutedResponseHistory (fabricGrantHistory events)) := by rw [modeled]

theorem reset_service_responses_eq_fabric_of_drained
    (events : List NamedClockEvent)
    (fifoDrained : System.channelState
      (system.runEventsFrom noInputs system.reset events)
      targetResponseConnection = [])
    (sourceDrained : systemServiceResponsePending
      (system.runEventsFrom noInputs system.reset events) = []) :
    (systemServiceCommitHistoryFrom noInputs system.reset events).responses =
      fabricTargetResponses events := by
  simpa [fifoDrained, sourceDrained] using
    reset_service_response_transport_ledger events

theorem audit_trace_conservation (events : List NamedClockEvent) :
    acceptedBits auditConnection events = deliveredBits auditConnection events ++
      System.channelState (system.runEventsFrom noInputs system.reset events)
        auditConnection := traceConservation _ (by rfl) events

theorem reset_service_audit_transport_ledger (events : List NamedClockEvent) :
    (systemServiceCommitHistoryFrom noInputs system.reset events).auditRecords =
      deliveredAuditRecords events ++
        (System.channelState
          (system.runEventsFrom noInputs system.reset events)
          auditConnection).map HwPacked.unpack ++
        systemServiceAuditPending
          (system.runEventsFrom noInputs system.reset events) := by
  rw [reset_service_audit_source_ledger]
  have fifo := congrArg (List.map (HwPacked.unpack :
      BitVec (HwPacked.width CommitRecord) → CommitRecord))
    (audit_trace_conservation events)
  simpa [acceptedAuditRecords, deliveredAuditRecords, List.map_append,
    List.append_assoc] using congrArg (fun records => records ++
      systemServiceAuditPending
        (system.runEventsFrom noInputs system.reset events)) fifo

theorem reset_service_audit_eq_delivered_of_drained
    (events : List NamedClockEvent)
    (fifoDrained : System.channelState
      (system.runEventsFrom noInputs system.reset events) auditConnection = [])
    (sourceDrained : systemServiceAuditPending
      (system.runEventsFrom noInputs system.reset events) = []) :
    (systemServiceCommitHistoryFrom noInputs system.reset events).auditRecords =
      deliveredAuditRecords events := by
  simpa [fifoDrained, sourceDrained] using
    reset_service_audit_transport_ledger events

def AllChannelsWithinCapacity (state : system.State) : Prop :=
  (System.channelState state cpuRequestConnection).length ≤ cpuRequest.bits.depth ∧
  (System.channelState state cpuResponseConnection).length ≤ cpuResponse.bits.depth ∧
  (System.channelState state dmaRequestConnection).length ≤ dmaRequest.bits.depth ∧
  (System.channelState state dmaResponseConnection).length ≤ dmaResponse.bits.depth ∧
  (System.channelState state targetRequestConnection).length ≤ targetRequest.bits.depth ∧
  (System.channelState state targetResponseConnection).length ≤ targetResponse.bits.depth ∧
  (System.channelState state auditConnection).length ≤ audit.bits.depth

theorem all_channels_within_capacity : system.Invariant AllChannelsWithinCapacity := by
  have c1 := System.channelCapacityInvariant system cpuRequestConnection (by rfl)
  have c2 := System.channelCapacityInvariant system cpuResponseConnection (by rfl)
  have c3 := System.channelCapacityInvariant system dmaRequestConnection (by rfl)
  have c4 := System.channelCapacityInvariant system dmaResponseConnection (by rfl)
  have c5 := System.channelCapacityInvariant system targetRequestConnection (by rfl)
  have c6 := System.channelCapacityInvariant system targetResponseConnection (by rfl)
  have c7 := System.channelCapacityInvariant system auditConnection (by rfl)
  intro schedule inputs admitted state reachable
  exact ⟨c1 schedule inputs admitted state reachable,
    c2 schedule inputs admitted state reachable,
    c3 schedule inputs admitted state reachable,
    c4 schedule inputs admitted state reachable,
    c5 schedule inputs admitted state reachable,
    c6 schedule inputs admitted state reachable,
    c7 schedule inputs admitted state reachable⟩

/-- The unconditional finite-schedule safety result.  Every equation retains
its literal endpoint/FIFO suffix at the cut; no clock fairness, ratio, drain,
or eventual-acceptance premise is hidden here. -/
structure FiniteScheduleSafety (events : List NamedClockEvent) : Prop where
  serviceModel :
    let history := systemServiceCommitHistoryFrom noInputs system.reset events
    history.responses = modelResponses history.requests ∧
      history.auditRecords = modelCommits history.requests ∧
      systemServiceMemory (system.runEventsFrom noInputs system.reset events) =
        committedMemory history.requests
  cpuAcceptedLedger : acceptedCpuRequests events =
    fabricCpuGrantedRequests events ++
      systemUngrantedClientRequests .cpu
        (system.runEventsFrom noInputs system.reset events)
  dmaAcceptedLedger : acceptedDmaRequests events =
    fabricDmaGrantedRequests events ++
      systemUngrantedClientRequests .dma
        (system.runEventsFrom noInputs system.reset events)
  targetRequestLedger : fabricGrantedRequests events =
    (systemServiceCommitHistoryFrom noInputs system.reset events).requests ++
      systemUncommittedTargetRequests
        (system.runEventsFrom noInputs system.reset events) ++
      systemFabricTargetRequestPending
        (system.runEventsFrom noInputs system.reset events)
  targetResponseLedger :
    (systemServiceCommitHistoryFrom noInputs system.reset events).responses =
      fabricRoutedResponses events ++
        systemUnroutedTargetResponses
          (system.runEventsFrom noInputs system.reset events) ++
        systemServiceResponsePending
          (system.runEventsFrom noInputs system.reset events)
  routeControlLedger : fabricGrantedClients events =
    fabricResponseRoutedClients events ++
      systemFabricOutstandingClients
        (system.runEventsFrom noInputs system.reset events)
  cpuResponseLedger : fabricCpuRoutedResponses events =
    deliveredCpuResponses events ++
      (System.channelState
        (system.runEventsFrom noInputs system.reset events)
        cpuResponseConnection).map HwPacked.unpack ++
      systemFabricResponsePending cpuResponse
        (system.runEventsFrom noInputs system.reset events)
  dmaResponseLedger : fabricDmaRoutedResponses events =
    deliveredDmaResponses events ++
      (System.channelState
        (system.runEventsFrom noInputs system.reset events)
        dmaResponseConnection).map HwPacked.unpack ++
      systemFabricResponsePending dmaResponse
        (system.runEventsFrom noInputs system.reset events)
  auditLedger :
    (systemServiceCommitHistoryFrom noInputs system.reset events).auditRecords =
      deliveredAuditRecords events ++
        (System.channelState
          (system.runEventsFrom noInputs system.reset events)
          auditConnection).map HwPacked.unpack ++
        systemServiceAuditPending
          (system.runEventsFrom noInputs system.reset events)
  grantHistoryClients : (fabricGrantHistory events).map Prod.fst =
    fabricGrantedClients events
  grantHistoryRequests : (fabricGrantHistory events).map Prod.snd =
    fabricGrantedRequests events
  routedHistoryClients : (fabricRoutedResponseHistory events).map Prod.fst =
    fabricResponseRoutedClients events
  routedHistoryResponses : (fabricRoutedResponseHistory events).map Prod.snd =
    fabricRoutedResponses events
  modeledPayloadIdentity : List.Forall₂ ResponseMatchesRequest
    (systemServiceCommitHistoryFrom noInputs system.reset events).requests
    (modelResponses
      (systemServiceCommitHistoryFrom noInputs system.reset events).requests)
  atMostOneGrantPerFabricTick : ∀ state,
    (fabricTargetRequestProduced state).length ≤ 1
  channelCapacity : system.Invariant AllChannelsWithinCapacity

theorem soc_fabric_unconditional_safety (events : List NamedClockEvent) :
    FiniteScheduleSafety events where
  serviceModel := reset_service_commit_history_refines events
  cpuAcceptedLedger := reset_cpu_accepted_request_ledger events
  dmaAcceptedLedger := reset_dma_accepted_request_ledger events
  targetRequestLedger := reset_fabric_service_request_ledger events
  targetResponseLedger := reset_service_fabric_response_ledger events
  routeControlLedger := reset_fabric_grant_route_client_ledger events
  cpuResponseLedger := reset_fabric_cpu_response_transport_ledger events
  dmaResponseLedger := reset_fabric_dma_response_transport_ledger events
  auditLedger := reset_service_audit_transport_ledger events
  grantHistoryClients := fabricGrantHistory_clients events
  grantHistoryRequests := fabricGrantHistory_requests events
  routedHistoryClients := fabricRoutedResponseHistory_clients events
  routedHistoryResponses := fabricRoutedResponseHistory_responses events
  modeledPayloadIdentity := modelResponses_match _
  atMostOneGrantPerFabricTick := fabricTargetRequestProduced_length_le_one
  channelCapacity := all_channels_within_capacity

end Machines.Multiclock.SoCFabricGauntlet
