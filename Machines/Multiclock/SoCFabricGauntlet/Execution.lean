-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SoCFabricGauntlet.Certification
import Loom.Hw.FastEval

/-!
# Compact executable semantics

The authoritative public semantics remains `System.runEventsFrom`.  This file
stores only the five verified FastEval island states, seven abstract queues,
and event index.  A correspondence theorem is the release boundary for using
this representation in large campaigns.
-/

namespace Machines.Multiclock.SoCFabricGauntlet.Execution

open Loom.Hw
open Machines.Multiclock.SoCFabricGauntlet

private def mustSlot (design : Design) {width : Nat} (reg : Reg width)
    (ready : (FastEval.regSlot? design reg).isSome = true) :
    FastEval.RegSlot design reg :=
  match found : FastEval.regSlot? design reg with
  | some slot => slot
  | none => False.elim <| by rw [found] at ready; contradiction

private def cpuSim : FastEval.VerifiedSimulator cpu := ⟨by decide⟩
private def dmaSim : FastEval.VerifiedSimulator dma := ⟨by decide⟩
private def fabricSim : FastEval.VerifiedSimulator fabric := ⟨by decide⟩
private def serviceSim : FastEval.VerifiedSimulator service := ⟨by decide⟩
private def monitorSim : FastEval.VerifiedSimulator monitor := ⟨by decide⟩

private def slot (design : Design) (name : String) {width : Nat}
    (ready : (FastEval.regSlot? design (Reg.mk name : Reg width)).isSome = true) :=
  mustSlot design (Reg.mk name : Reg width) ready

private def cpuReqValid := slot (width := 1) cpu cpuRequest.bits.sourceValidName (by decide)
private def cpuReqPayload := slot (width := 50) cpu cpuRequest.bits.sourcePayloadName (by decide)
private def cpuRespPop := slot (width := 1) cpu cpuResponse.bits.sinkPopName (by decide)
private def dmaReqValid := slot (width := 1) dma dmaRequest.bits.sourceValidName (by decide)
private def dmaReqPayload := slot (width := 50) dma dmaRequest.bits.sourcePayloadName (by decide)
private def dmaRespPop := slot (width := 1) dma dmaResponse.bits.sinkPopName (by decide)

private def fabricCpuReqPop := slot (width := 1) fabric cpuRequest.bits.sinkPopName (by decide)
private def fabricCpuRespValid := slot (width := 1) fabric cpuResponse.bits.sourceValidName (by decide)
private def fabricCpuRespPayload := slot (width := 38) fabric cpuResponse.bits.sourcePayloadName (by decide)
private def fabricDmaReqPop := slot (width := 1) fabric dmaRequest.bits.sinkPopName (by decide)
private def fabricDmaRespValid := slot (width := 1) fabric dmaResponse.bits.sourceValidName (by decide)
private def fabricDmaRespPayload := slot (width := 38) fabric dmaResponse.bits.sourcePayloadName (by decide)
private def fabricTargetReqValid := slot (width := 1) fabric targetRequest.bits.sourceValidName (by decide)
private def fabricTargetReqPayload := slot (width := 50) fabric targetRequest.bits.sourcePayloadName (by decide)
private def fabricTargetRespPop := slot (width := 1) fabric targetResponse.bits.sinkPopName (by decide)

private def serviceTargetReqPop := slot (width := 1) service targetRequest.bits.sinkPopName (by decide)
private def serviceTargetRespValid := slot (width := 1) service targetResponse.bits.sourceValidName (by decide)
private def serviceTargetRespPayload := slot (width := 38) service targetResponse.bits.sourcePayloadName (by decide)
private def serviceAuditValid := slot (width := 1) service audit.bits.sourceValidName (by decide)
private def serviceAuditPayload := slot (width := 46) service audit.bits.sourcePayloadName (by decide)
private def monitorAuditPop := slot (width := 1) monitor audit.bits.sinkPopName (by decide)

structure FastState where
  cpu : FastSt
  dma : FastSt
  fabric : FastSt
  service : FastSt
  monitor : FastSt
  cpuRequest : Chan.State 50
  cpuResponse : Chan.State 38
  dmaRequest : Chan.State 50
  dmaResponse : Chan.State 38
  targetRequest : Chan.State 50
  targetResponse : Chan.State 38
  audit : Chan.State 46
  time : Nat

def reset : FastState :=
  ⟨cpuSim.reset, dmaSim.reset, fabricSim.reset, serviceSim.reset,
    monitorSim.reset, [], [], [], [], [], [], [], 0⟩

/-- The supported reset contract is coordinated replacement of all island and
channel state.  No unilateral-domain reset transition is provided. -/
def coordinatedReset (_loaded : FastState) : FastState := reset

@[simp] theorem coordinatedReset_eq (loaded : FastState) :
    coordinatedReset loaded = reset := rfl

/-- A lightweight semantic view used only for System-owned endpoint planning.
It does not execute semantic islands or copy memories: `Design.toSt` installs
readback closures over the existing flat arrays, and queues are packed by
reference into the public System representation. -/
def view (state : FastState) : system.State where
  island := fun name =>
    if name = "cpu" then cpu.toSt state.cpu
    else if name = "dma" then dma.toSt state.dma
    else if name = "fabric" then fabric.toSt state.fabric
    else if name = "service" then service.toSt state.service
    else if name = "monitor" then monitor.toSt state.monitor
    else ⟨fun _ _ => 0, fun _ _ _ => 0⟩
  channel := fun name =>
    if name = cpuRequest.bits.name then ⟨HwPacked.width Request, state.cpuRequest⟩
    else if name = cpuResponse.bits.name then ⟨HwPacked.width Response, state.cpuResponse⟩
    else if name = dmaRequest.bits.name then ⟨HwPacked.width Request, state.dmaRequest⟩
    else if name = dmaResponse.bits.name then ⟨HwPacked.width Response, state.dmaResponse⟩
    else if name = targetRequest.bits.name then ⟨HwPacked.width Request, state.targetRequest⟩
    else if name = targetResponse.bits.name then ⟨HwPacked.width Response, state.targetResponse⟩
    else if name = audit.bits.name then ⟨HwPacked.width CommitRecord, state.audit⟩
    else ⟨0, []⟩
  time := state.time

private theorem bitVecNonzero {width : Nat} (value : BitVec width) :
    (value.toNat != 0) = (value != 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne]
  constructor
  · intro nonzero zero
    apply nonzero
    simpa [zero]
  · intro nonzero toNatZero
    apply nonzero
    exact BitVec.toNat_inj.mp (by simpa using toNatZero)

private def cpuRequestEvent (clockEvent : NamedClockEvent) (state : FastState) :
    Chan.Event 50 :=
  { push := if clockEvent.fires "cpu_fabric_clk" &&
        cpuReqValid.read state.cpu != 0 then
      some (cpuReqPayload.read state.cpu) else none
    pop := clockEvent.fires "cpu_fabric_clk" &&
      fabricCpuReqPop.read state.fabric != 0 }

private def cpuResponseEvent (clockEvent : NamedClockEvent) (state : FastState) :
    Chan.Event 38 :=
  { push := if clockEvent.fires "cpu_fabric_clk" &&
        fabricCpuRespValid.read state.fabric != 0 then
      some (fabricCpuRespPayload.read state.fabric) else none
    pop := clockEvent.fires "cpu_fabric_clk" && cpuRespPop.read state.cpu != 0 }

private def dmaRequestEvent (clockEvent : NamedClockEvent) (state : FastState) :
    Chan.Event 50 :=
  { push := if clockEvent.fires "dma_clk" && dmaReqValid.read state.dma != 0 then
      some (dmaReqPayload.read state.dma) else none
    pop := clockEvent.fires "cpu_fabric_clk" &&
      fabricDmaReqPop.read state.fabric != 0 }

private def dmaResponseEvent (clockEvent : NamedClockEvent) (state : FastState) :
    Chan.Event 38 :=
  { push := if clockEvent.fires "cpu_fabric_clk" &&
        fabricDmaRespValid.read state.fabric != 0 then
      some (fabricDmaRespPayload.read state.fabric) else none
    pop := clockEvent.fires "dma_clk" && dmaRespPop.read state.dma != 0 }

private def targetRequestEvent (clockEvent : NamedClockEvent) (state : FastState) :
    Chan.Event 50 :=
  { push := if clockEvent.fires "cpu_fabric_clk" &&
        fabricTargetReqValid.read state.fabric != 0 then
      some (fabricTargetReqPayload.read state.fabric) else none
    pop := clockEvent.fires "mem_clk" &&
      serviceTargetReqPop.read state.service != 0 }

private def targetResponseEvent (clockEvent : NamedClockEvent) (state : FastState) :
    Chan.Event 38 :=
  { push := if clockEvent.fires "mem_clk" &&
        serviceTargetRespValid.read state.service != 0 then
      some (serviceTargetRespPayload.read state.service) else none
    pop := clockEvent.fires "cpu_fabric_clk" &&
      fabricTargetRespPop.read state.fabric != 0 }

private def auditEvent (clockEvent : NamedClockEvent) (state : FastState) :
    Chan.Event 46 :=
  { push := if clockEvent.fires "mem_clk" &&
        serviceAuditValid.read state.service != 0 then
      some (serviceAuditPayload.read state.service) else none
    pop := clockEvent.fires "mon_clk" && monitorAuditPop.read state.monitor != 0 }

def advance (inputs : ExternalInputs) (clockEvent : NamedClockEvent)
    (state : FastState) : FastState :=
  let external := inputs state.time
  let semantic := view state
  let cpuReqEvent := cpuRequestEvent clockEvent state
  let cpuRespEvent := cpuResponseEvent clockEvent state
  let dmaReqEvent := dmaRequestEvent clockEvent state
  let dmaRespEvent := dmaResponseEvent clockEvent state
  let targetReqEvent := targetRequestEvent clockEvent state
  let targetRespEvent := targetResponseEvent clockEvent state
  let auditRequest := auditEvent clockEvent state
  let cpuReq := cpuRequest.bits.step state.cpuRequest cpuReqEvent
  let cpuResp := cpuResponse.bits.step state.cpuResponse cpuRespEvent
  let dmaReq := dmaRequest.bits.step state.dmaRequest dmaReqEvent
  let dmaResp := dmaResponse.bits.step state.dmaResponse dmaRespEvent
  let targetReq := targetRequest.bits.step state.targetRequest targetReqEvent
  let targetResp := targetResponse.bits.step state.targetResponse targetRespEvent
  let auditResult := audit.bits.step state.audit auditRequest
  { cpu := if clockEvent.fires "cpu_fabric_clk" then cpuSim.cycleOpen
      (system.islandInput clockEvent semantic external "cpu") state.cpu else state.cpu
    dma := if clockEvent.fires "dma_clk" then dmaSim.cycleOpen
      (system.islandInput clockEvent semantic external "dma") state.dma else state.dma
    fabric := if clockEvent.fires "cpu_fabric_clk" then fabricSim.cycleOpen
      (system.islandInput clockEvent semantic external "fabric") state.fabric else state.fabric
    service := if clockEvent.fires "mem_clk" then serviceSim.cycleOpen
      (system.islandInput clockEvent semantic external "service") state.service else state.service
    monitor := if clockEvent.fires "mon_clk" then monitorSim.cycleOpen
      (system.islandInput clockEvent semantic external "monitor") state.monitor else state.monitor
    cpuRequest := cpuReq.state
    cpuResponse := cpuResp.state
    dmaRequest := dmaReq.state
    dmaResponse := dmaResp.state
    targetRequest := targetReq.state
    targetResponse := targetResp.state
    audit := auditResult.state
    time := state.time + 1 }

def run (inputs : ExternalInputs) : FastState → List NamedClockEvent → FastState
  | state, [] => state
  | state, next :: rest => run inputs (advance inputs next state) rest

def inputsWithLimit (limit : Nat) : ExternalInputs :=
  fun _ island name width =>
    if (island = "cpu" || island = "dma") && name = "transaction_limit" then
      BitVec.ofNat width limit
    else 0

/-- Standard 256-transaction campaign inputs.  The limit is an input so the
literal canonical RTL can also execute the continuous silicon soak. -/
def noInputs : ExternalInputs := inputsWithLimit transactionCount

/-- Proof relation between the allocation-light campaign state and Loom's
authoritative named-System state. -/
structure Represents (fast : FastState) (semantic : system.State) : Prop where
  cpu : Agree cpu fast.cpu (semantic.island "cpu")
  dma : Agree dma fast.dma (semantic.island "dma")
  fabric : Agree fabric fast.fabric (semantic.island "fabric")
  service : Agree service fast.service (semantic.island "service")
  monitor : Agree monitor fast.monitor (semantic.island "monitor")
  cpuRequest : fast.cpuRequest = System.channelState semantic cpuRequestConnection
  cpuResponse : fast.cpuResponse = System.channelState semantic cpuResponseConnection
  dmaRequest : fast.dmaRequest = System.channelState semantic dmaRequestConnection
  dmaResponse : fast.dmaResponse = System.channelState semantic dmaResponseConnection
  targetRequest : fast.targetRequest = System.channelState semantic targetRequestConnection
  targetResponse : fast.targetResponse = System.channelState semantic targetResponseConnection
  audit : fast.audit = System.channelState semantic auditConnection
  time : fast.time = semantic.time

theorem reset_represents : Represents reset system.reset := by
  refine
    { cpu := FastEval.agree_fastReset cpu
      dma := FastEval.agree_fastReset dma
      fabric := FastEval.agree_fastReset fabric
      service := FastEval.agree_fastReset service
      monitor := FastEval.agree_fastReset monitor
      time := rfl
      cpuRequest := ?_
      cpuResponse := ?_
      dmaRequest := ?_
      dmaResponse := ?_
      targetRequest := ?_
      targetResponse := ?_
      audit := ?_ }
  · exact (System.channelState_reset system cpuRequestConnection (by rfl)).symm
  · exact (System.channelState_reset system cpuResponseConnection (by rfl)).symm
  · exact (System.channelState_reset system dmaRequestConnection (by rfl)).symm
  · exact (System.channelState_reset system dmaResponseConnection (by rfl)).symm
  · exact (System.channelState_reset system targetRequestConnection (by rfl)).symm
  · exact (System.channelState_reset system targetResponseConnection (by rfl)).symm
  · exact (System.channelState_reset system auditConnection (by rfl)).symm

@[simp] theorem view_cpuRequest (state : FastState) :
    System.channelState (view state) cpuRequestConnection = state.cpuRequest := by
  simp [System.channelState, System.connectionQueue, view, cpuRequestConnection,
    System.PackedQueue.asWidth, cpuRequest, PackedChan.named]

@[simp] theorem view_cpuResponse (state : FastState) :
    System.channelState (view state) cpuResponseConnection = state.cpuResponse := by
  simp [System.channelState, System.connectionQueue, view, cpuResponseConnection,
    System.PackedQueue.asWidth, cpuRequest, cpuResponse, PackedChan.named]

@[simp] theorem view_dmaRequest (state : FastState) :
    System.channelState (view state) dmaRequestConnection = state.dmaRequest := by
  simp [System.channelState, System.connectionQueue, view, dmaRequestConnection,
    System.PackedQueue.asWidth, cpuRequest, cpuResponse, dmaRequest, PackedChan.named]

@[simp] theorem view_dmaResponse (state : FastState) :
    System.channelState (view state) dmaResponseConnection = state.dmaResponse := by
  simp [System.channelState, System.connectionQueue, view, dmaResponseConnection,
    System.PackedQueue.asWidth, cpuRequest, cpuResponse, dmaRequest, dmaResponse,
    PackedChan.named]

@[simp] theorem view_targetRequest (state : FastState) :
    System.channelState (view state) targetRequestConnection = state.targetRequest := by
  simp [System.channelState, System.connectionQueue, view, targetRequestConnection,
    System.PackedQueue.asWidth, cpuRequest, cpuResponse, dmaRequest, dmaResponse,
    targetRequest, PackedChan.named]

@[simp] theorem view_targetResponse (state : FastState) :
    System.channelState (view state) targetResponseConnection = state.targetResponse := by
  simp [System.channelState, System.connectionQueue, view, targetResponseConnection,
    System.PackedQueue.asWidth, cpuRequest, cpuResponse, dmaRequest, dmaResponse,
    targetRequest, targetResponse, PackedChan.named]

@[simp] theorem view_audit (state : FastState) :
    System.channelState (view state) auditConnection = state.audit := by
  simp [System.channelState, System.connectionQueue, view, auditConnection,
    System.PackedQueue.asWidth, cpuRequest, cpuResponse, dmaRequest, dmaResponse,
    targetRequest, targetResponse, audit, PackedChan.named]

private theorem cpuRequestEvent_view (clockEvent : NamedClockEvent)
    (state : FastState) :
    cpuRequestEvent clockEvent state =
      system.connectionEvent clockEvent (view state) cpuRequestConnection := by
  have cpuFound : system.findIsland? "cpu" =
      some ⟨"cpu", "cpu_fabric_clk", cpu⟩ := by rfl
  have fabricFound : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  have payload :
      (cpu.toSt state.cpu).regs cpuRequest.bits.sourcePayloadName
          (HwPacked.width Request) = cpuReqPayload.read state.cpu := by
    simpa using (cpuReqPayload.read_toSt state.cpu).symm
  simp [cpuRequestEvent, System.connectionEvent, cpuRequestConnection,
    cpuFound, fabricFound, view, Chan.sourceValid, Chan.sourcePayload, Expr.eval,
    ← cpuReqValid.read_toSt state.cpu, payload,
    ← fabricCpuReqPop.read_toSt state.fabric]

private theorem cpuResponseEvent_view (clockEvent : NamedClockEvent)
    (state : FastState) :
    cpuResponseEvent clockEvent state =
      system.connectionEvent clockEvent (view state) cpuResponseConnection := by
  have fabricFound : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  have cpuFound : system.findIsland? "cpu" =
      some ⟨"cpu", "cpu_fabric_clk", cpu⟩ := by rfl
  have payload :
      (fabric.toSt state.fabric).regs cpuResponse.bits.sourcePayloadName
          (HwPacked.width Response) = fabricCpuRespPayload.read state.fabric := by
    simpa using (fabricCpuRespPayload.read_toSt state.fabric).symm
  simp [cpuResponseEvent, System.connectionEvent, cpuResponseConnection,
    fabricFound, cpuFound, view, Chan.sourceValid, Chan.sourcePayload, Expr.eval,
    ← fabricCpuRespValid.read_toSt state.fabric, payload,
    ← cpuRespPop.read_toSt state.cpu]

private theorem dmaRequestEvent_view (clockEvent : NamedClockEvent)
    (state : FastState) :
    dmaRequestEvent clockEvent state =
      system.connectionEvent clockEvent (view state) dmaRequestConnection := by
  have dmaFound : system.findIsland? "dma" =
      some ⟨"dma", "dma_clk", dma⟩ := by rfl
  have fabricFound : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  have payload :
      (dma.toSt state.dma).regs dmaRequest.bits.sourcePayloadName
          (HwPacked.width Request) = dmaReqPayload.read state.dma := by
    simpa using (dmaReqPayload.read_toSt state.dma).symm
  simp [dmaRequestEvent, System.connectionEvent, dmaRequestConnection,
    dmaFound, fabricFound, view, Chan.sourceValid, Chan.sourcePayload, Expr.eval,
    ← dmaReqValid.read_toSt state.dma, payload,
    ← fabricDmaReqPop.read_toSt state.fabric]

private theorem dmaResponseEvent_view (clockEvent : NamedClockEvent)
    (state : FastState) :
    dmaResponseEvent clockEvent state =
      system.connectionEvent clockEvent (view state) dmaResponseConnection := by
  have fabricFound : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  have dmaFound : system.findIsland? "dma" =
      some ⟨"dma", "dma_clk", dma⟩ := by rfl
  have payload :
      (fabric.toSt state.fabric).regs dmaResponse.bits.sourcePayloadName
          (HwPacked.width Response) = fabricDmaRespPayload.read state.fabric := by
    simpa using (fabricDmaRespPayload.read_toSt state.fabric).symm
  simp [dmaResponseEvent, System.connectionEvent, dmaResponseConnection,
    fabricFound, dmaFound, view, Chan.sourceValid, Chan.sourcePayload, Expr.eval,
    ← fabricDmaRespValid.read_toSt state.fabric, payload,
    ← dmaRespPop.read_toSt state.dma]

private theorem targetRequestEvent_view (clockEvent : NamedClockEvent)
    (state : FastState) :
    targetRequestEvent clockEvent state =
      system.connectionEvent clockEvent (view state) targetRequestConnection := by
  have fabricFound : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  have serviceFound : system.findIsland? "service" =
      some ⟨"service", "mem_clk", service⟩ := by rfl
  have payload :
      (fabric.toSt state.fabric).regs targetRequest.bits.sourcePayloadName
          (HwPacked.width Request) = fabricTargetReqPayload.read state.fabric := by
    simpa using (fabricTargetReqPayload.read_toSt state.fabric).symm
  simp [targetRequestEvent, System.connectionEvent, targetRequestConnection,
    fabricFound, serviceFound, view, Chan.sourceValid, Chan.sourcePayload, Expr.eval,
    ← fabricTargetReqValid.read_toSt state.fabric, payload,
    ← serviceTargetReqPop.read_toSt state.service]

private theorem targetResponseEvent_view (clockEvent : NamedClockEvent)
    (state : FastState) :
    targetResponseEvent clockEvent state =
      system.connectionEvent clockEvent (view state) targetResponseConnection := by
  have serviceFound : system.findIsland? "service" =
      some ⟨"service", "mem_clk", service⟩ := by rfl
  have fabricFound : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  have payload :
      (service.toSt state.service).regs targetResponse.bits.sourcePayloadName
          (HwPacked.width Response) = serviceTargetRespPayload.read state.service := by
    simpa using (serviceTargetRespPayload.read_toSt state.service).symm
  simp [targetResponseEvent, System.connectionEvent, targetResponseConnection,
    serviceFound, fabricFound, view, Chan.sourceValid, Chan.sourcePayload, Expr.eval,
    ← serviceTargetRespValid.read_toSt state.service, payload,
    ← fabricTargetRespPop.read_toSt state.fabric]

private theorem auditEvent_view (clockEvent : NamedClockEvent)
    (state : FastState) :
    auditEvent clockEvent state =
      system.connectionEvent clockEvent (view state) auditConnection := by
  have serviceFound : system.findIsland? "service" =
      some ⟨"service", "mem_clk", service⟩ := by rfl
  have monitorFound : system.findIsland? "monitor" =
      some ⟨"monitor", "mon_clk", monitor⟩ := by rfl
  have payload :
      (service.toSt state.service).regs audit.bits.sourcePayloadName
          (HwPacked.width CommitRecord) = serviceAuditPayload.read state.service := by
    simpa using (serviceAuditPayload.read_toSt state.service).symm
  simp [auditEvent, System.connectionEvent, auditConnection,
    serviceFound, monitorFound, view, Chan.sourceValid, Chan.sourcePayload, Expr.eval,
    ← serviceAuditValid.read_toSt state.service, payload,
    ← monitorAuditPop.read_toSt state.monitor]

private theorem cpuRequestEvent_semantic (clockEvent : NamedClockEvent)
    (fast : FastState) (semantic : system.State)
    (rep : Represents fast semantic) :
    cpuRequestEvent clockEvent fast =
      system.connectionEvent clockEvent semantic cpuRequestConnection := by
  have cpuFound : system.findIsland? "cpu" =
      some ⟨"cpu", "cpu_fabric_clk", cpu⟩ := by rfl
  have fabricFound : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  have payload :
      (semantic.island "cpu").regs cpuRequest.bits.sourcePayloadName
          (HwPacked.width Request) = cpuReqPayload.read fast.cpu := by
    simpa using (cpuReqPayload.read_eq rep.cpu).symm
  simp [cpuRequestEvent, System.connectionEvent, cpuRequestConnection,
    cpuFound, fabricFound, Chan.sourceValid, Chan.sourcePayload, Expr.eval,
    ← cpuReqValid.read_eq rep.cpu, payload,
    ← fabricCpuReqPop.read_eq rep.fabric]

private theorem cpuResponseEvent_semantic (clockEvent : NamedClockEvent)
    (fast : FastState) (semantic : system.State)
    (rep : Represents fast semantic) :
    cpuResponseEvent clockEvent fast =
      system.connectionEvent clockEvent semantic cpuResponseConnection := by
  have fabricFound : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  have cpuFound : system.findIsland? "cpu" =
      some ⟨"cpu", "cpu_fabric_clk", cpu⟩ := by rfl
  have payload :
      (semantic.island "fabric").regs cpuResponse.bits.sourcePayloadName
          (HwPacked.width Response) = fabricCpuRespPayload.read fast.fabric := by
    simpa using (fabricCpuRespPayload.read_eq rep.fabric).symm
  simp [cpuResponseEvent, System.connectionEvent, cpuResponseConnection,
    fabricFound, cpuFound, Chan.sourceValid, Chan.sourcePayload, Expr.eval,
    ← fabricCpuRespValid.read_eq rep.fabric, payload,
    ← cpuRespPop.read_eq rep.cpu]

private theorem dmaRequestEvent_semantic (clockEvent : NamedClockEvent)
    (fast : FastState) (semantic : system.State)
    (rep : Represents fast semantic) :
    dmaRequestEvent clockEvent fast =
      system.connectionEvent clockEvent semantic dmaRequestConnection := by
  have dmaFound : system.findIsland? "dma" =
      some ⟨"dma", "dma_clk", dma⟩ := by rfl
  have fabricFound : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  have payload :
      (semantic.island "dma").regs dmaRequest.bits.sourcePayloadName
          (HwPacked.width Request) = dmaReqPayload.read fast.dma := by
    simpa using (dmaReqPayload.read_eq rep.dma).symm
  simp [dmaRequestEvent, System.connectionEvent, dmaRequestConnection,
    dmaFound, fabricFound, Chan.sourceValid, Chan.sourcePayload, Expr.eval,
    ← dmaReqValid.read_eq rep.dma, payload,
    ← fabricDmaReqPop.read_eq rep.fabric]

private theorem dmaResponseEvent_semantic (clockEvent : NamedClockEvent)
    (fast : FastState) (semantic : system.State)
    (rep : Represents fast semantic) :
    dmaResponseEvent clockEvent fast =
      system.connectionEvent clockEvent semantic dmaResponseConnection := by
  have fabricFound : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  have dmaFound : system.findIsland? "dma" =
      some ⟨"dma", "dma_clk", dma⟩ := by rfl
  have payload :
      (semantic.island "fabric").regs dmaResponse.bits.sourcePayloadName
          (HwPacked.width Response) = fabricDmaRespPayload.read fast.fabric := by
    simpa using (fabricDmaRespPayload.read_eq rep.fabric).symm
  simp [dmaResponseEvent, System.connectionEvent, dmaResponseConnection,
    fabricFound, dmaFound, Chan.sourceValid, Chan.sourcePayload, Expr.eval,
    ← fabricDmaRespValid.read_eq rep.fabric, payload,
    ← dmaRespPop.read_eq rep.dma]

private theorem targetRequestEvent_semantic (clockEvent : NamedClockEvent)
    (fast : FastState) (semantic : system.State)
    (rep : Represents fast semantic) :
    targetRequestEvent clockEvent fast =
      system.connectionEvent clockEvent semantic targetRequestConnection := by
  have fabricFound : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  have serviceFound : system.findIsland? "service" =
      some ⟨"service", "mem_clk", service⟩ := by rfl
  have payload :
      (semantic.island "fabric").regs targetRequest.bits.sourcePayloadName
          (HwPacked.width Request) = fabricTargetReqPayload.read fast.fabric := by
    simpa using (fabricTargetReqPayload.read_eq rep.fabric).symm
  simp [targetRequestEvent, System.connectionEvent, targetRequestConnection,
    fabricFound, serviceFound, Chan.sourceValid, Chan.sourcePayload, Expr.eval,
    ← fabricTargetReqValid.read_eq rep.fabric, payload,
    ← serviceTargetReqPop.read_eq rep.service]

private theorem targetResponseEvent_semantic (clockEvent : NamedClockEvent)
    (fast : FastState) (semantic : system.State)
    (rep : Represents fast semantic) :
    targetResponseEvent clockEvent fast =
      system.connectionEvent clockEvent semantic targetResponseConnection := by
  have serviceFound : system.findIsland? "service" =
      some ⟨"service", "mem_clk", service⟩ := by rfl
  have fabricFound : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  have payload :
      (semantic.island "service").regs targetResponse.bits.sourcePayloadName
          (HwPacked.width Response) = serviceTargetRespPayload.read fast.service := by
    simpa using (serviceTargetRespPayload.read_eq rep.service).symm
  simp [targetResponseEvent, System.connectionEvent, targetResponseConnection,
    serviceFound, fabricFound, Chan.sourceValid, Chan.sourcePayload, Expr.eval,
    ← serviceTargetRespValid.read_eq rep.service, payload,
    ← fabricTargetRespPop.read_eq rep.fabric]

private theorem auditEvent_semantic (clockEvent : NamedClockEvent)
    (fast : FastState) (semantic : system.State)
    (rep : Represents fast semantic) :
    auditEvent clockEvent fast =
      system.connectionEvent clockEvent semantic auditConnection := by
  have serviceFound : system.findIsland? "service" =
      some ⟨"service", "mem_clk", service⟩ := by rfl
  have monitorFound : system.findIsland? "monitor" =
      some ⟨"monitor", "mon_clk", monitor⟩ := by rfl
  have payload :
      (semantic.island "service").regs audit.bits.sourcePayloadName
          (HwPacked.width CommitRecord) = serviceAuditPayload.read fast.service := by
    simpa using (serviceAuditPayload.read_eq rep.service).symm
  simp [auditEvent, System.connectionEvent, auditConnection,
    serviceFound, monitorFound, Chan.sourceValid, Chan.sourcePayload, Expr.eval,
    ← serviceAuditValid.read_eq rep.service, payload,
    ← monitorAuditPop.read_eq rep.monitor]

private theorem connectionInput_eq_of
    (clockEvent : NamedClockEvent) (fast : FastState)
    (semantic : system.State) (connection : SystemConnection)
    (queueEq : System.connectionQueue (view fast) connection =
      System.connectionQueue semantic connection)
    (eventEq : system.connectionEvent clockEvent (view fast) connection =
      system.connectionEvent clockEvent semantic connection)
    (islandName inputName : String) (inputWidth : Nat) :
    system.connectionInput? clockEvent (view fast) connection
        islandName inputName inputWidth =
      system.connectionInput? clockEvent semantic connection
        islandName inputName inputWidth := by
  simp only [System.connectionInput?]
  rw [queueEq, eventEq]

set_option maxRecDepth 10000 in
private theorem view_input_eq (clockEvent : NamedClockEvent)
    (external : String → InEnv) (fast : FastState) (semantic : system.State)
    (rep : Represents fast semantic) (islandName : String) :
    system.islandInput clockEvent (view fast) external islandName =
      system.islandInput clockEvent semantic external islandName := by
  funext inputName inputWidth
  have cpuReqQueue : System.connectionQueue (view fast) cpuRequestConnection =
      System.connectionQueue semantic cpuRequestConnection := by
    simpa [System.channelState] using (view_cpuRequest fast).trans rep.cpuRequest
  have cpuRespQueue : System.connectionQueue (view fast) cpuResponseConnection =
      System.connectionQueue semantic cpuResponseConnection := by
    simpa [System.channelState] using (view_cpuResponse fast).trans rep.cpuResponse
  have dmaReqQueue : System.connectionQueue (view fast) dmaRequestConnection =
      System.connectionQueue semantic dmaRequestConnection := by
    simpa [System.channelState] using (view_dmaRequest fast).trans rep.dmaRequest
  have dmaRespQueue : System.connectionQueue (view fast) dmaResponseConnection =
      System.connectionQueue semantic dmaResponseConnection := by
    simpa [System.channelState] using (view_dmaResponse fast).trans rep.dmaResponse
  have targetReqQueue : System.connectionQueue (view fast) targetRequestConnection =
      System.connectionQueue semantic targetRequestConnection := by
    simpa [System.channelState] using (view_targetRequest fast).trans rep.targetRequest
  have targetRespQueue : System.connectionQueue (view fast) targetResponseConnection =
      System.connectionQueue semantic targetResponseConnection := by
    simpa [System.channelState] using (view_targetResponse fast).trans rep.targetResponse
  have auditQueue : System.connectionQueue (view fast) auditConnection =
      System.connectionQueue semantic auditConnection := by
    simpa [System.channelState] using (view_audit fast).trans rep.audit
  have cpuReqEvent : system.connectionEvent clockEvent (view fast)
      cpuRequestConnection = system.connectionEvent clockEvent semantic
        cpuRequestConnection :=
    (cpuRequestEvent_view clockEvent fast).symm.trans
      (cpuRequestEvent_semantic clockEvent fast semantic rep)
  have cpuRespEvent : system.connectionEvent clockEvent (view fast)
      cpuResponseConnection = system.connectionEvent clockEvent semantic
        cpuResponseConnection :=
    (cpuResponseEvent_view clockEvent fast).symm.trans
      (cpuResponseEvent_semantic clockEvent fast semantic rep)
  have dmaReqEvent : system.connectionEvent clockEvent (view fast)
      dmaRequestConnection = system.connectionEvent clockEvent semantic
        dmaRequestConnection :=
    (dmaRequestEvent_view clockEvent fast).symm.trans
      (dmaRequestEvent_semantic clockEvent fast semantic rep)
  have dmaRespEvent : system.connectionEvent clockEvent (view fast)
      dmaResponseConnection = system.connectionEvent clockEvent semantic
        dmaResponseConnection :=
    (dmaResponseEvent_view clockEvent fast).symm.trans
      (dmaResponseEvent_semantic clockEvent fast semantic rep)
  have targetReqEvent : system.connectionEvent clockEvent (view fast)
      targetRequestConnection = system.connectionEvent clockEvent semantic
        targetRequestConnection :=
    (targetRequestEvent_view clockEvent fast).symm.trans
      (targetRequestEvent_semantic clockEvent fast semantic rep)
  have targetRespEvent : system.connectionEvent clockEvent (view fast)
      targetResponseConnection = system.connectionEvent clockEvent semantic
        targetResponseConnection :=
    (targetResponseEvent_view clockEvent fast).symm.trans
      (targetResponseEvent_semantic clockEvent fast semantic rep)
  have auditEventEq : system.connectionEvent clockEvent (view fast)
      auditConnection = system.connectionEvent clockEvent semantic auditConnection :=
    (auditEvent_view clockEvent fast).symm.trans
      (auditEvent_semantic clockEvent fast semantic rep)
  have c1 := connectionInput_eq_of clockEvent fast semantic cpuRequestConnection
    cpuReqQueue cpuReqEvent islandName inputName inputWidth
  have c2 := connectionInput_eq_of clockEvent fast semantic cpuResponseConnection
    cpuRespQueue cpuRespEvent islandName inputName inputWidth
  have c3 := connectionInput_eq_of clockEvent fast semantic dmaRequestConnection
    dmaReqQueue dmaReqEvent islandName inputName inputWidth
  have c4 := connectionInput_eq_of clockEvent fast semantic dmaResponseConnection
    dmaRespQueue dmaRespEvent islandName inputName inputWidth
  have c5 := connectionInput_eq_of clockEvent fast semantic targetRequestConnection
    targetReqQueue targetReqEvent islandName inputName inputWidth
  have c6 := connectionInput_eq_of clockEvent fast semantic targetResponseConnection
    targetRespQueue targetRespEvent islandName inputName inputWidth
  have c7 := connectionInput_eq_of clockEvent fast semantic auditConnection
    auditQueue auditEventEq islandName inputName inputWidth
  simp [System.islandInput, System.inputFor, connectionInventory,
    List.findSome?, c1, c2, c3, c4, c5, c6, c7]

theorem advance_represents (inputs : ExternalInputs)
    (clockEvent : NamedClockEvent) (fast : FastState)
    (semantic : system.State) (rep : Represents fast semantic) :
    Represents (advance inputs clockEvent fast)
      (system.advance clockEvent (inputs semantic.time) semantic) := by
  have cpuFound : system.findIsland? "cpu" =
      some ⟨"cpu", "cpu_fabric_clk", cpu⟩ := by rfl
  have dmaFound : system.findIsland? "dma" =
      some ⟨"dma", "dma_clk", dma⟩ := by rfl
  have fabricFound : system.findIsland? "fabric" =
      some ⟨"fabric", "cpu_fabric_clk", fabric⟩ := by rfl
  have serviceFound : system.findIsland? "service" =
      some ⟨"service", "mem_clk", service⟩ := by rfl
  have monitorFound : system.findIsland? "monitor" =
      some ⟨"monitor", "mon_clk", monitor⟩ := by rfl
  have cpuInput := view_input_eq clockEvent (inputs semantic.time)
    fast semantic rep "cpu"
  have dmaInput := view_input_eq clockEvent (inputs semantic.time)
    fast semantic rep "dma"
  have fabricInput := view_input_eq clockEvent (inputs semantic.time)
    fast semantic rep "fabric"
  have serviceInput := view_input_eq clockEvent (inputs semantic.time)
    fast semantic rep "service"
  have monitorInput := view_input_eq clockEvent (inputs semantic.time)
    fast semantic rep "monitor"
  have cpuNext : Agree cpu (advance inputs clockEvent fast).cpu
      ((system.advance clockEvent (inputs semantic.time) semantic).island "cpu") := by
    by_cases tick : clockEvent.fires "cpu_fabric_clk" = true
    · simp only [advance, rep.time, tick, if_true]
      rw [System.advance_island_ticked system clockEvent (inputs semantic.time)
        semantic ⟨"cpu", "cpu_fabric_clk", cpu⟩ cpuFound tick]
      rw [← cpuInput]
      exact cpuSim.cycleOpen_eq _ _ _ rep.cpu
    · have unticked : clockEvent.fires "cpu_fabric_clk" = false :=
        Bool.eq_false_of_not_eq_true tick
      simp only [advance, rep.time, unticked, if_false]
      rw [System.advance_island_unticked system clockEvent (inputs semantic.time)
        semantic ⟨"cpu", "cpu_fabric_clk", cpu⟩ cpuFound unticked]
      exact rep.cpu
  have dmaNext : Agree dma (advance inputs clockEvent fast).dma
      ((system.advance clockEvent (inputs semantic.time) semantic).island "dma") := by
    by_cases tick : clockEvent.fires "dma_clk" = true
    · simp only [advance, rep.time, tick, if_true]
      rw [System.advance_island_ticked system clockEvent (inputs semantic.time)
        semantic ⟨"dma", "dma_clk", dma⟩ dmaFound tick]
      rw [← dmaInput]
      exact dmaSim.cycleOpen_eq _ _ _ rep.dma
    · have unticked : clockEvent.fires "dma_clk" = false :=
        Bool.eq_false_of_not_eq_true tick
      simp only [advance, rep.time, unticked, if_false]
      rw [System.advance_island_unticked system clockEvent (inputs semantic.time)
        semantic ⟨"dma", "dma_clk", dma⟩ dmaFound unticked]
      exact rep.dma
  have fabricNext : Agree fabric (advance inputs clockEvent fast).fabric
      ((system.advance clockEvent (inputs semantic.time) semantic).island "fabric") := by
    by_cases tick : clockEvent.fires "cpu_fabric_clk" = true
    · simp only [advance, rep.time, tick, if_true]
      rw [System.advance_island_ticked system clockEvent (inputs semantic.time)
        semantic ⟨"fabric", "cpu_fabric_clk", fabric⟩ fabricFound tick]
      rw [← fabricInput]
      exact fabricSim.cycleOpen_eq _ _ _ rep.fabric
    · have unticked : clockEvent.fires "cpu_fabric_clk" = false :=
        Bool.eq_false_of_not_eq_true tick
      simp only [advance, rep.time, unticked, if_false]
      rw [System.advance_island_unticked system clockEvent (inputs semantic.time)
        semantic ⟨"fabric", "cpu_fabric_clk", fabric⟩ fabricFound unticked]
      exact rep.fabric
  have serviceNext : Agree service (advance inputs clockEvent fast).service
      ((system.advance clockEvent (inputs semantic.time) semantic).island "service") := by
    by_cases tick : clockEvent.fires "mem_clk" = true
    · simp only [advance, rep.time, tick, if_true]
      rw [System.advance_island_ticked system clockEvent (inputs semantic.time)
        semantic ⟨"service", "mem_clk", service⟩ serviceFound tick]
      rw [← serviceInput]
      exact serviceSim.cycleOpen_eq _ _ _ rep.service
    · have unticked : clockEvent.fires "mem_clk" = false :=
        Bool.eq_false_of_not_eq_true tick
      simp only [advance, rep.time, unticked, if_false]
      rw [System.advance_island_unticked system clockEvent (inputs semantic.time)
        semantic ⟨"service", "mem_clk", service⟩ serviceFound unticked]
      exact rep.service
  have monitorNext : Agree monitor (advance inputs clockEvent fast).monitor
      ((system.advance clockEvent (inputs semantic.time) semantic).island "monitor") := by
    by_cases tick : clockEvent.fires "mon_clk" = true
    · simp only [advance, rep.time, tick, if_true]
      rw [System.advance_island_ticked system clockEvent (inputs semantic.time)
        semantic ⟨"monitor", "mon_clk", monitor⟩ monitorFound tick]
      rw [← monitorInput]
      exact monitorSim.cycleOpen_eq _ _ _ rep.monitor
    · have unticked : clockEvent.fires "mon_clk" = false :=
        Bool.eq_false_of_not_eq_true tick
      simp only [advance, rep.time, unticked, if_false]
      rw [System.advance_island_unticked system clockEvent (inputs semantic.time)
        semantic ⟨"monitor", "mon_clk", monitor⟩ monitorFound unticked]
      exact rep.monitor
  refine
    { cpu := cpuNext
      dma := dmaNext
      fabric := fabricNext
      service := serviceNext
      monitor := monitorNext
      cpuRequest := ?_
      cpuResponse := ?_
      dmaRequest := ?_
      dmaResponse := ?_
      targetRequest := ?_
      targetResponse := ?_
      audit := ?_
      time := ?_ }
  · simp only [advance]
    rw [System.channelState_advance system clockEvent (inputs semantic.time)
      semantic cpuRequestConnection (by rfl)]
    simp only [System.connectionResult]
    rw [← cpuRequestEvent_semantic clockEvent fast semantic rep]
    have queueEq : fast.cpuRequest =
        System.connectionQueue semantic cpuRequestConnection := by
      simpa [System.channelState] using rep.cpuRequest
    rw [← queueEq]
    rfl
  · simp only [advance]
    rw [System.channelState_advance system clockEvent (inputs semantic.time)
      semantic cpuResponseConnection (by rfl)]
    simp only [System.connectionResult]
    rw [← cpuResponseEvent_semantic clockEvent fast semantic rep]
    have queueEq : fast.cpuResponse =
        System.connectionQueue semantic cpuResponseConnection := by
      simpa [System.channelState] using rep.cpuResponse
    rw [← queueEq]
    rfl
  · simp only [advance]
    rw [System.channelState_advance system clockEvent (inputs semantic.time)
      semantic dmaRequestConnection (by rfl)]
    simp only [System.connectionResult]
    rw [← dmaRequestEvent_semantic clockEvent fast semantic rep]
    have queueEq : fast.dmaRequest =
        System.connectionQueue semantic dmaRequestConnection := by
      simpa [System.channelState] using rep.dmaRequest
    rw [← queueEq]
    rfl
  · simp only [advance]
    rw [System.channelState_advance system clockEvent (inputs semantic.time)
      semantic dmaResponseConnection (by rfl)]
    simp only [System.connectionResult]
    rw [← dmaResponseEvent_semantic clockEvent fast semantic rep]
    have queueEq : fast.dmaResponse =
        System.connectionQueue semantic dmaResponseConnection := by
      simpa [System.channelState] using rep.dmaResponse
    rw [← queueEq]
    rfl
  · simp only [advance]
    rw [System.channelState_advance system clockEvent (inputs semantic.time)
      semantic targetRequestConnection (by rfl)]
    simp only [System.connectionResult]
    rw [← targetRequestEvent_semantic clockEvent fast semantic rep]
    have queueEq : fast.targetRequest =
        System.connectionQueue semantic targetRequestConnection := by
      simpa [System.channelState] using rep.targetRequest
    rw [← queueEq]
    rfl
  · simp only [advance]
    rw [System.channelState_advance system clockEvent (inputs semantic.time)
      semantic targetResponseConnection (by rfl)]
    simp only [System.connectionResult]
    rw [← targetResponseEvent_semantic clockEvent fast semantic rep]
    have queueEq : fast.targetResponse =
        System.connectionQueue semantic targetResponseConnection := by
      simpa [System.channelState] using rep.targetResponse
    rw [← queueEq]
    rfl
  · simp only [advance]
    rw [System.channelState_advance system clockEvent (inputs semantic.time)
      semantic auditConnection (by rfl)]
    simp only [System.connectionResult]
    rw [← auditEvent_semantic clockEvent fast semantic rep]
    have queueEq : fast.audit =
        System.connectionQueue semantic auditConnection := by
      simpa [System.channelState] using rep.audit
    rw [← queueEq]
    rfl
  · simp [advance, System.advance, rep.time]

private theorem run_represents (inputs : ExternalInputs)
    (fast : FastState) (semantic : system.State)
    (events : List NamedClockEvent) (rep : Represents fast semantic) :
    Represents (run inputs fast events)
      (system.runEventsFrom inputs semantic events) := by
  induction events generalizing fast semantic with
  | nil => exact rep
  | cons next rest ih =>
      simp only [run, System.runEventsFrom]
      apply ih
      exact advance_represents inputs next fast semantic rep

/-- Every compact campaign replay is pointwise related to Loom's public
named-clock semantics for the identical external inputs and event list. -/
theorem reset_run_represents (inputs : ExternalInputs)
    (events : List NamedClockEvent) :
    Represents (run inputs reset events)
      (system.runEventsFrom inputs system.reset events) :=
  run_represents inputs reset system.reset events reset_represents

private def cpuCounter (name : String)
    (ready : (FastEval.regSlot? cpu (Reg.mk name : Reg 32)).isSome = true) :=
  mustSlot cpu (Reg.mk name : Reg 32) ready

private def dmaCounter (name : String)
    (ready : (FastEval.regSlot? dma (Reg.mk name : Reg 32)).isSome = true) :=
  mustSlot dma (Reg.mk name : Reg 32) ready

private def fabricCounter (name : String)
    (ready : (FastEval.regSlot? fabric (Reg.mk name : Reg 32)).isSome = true) :=
  mustSlot fabric (Reg.mk name : Reg 32) ready

private def serviceCounter (name : String)
    (ready : (FastEval.regSlot? service (Reg.mk name : Reg 32)).isSome = true) :=
  mustSlot service (Reg.mk name : Reg 32) ready

private def monitorCounter (name : String)
    (ready : (FastEval.regSlot? monitor (Reg.mk name : Reg 32)).isSome = true) :=
  mustSlot monitor (Reg.mk name : Reg 32) ready

structure Metrics where
  cpuStaged : Nat
  cpuAccepted : Nat
  cpuResponses : Nat
  cpuDigest : Nat
  cpuRequestStalls : Nat
  cpuError : Nat
  dmaStaged : Nat
  dmaAccepted : Nat
  dmaResponses : Nat
  dmaDigest : Nat
  dmaRequestStalls : Nat
  dmaError : Nat
  cpuGrants : Nat
  dmaGrants : Nat
  totalGrants : Nat
  routed : Nat
  contentionTicks : Nat
  targetStalls : Nat
  responseStalls : Nat
  doubleGrantError : Nat
  commits : Nat
  serviceRequestStalls : Nat
  serviceResponseStalls : Nat
  records : Nat
  auditDigest : Nat
  monitorError : Nat
  auditStalls : Nat
  channelOccupancy : List Nat
  deriving Repr

def metrics (state : FastState) : Metrics :=
  { cpuStaged := (cpuCounter "requests_staged" (by decide)).readNat state.cpu
    cpuAccepted := (cpuCounter "requests_accepted" (by decide)).readNat state.cpu
    cpuResponses := (cpuCounter "responses_received" (by decide)).readNat state.cpu
    cpuDigest := (cpuCounter "response_digest" (by decide)).readNat state.cpu
    cpuRequestStalls := (cpuCounter "request_stalls" (by decide)).readNat state.cpu
    cpuError := (mustSlot cpu (Reg.mk "sticky_error" : Reg 1) (by decide)).readNat state.cpu
    dmaStaged := (dmaCounter "requests_staged" (by decide)).readNat state.dma
    dmaAccepted := (dmaCounter "requests_accepted" (by decide)).readNat state.dma
    dmaResponses := (dmaCounter "responses_received" (by decide)).readNat state.dma
    dmaDigest := (dmaCounter "response_digest" (by decide)).readNat state.dma
    dmaRequestStalls := (dmaCounter "request_stalls" (by decide)).readNat state.dma
    dmaError := (mustSlot dma (Reg.mk "sticky_error" : Reg 1) (by decide)).readNat state.dma
    cpuGrants := (fabricCounter "cpu_grants" (by decide)).readNat state.fabric
    dmaGrants := (fabricCounter "dma_grants" (by decide)).readNat state.fabric
    totalGrants := (fabricCounter "total_grants" (by decide)).readNat state.fabric
    routed := (fabricCounter "responses_routed" (by decide)).readNat state.fabric
    contentionTicks := (fabricCounter "contention_ticks" (by decide)).readNat state.fabric
    targetStalls := (fabricCounter "target_stalls" (by decide)).readNat state.fabric
    responseStalls := (fabricCounter "response_stalls" (by decide)).readNat state.fabric
    doubleGrantError := (mustSlot fabric (Reg.mk "double_grant_error" : Reg 1)
      (by decide)).readNat state.fabric
    commits := (serviceCounter "commits" (by decide)).readNat state.service
    serviceRequestStalls := (serviceCounter "request_stalls" (by decide)).readNat state.service
    serviceResponseStalls := (serviceCounter "response_stalls" (by decide)).readNat state.service
    records := (monitorCounter "records" (by decide)).readNat state.monitor
    auditDigest := (monitorCounter "audit_digest" (by decide)).readNat state.monitor
    monitorError := (mustSlot monitor (Reg.mk "sticky_error" : Reg 1)
      (by decide)).readNat state.monitor
    auditStalls := (serviceCounter "audit_stalls" (by decide)).readNat state.service
    channelOccupancy := [state.cpuRequest.length, state.cpuResponse.length,
      state.dmaRequest.length, state.dmaResponse.length, state.targetRequest.length,
      state.targetResponse.length, state.audit.length] }

def complete (observed : Metrics) : Bool :=
  observed.cpuStaged == transactionCount &&
  observed.cpuAccepted == transactionCount &&
  observed.cpuResponses == transactionCount &&
  observed.dmaStaged == transactionCount &&
  observed.dmaAccepted == transactionCount &&
  observed.dmaResponses == transactionCount &&
  observed.cpuGrants == transactionCount &&
  observed.dmaGrants == transactionCount &&
  observed.totalGrants == 2 * transactionCount &&
  observed.routed == 2 * transactionCount &&
  observed.commits == 2 * transactionCount &&
  observed.records == 2 * transactionCount &&
  observed.cpuError == 0 && observed.dmaError == 0 &&
  observed.monitorError == 0 && observed.doubleGrantError == 0 &&
  observed.cpuDigest == 0 && observed.dmaDigest == 0 && observed.auditDigest == 0 &&
  observed.auditDigest == (observed.cpuDigest ^^^ observed.dmaDigest) &&
  observed.channelOccupancy.all (· == 0)

structure StageFlags where
  clientHeld : Bool
  requestFifo : Bool
  arbiterSelected : Bool
  targetFifo : Bool
  committedResponsePending : Bool
  responseFifo : Bool
  fullBackpressured : Bool
  trafficBothDirections : Bool
  empty : Bool
  deriving Repr

def stageFlags (state : FastState) : StageFlags :=
  let cpuActive := (mustSlot cpu (Reg.mk "active" : Reg 1) (by decide)).readNat state.cpu
  let dmaActive := (mustSlot dma (Reg.mk "active" : Reg 1) (by decide)).readNat state.dma
  let outstanding := (mustSlot fabric (Reg.mk "outstanding" : Reg 1)
    (by decide)).readNat state.fabric
  { clientHeld := (cpuActive != 0 && cpuReqValid.readNat state.cpu != 0) ||
      (dmaActive != 0 && dmaReqValid.readNat state.dma != 0)
    requestFifo := !state.cpuRequest.isEmpty || !state.dmaRequest.isEmpty
    arbiterSelected := outstanding != 0
    targetFifo := !state.targetRequest.isEmpty
    committedResponsePending := serviceTargetRespValid.readNat state.service != 0 ||
      serviceAuditValid.readNat state.service != 0
    responseFifo := !state.cpuResponse.isEmpty || !state.dmaResponse.isEmpty
    fullBackpressured := state.audit.length == audit.bits.depth &&
      (serviceCounter "audit_stalls" (by decide)).readNat state.service != 0
    trafficBothDirections :=
      (!state.cpuRequest.isEmpty || !state.dmaRequest.isEmpty ||
        !state.targetRequest.isEmpty) &&
      (!state.cpuResponse.isEmpty || !state.dmaResponse.isEmpty ||
        !state.targetResponse.isEmpty)
    empty := [state.cpuRequest, state.dmaRequest, state.targetRequest].all List.isEmpty &&
      [state.cpuResponse, state.dmaResponse, state.targetResponse].all List.isEmpty &&
      state.audit.isEmpty && outstanding == 0 }

end Machines.Multiclock.SoCFabricGauntlet.Execution
