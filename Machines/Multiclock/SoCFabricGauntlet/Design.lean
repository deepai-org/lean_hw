-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SoCFabricGauntlet.Protocol
import Loom.Hw.System

/-!
# SoC Fabric Gauntlet design

Five ordinary synchronous islands implement two one-outstanding clients, a
round-robin fabric, a 256x32 register service, and a lossless audit monitor.
Only typed `PackedChan` routes cross island boundaries.
-/

namespace Machines.Multiclock.SoCFabricGauntlet

open Loom.Hw

def transactionCount : Nat := 256

def requestExpr (client : BitVec 1) (sequence : Expr 32) : PackedExpr Request :=
  .ofFields <| .cons (.lit client) <| .cons (.slice sequence 0 4) <|
    .cons (.slice sequence 4 1) <| .cons (.slice sequence 0 8) <|
      .cons (.xor sequence (.lit (if client = 0 then 0x13579bdf else 0x2468ace0))) <|
        .cons (.slice sequence 0 4) .nil

def responseExpr (request : PackedExpr Request)
    (result : Expr 32) : PackedExpr Response :=
  .ofFields <| .cons (Request.clientField.read request) <|
    .cons (Request.tagField.read request) <| .cons result <| .cons (.lit 0#1) .nil

def commitExpr (request : PackedExpr Request)
    (result : Expr 32) : PackedExpr CommitRecord :=
  .ofFields <| .cons (Request.clientField.read request) <|
    .cons (Request.tagField.read request) <|
      .cons (Request.addrField.read request) <|
        .cons (Request.writeField.read request) <| .cons result .nil

def maskedWord (old data : Expr 32) (mask : Expr 4) : Expr 32 :=
  Expr.concat
    (.mux (.slice mask 3 1) (.slice data 24 8) (.slice old 24 8)) <|
  Expr.concat
    (.mux (.slice mask 2 1) (.slice data 16 8) (.slice old 16 8)) <|
  Expr.concat
    (.mux (.slice mask 1 1) (.slice data 8 8) (.slice old 8 8))
    (.mux (.slice mask 0 1) (.slice data 0 8) (.slice old 0 8))

def clientBody (name : String) (client : BitVec 1)
    (requests : PackedChan Request) (responses : PackedChan Response) : Design where
  name := name
  regs := [
    ⟨"sequence", 32, 0⟩, ⟨"active", 1, 0⟩, ⟨"active_tag", 4, 0⟩,
    ⟨"requests_staged", 32, 0⟩, ⟨"requests_accepted", 32, 0⟩,
    ⟨"responses_received", 32, 0⟩, ⟨"response_digest", 32, 0⟩,
    ⟨"request_stalls", 32, 0⟩, ⟨"sticky_error", 1, 0⟩,
    ⟨"progress", 2, 0⟩]
  mems := []
  rules := [
    ⟨"progress", .write 2 "progress" (.lit 1)⟩,
    ⟨"request_accepted", .ite requests.bits.sourceAccepted
      (.write 32 "requests_accepted"
        (.add (.reg 32 "requests_accepted") (.lit 1))) .skip⟩,
    ⟨"consume_response", .ite
      (.and (.not (.reg 1 "hold_response"))
        (.and (.reg 1 "active") responses.canDeq))
      (.seq (.ite
          (.or (.not (.eq (Response.clientField.read responses.deq) (.lit client)))
            (.or (.not (.eq (Response.tagField.read responses.deq)
                (.reg 4 "active_tag")))
              (Response.errorField.read responses.deq)))
          (.write 1 "sticky_error" (.lit 1)) .skip)
        (.seq (.write 32 "response_digest"
            (.xor (.reg 32 "response_digest")
              (Response.dataField.read responses.deq)))
          (.seq (.write 32 "responses_received"
              (.add (.reg 32 "responses_received") (.lit 1)))
            (.seq (.write 1 "active" (.lit 0)) responses.pop)))) .skip⟩,
    ⟨"issue_request", .ite
      (.and (.not (.reg 1 "hold_issue"))
        (.and (.not (.reg 1 "active"))
          (.ult (.reg 32 "sequence")
            (.reg 32 "transaction_limit"))))
      (.ite requests.canEnq
        (.seq (requests.enq (requestExpr client (.reg 32 "sequence")))
          (.seq (.write 4 "active_tag" (.slice (.reg 32 "sequence") 0 4))
            (.seq (.write 1 "active" (.lit 1))
              (.seq (.write 32 "sequence"
                  (.add (.reg 32 "sequence") (.lit 1)))
                (.write 32 "requests_staged"
                  (.add (.reg 32 "requests_staged") (.lit 1)))))))
        (.write 32 "request_stalls"
          (.add (.reg 32 "request_stalls") (.lit 1)))) .skip⟩]
  inputs := [⟨"hold_issue", 1⟩, ⟨"hold_response", 1⟩,
    ⟨"transaction_limit", 32⟩]
  outputs := ["sequence", "active", "active_tag", "requests_staged",
    "requests_accepted", "responses_received", "response_digest",
    "request_stalls", "sticky_error", "progress"]

def cpuBody : Design := clientBody "soc_fabric_cpu" 0#1 cpuRequest cpuResponse
def dmaBody : Design := clientBody "soc_fabric_dma" 1#1 dmaRequest dmaResponse

def fabricGrant (incoming : PackedChan Request) (client : BitVec 1)
    (nextPriority : BitVec 1) : Act :=
  .seq (targetRequest.enq incoming.deq)
    (.seq incoming.pop
      (.seq (.write 1 "outstanding" (.lit 1))
        (.seq (.write 1 "route" (.lit client))
          (.seq (.write 1 "round_robin" (.lit nextPriority))
            (.seq (.write 32 (if client = 0 then "cpu_grants" else "dma_grants")
                (.add (.reg 32 (if client = 0 then "cpu_grants" else "dma_grants"))
                  (.lit 1)))
              (.write 32 "total_grants"
                (.add (.reg 32 "total_grants") (.lit 1))))))))

def fabricRouteResponseRule : Rule :=
  ⟨"route_response", .ite
    (.and (.reg 1 "outstanding") targetResponse.canDeq)
    (.ite (.eq (.reg 1 "route") (.lit 0#1))
      (.ite cpuResponse.canEnq
        (.seq (cpuResponse.enq targetResponse.deq)
          (.seq targetResponse.pop
            (.seq (.write 1 "outstanding" (.lit 0))
              (.write 32 "responses_routed"
                (.add (.reg 32 "responses_routed") (.lit 1))))))
        (.write 32 "response_stalls"
          (.add (.reg 32 "response_stalls") (.lit 1))))
      (.ite dmaResponse.canEnq
        (.seq (dmaResponse.enq targetResponse.deq)
          (.seq targetResponse.pop
            (.seq (.write 1 "outstanding" (.lit 0))
              (.write 32 "responses_routed"
                (.add (.reg 32 "responses_routed") (.lit 1))))))
        (.write 32 "response_stalls"
          (.add (.reg 32 "response_stalls") (.lit 1))))) .skip⟩

def fabricArbitrateRule : Rule :=
  ⟨"arbitrate", .ite
    (.and (.not (.reg 1 "hold_arbitration")) (.not (.reg 1 "outstanding")))
    (.ite targetRequest.canEnq
      (.ite (.and cpuRequest.canDeq dmaRequest.canDeq)
        (.ite (.eq (.reg 1 "round_robin") (.lit 0#1))
          (fabricGrant cpuRequest 0#1 1#1)
          (fabricGrant dmaRequest 1#1 0#1))
        (.ite cpuRequest.canDeq (fabricGrant cpuRequest 0#1 1#1)
          (.ite dmaRequest.canDeq (fabricGrant dmaRequest 1#1 0#1) .skip)))
      (.ite (.or cpuRequest.canDeq dmaRequest.canDeq)
        (.write 32 "target_stalls"
          (.add (.reg 32 "target_stalls") (.lit 1))) .skip)) .skip⟩

def fabricBody : Design where
  name := "soc_fabric_arbiter"
  regs := [
    ⟨"round_robin", 1, 0⟩, ⟨"outstanding", 1, 0⟩, ⟨"route", 1, 0⟩,
    ⟨"cpu_grants", 32, 0⟩, ⟨"dma_grants", 32, 0⟩,
    ⟨"total_grants", 32, 0⟩, ⟨"responses_routed", 32, 0⟩,
    ⟨"contention_ticks", 32, 0⟩, ⟨"target_stalls", 32, 0⟩,
    ⟨"response_stalls", 32, 0⟩, ⟨"double_grant_error", 1, 0⟩,
    ⟨"progress", 2, 0⟩]
  mems := []
  rules := [
    ⟨"progress", .write 2 "progress" (.lit 1)⟩,
    ⟨"contention", .ite (.and cpuRequest.canDeq dmaRequest.canDeq)
      (.write 32 "contention_ticks"
        (.add (.reg 32 "contention_ticks") (.lit 1))) .skip⟩,
    fabricRouteResponseRule,
    fabricArbitrateRule]
  inputs := [⟨"hold_arbitration", 1⟩]
  outputs := ["round_robin", "outstanding", "route", "cpu_grants",
    "dma_grants", "total_grants", "responses_routed", "contention_ticks",
    "target_stalls", "response_stalls", "double_grant_error", "progress"]

def registerFile : Mem 8 32 := ⟨"register_file"⟩

def serviceCommit : Act :=
  let request := targetRequest.deq
  let old := registerFile.rd (Request.addrField.read request)
  let updated := maskedWord old (Request.dataField.read request)
    (Request.maskField.read request)
  let result := .mux (Request.writeField.read request) updated old
  .seq (.ite (Request.writeField.read request)
      (registerFile.write 0 (Request.addrField.read request) result) .skip)
    (.seq (targetResponse.enq (responseExpr request result))
      (.seq (audit.enq (commitExpr request result))
        (.seq targetRequest.pop
          (.write 32 "commits" (.add (.reg 32 "commits") (.lit 1))))))

def serviceCommitRule : Rule :=
  ⟨"commit", .ite targetRequest.canDeq
    (.ite targetResponse.canEnq
      (.ite audit.canEnq serviceCommit
        (.write 32 "audit_stalls"
          (.add (.reg 32 "audit_stalls") (.lit 1))))
      (.write 32 "response_stalls"
        (.add (.reg 32 "response_stalls") (.lit 1))))
    (.write 32 "request_stalls"
      (.add (.reg 32 "request_stalls") (.lit 1)))⟩

def serviceBody : Design where
  name := "soc_fabric_register_service"
  regs := [⟨"commits", 32, 0⟩, ⟨"request_stalls", 32, 0⟩,
    ⟨"response_stalls", 32, 0⟩, ⟨"audit_stalls", 32, 0⟩,
    ⟨"progress", 2, 0⟩]
  mems := [registerFile.decl]
  rules := [
    ⟨"progress", .write 2 "progress" (.lit 1)⟩,
    serviceCommitRule]
  outputs := ["commits", "request_stalls", "response_stalls", "audit_stalls",
    "progress"]

def monitorMemory : Mem 8 32 := ⟨"monitor_memory"⟩

private def monitorConsume : Act :=
  let record := audit.deq
  let old := monitorMemory.rd (CommitRecord.addrField.read record)
  let expectedSequence := .mux (CommitRecord.clientField.read record)
    (.reg 32 "dma_expected_sequence") (.reg 32 "cpu_expected_sequence")
  let expectedWrite := .slice expectedSequence 4 1
  let expectedData := .xor expectedSequence
    (.mux (CommitRecord.clientField.read record) (.lit 0x2468ace0) (.lit 0x13579bdf))
  let expectedMask := .slice expectedSequence 0 4
  let expectedResult := .mux expectedWrite
    (maskedWord old expectedData expectedMask) old
  let mismatch := .or
    (.not (.eq (CommitRecord.tagField.read record) (.slice expectedSequence 0 4))) <|
    .or (.not (.eq (CommitRecord.addrField.read record) (.slice expectedSequence 0 8))) <|
    .or (.not (.eq (CommitRecord.writeField.read record) expectedWrite))
      (.not (.eq (CommitRecord.resultField.read record) expectedResult))
  .seq (.ite
      mismatch
      (.write 1 "sticky_error" (.lit 1)) .skip)
    (.seq (.ite expectedWrite
        (monitorMemory.write 0 (CommitRecord.addrField.read record)
          expectedResult) .skip)
      (.seq (.write 32 "audit_digest"
          (.xor (.reg 32 "audit_digest")
            (CommitRecord.resultField.read record)))
        (.seq (.write 32 "expected_digest"
            (.xor (.reg 32 "expected_digest") expectedResult))
          (.seq (.ite (CommitRecord.clientField.read record)
              (.write 32 "dma_expected_sequence"
                (.add (.reg 32 "dma_expected_sequence") (.lit 1)))
              (.write 32 "cpu_expected_sequence"
                (.add (.reg 32 "cpu_expected_sequence") (.lit 1))))
            (.seq (.write 32 "records"
                (.add (.reg 32 "records") (.lit 1))) audit.pop)))))

def monitorBody : Design where
  name := "soc_fabric_audit_monitor"
  regs := [⟨"records", 32, 0⟩, ⟨"audit_digest", 32, 0⟩,
    ⟨"expected_digest", 32, 0⟩, ⟨"cpu_expected_sequence", 32, 0⟩,
    ⟨"dma_expected_sequence", 32, 0⟩,
    ⟨"sticky_error", 1, 0⟩, ⟨"progress", 2, 0⟩]
  mems := [monitorMemory.decl]
  rules := [
    ⟨"progress", .write 2 "progress" (.lit 1)⟩,
    ⟨"consume", .ite audit.canDeq monitorConsume .skip⟩]
  outputs := ["records", "audit_digest", "expected_digest",
    "cpu_expected_sequence", "dma_expected_sequence", "sticky_error", "progress"]

def cpu : Design := cpuRequest.withSource (cpuResponse.withSink cpuBody)
def dma : Design := dmaRequest.withSource (dmaResponse.withSink dmaBody)
def fabric : Design := targetRequest.withSource <| targetResponse.withSink <|
  cpuRequest.withSink <| dmaRequest.withSink <|
    cpuResponse.withSource <| dmaResponse.withSource fabricBody
def service : Design := targetRequest.withSink <|
  targetResponse.withSource <| audit.withSource serviceBody
def monitor : Design := audit.withSink monitorBody

def builder : SystemBuilder :=
  System.empty
    |>.addErasedDesignIsland "cpu" cpu (clock := "cpu_fabric_clk")
    |>.addErasedDesignIsland "dma" dma (clock := "dma_clk")
    |>.addErasedDesignIsland "fabric" fabric (clock := "cpu_fabric_clk")
    |>.addErasedDesignIsland "service" service (clock := "mem_clk")
    |>.addErasedDesignIsland "monitor" monitor (clock := "mon_clk")
    |>.connect cpuRequest.bits (source := "cpu") (sink := "fabric")
    |>.connect cpuResponse.bits (source := "fabric") (sink := "cpu")
    |>.connect dmaRequest.bits (source := "dma") (sink := "fabric")
    |>.connect dmaResponse.bits (source := "fabric") (sink := "dma")
    |>.connect targetRequest.bits (source := "fabric") (sink := "service")
    |>.connect targetResponse.bits (source := "service") (sink := "fabric")
    |>.connect audit.bits (source := "service") (sink := "monitor")
    |>.withClockRel .asynchronous

def system : System := builder.certify (by decide)

def cpuRequestConnection : SystemConnection :=
  ⟨HwPacked.width Request, cpuRequest.bits, "cpu", "fabric"⟩
def cpuResponseConnection : SystemConnection :=
  ⟨HwPacked.width Response, cpuResponse.bits, "fabric", "cpu"⟩
def dmaRequestConnection : SystemConnection :=
  ⟨HwPacked.width Request, dmaRequest.bits, "dma", "fabric"⟩
def dmaResponseConnection : SystemConnection :=
  ⟨HwPacked.width Response, dmaResponse.bits, "fabric", "dma"⟩
def targetRequestConnection : SystemConnection :=
  ⟨HwPacked.width Request, targetRequest.bits, "fabric", "service"⟩
def targetResponseConnection : SystemConnection :=
  ⟨HwPacked.width Response, targetResponse.bits, "service", "fabric"⟩
def auditConnection : SystemConnection :=
  ⟨HwPacked.width CommitRecord, audit.bits, "service", "monitor"⟩

theorem connectionInventory : system.connections =
    [cpuRequestConnection, cpuResponseConnection, dmaRequestConnection,
      dmaResponseConnection, targetRequestConnection, targetResponseConnection,
      auditConnection] := by
  rfl

end Machines.Multiclock.SoCFabricGauntlet
