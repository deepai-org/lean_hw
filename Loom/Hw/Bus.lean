-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Stream

/-!
# Typed same-clock request/response buses

A bus is a pair of ordinary ready/valid streams. The Lean types retain the
clock domain and the nominal request and response payloads, while `Protocol`
states the transaction-level ordering and capacity contract. Protocol names
remain library values; this module adds no bus-specific core semantics or DSL
keywords.
-/

namespace Loom.Hw

universe u v

namespace Bus

variable {Req Rsp : Type u}

/-- Whether a response may be accepted in the same cycle as its request when
there was no older request. This is an observable protocol choice. -/
inductive ResponseTiming where
  | registered
  | combinational
  deriving Repr, DecidableEq, BEq

/-- Transaction-level contract for an ordered request/response protocol.
`matches` may express tags, operation kinds, or any other semantic relation;
the supplied decision procedure is used by executable monitors. -/
structure Protocol (Req Rsp : Type u) where
  name : String
  maxOutstanding : Nat
  responseTiming : ResponseTiming := .registered
  relates : Req → Rsp → Prop
  relatesDecidable : DecidableRel relates

/-- Initiator-facing ports. Requests travel outward and responses inward. -/
structure InitiatorPorts (δ : Type v) (Req Rsp : Type u)
    [ClockDomain δ] [HwPacked Req] [HwPacked Rsp] where
  request : Stream.SourcePorts δ Req
  response : Stream.SinkPorts δ Rsp

/-- Target-facing dual of `InitiatorPorts`. -/
structure TargetPorts (δ : Type v) (Req Rsp : Type u)
    [ClockDomain δ] [HwPacked Req] [HwPacked Rsp] where
  request : Stream.SinkPorts δ Req
  response : Stream.SourcePorts δ Rsp

def initiatorPorts {δ : Type v} {Req Rsp : Type u}
    [ClockDomain δ] [HwPacked Req] [HwPacked Rsp]
    (requestType responseType : String) : InitiatorPorts δ Req Rsp :=
  ⟨Stream.sourcePorts "req" requestType,
    Stream.sinkPorts "rsp" responseType⟩

def targetPorts {δ : Type v} {Req Rsp : Type u}
    [ClockDomain δ] [HwPacked Req] [HwPacked Rsp]
    (requestType responseType : String) : TargetPorts δ Req Rsp :=
  ⟨Stream.sinkPorts "req" requestType,
    Stream.sourcePorts "rsp" responseType⟩

def InitiatorPorts.decls {δ : Type v} {Req Rsp : Type u}
    [ClockDomain δ] [HwPacked Req] [HwPacked Rsp]
    (ports : InitiatorPorts δ Req Rsp) : List PortDecl :=
  ports.request.decls ++ ports.response.decls

def TargetPorts.decls {δ : Type v} {Req Rsp : Type u}
    [ClockDomain δ] [HwPacked Req] [HwPacked Rsp]
    (ports : TargetPorts δ Req Rsp) : List PortDecl :=
  ports.request.decls ++ ports.response.decls

structure InitiatorEndpoint (δ : Type v) (Req Rsp : Type u)
    [ClockDomain δ] [HwPacked Req] [HwPacked Rsp] where
  request : Stream.SourceEndpoint δ Req
  response : Stream.SinkEndpoint δ Rsp

structure TargetEndpoint (δ : Type v) (Req Rsp : Type u)
    [ClockDomain δ] [HwPacked Req] [HwPacked Rsp] where
  request : Stream.SinkEndpoint δ Req
  response : Stream.SourceEndpoint δ Rsp

def InitiatorPorts.resolve {δ : Type v} {Req Rsp : Type u}
    [ClockDomain δ] [HwPacked Req] [HwPacked Rsp]
    (ports : InitiatorPorts δ Req Rsp) (inst : DomainComponentInstance δ) :
    Except String (InitiatorEndpoint δ Req Rsp) := do
  return ⟨← ports.request.resolve inst, ← ports.response.resolve inst⟩

def TargetPorts.resolve {δ : Type v} {Req Rsp : Type u}
    [ClockDomain δ] [HwPacked Req] [HwPacked Rsp]
    (ports : TargetPorts δ Req Rsp) (inst : DomainComponentInstance δ) :
    Except String (TargetEndpoint δ Req Rsp) := do
  return ⟨← ports.request.resolve inst, ← ports.response.resolve inst⟩

/-- Connect an initiator to a target. Equal payload widths are insufficient:
the same nominal `Req`, `Rsp`, and domain `δ` must inhabit both endpoints. -/
def connect {δ : Type v} {Req Rsp : Type u}
    [ClockDomain δ] [HwPacked Req] [HwPacked Rsp]
    (graph : DomainComponentGraph δ) (initiator : InitiatorEndpoint δ Req Rsp)
    (target : TargetEndpoint δ Req Rsp) : Except String (DomainComponentGraph δ) := do
  let graph ← Stream.connect graph initiator.request target.request
  Stream.connect graph target.response initiator.response

/-- One simultaneous observation of the two independent handshakes. -/
structure Sample (Req Rsp : Type u) where
  request : Stream.Sample Req
  response : Stream.Sample Rsp
  deriving Repr, DecidableEq

def Sample.requestAccepted (sample : Sample Req Rsp) : Bool :=
  sample.request.accepted

def Sample.responseAccepted (sample : Sample Req Rsp) : Bool :=
  sample.response.accepted

/-- A monitor state carries the exact ordered request queue. Its capacity
proof makes an overfull successfully-constructed state unrepresentable. -/
structure Tracker (protocol : Protocol Req Rsp) where
  pending : List Req
  bounded : pending.length ≤ protocol.maxOutstanding

namespace Tracker

def empty (protocol : Protocol Req Rsp) : Tracker protocol :=
  ⟨[], Nat.zero_le _⟩

private def enqueue (protocol : Protocol Req Rsp) (tracker : Tracker protocol)
    (request : Req) : Except String (Tracker protocol) :=
  if room : tracker.pending.length < protocol.maxOutstanding then
    .ok ⟨tracker.pending ++ [request], by simp; omega⟩
  else
    .error s!"protocol '{protocol.name}' exceeded its {protocol.maxOutstanding}-request outstanding limit"

private def matchResponse (protocol : Protocol Req Rsp)
    (request : Req) (response : Rsp) : Except String PUnit.{u + 1} :=
  letI := protocol.relatesDecidable
  if protocol.relates request response then .ok ⟨⟩
  else .error s!"response violates ordered protocol '{protocol.name}'"

/-- Execute one monitor cycle. A registered protocol cannot respond to a
new request with no older request; a combinational protocol may do so. With
older traffic, simultaneous response/request replaces the queue head and
therefore never needs a transient extra slot. -/
def step (protocol : Protocol Req Rsp) (tracker : Tracker protocol)
    (sample : Sample Req Rsp) : Except String (Tracker protocol) := do
  match sample.requestAccepted, sample.responseAccepted with
  | false, false => return tracker
  | true, false => enqueue protocol tracker sample.request.payload
  | false, true =>
      match pendingEq : tracker.pending with
      | [] => throw s!"protocol '{protocol.name}' accepted a response with no outstanding request"
      | request :: rest =>
          matchResponse protocol request sample.response.payload
          return ⟨rest, by
            have bound : (request :: rest).length ≤ protocol.maxOutstanding := by
              rw [← pendingEq]
              exact tracker.bounded
            simp only [List.length_cons] at bound
            omega⟩
  | true, true =>
      match pendingEq : tracker.pending with
      | request :: rest =>
          matchResponse protocol request sample.response.payload
          return ⟨rest ++ [sample.request.payload], by
            have bound : (request :: rest).length ≤ protocol.maxOutstanding := by
              rw [← pendingEq]
              exact tracker.bounded
            simpa only [List.length_append, List.length_cons, List.length_singleton,
              Nat.add_comm] using bound⟩
      | [] =>
          match protocol.responseTiming with
          | .registered =>
              throw s!"registered protocol '{protocol.name}' responded in the request's acceptance cycle"
          | .combinational =>
              matchResponse protocol sample.request.payload sample.response.payload
              return tracker

def run (protocol : Protocol Req Rsp) (samples : List (Sample Req Rsp)) :
    Except String (Tracker protocol) :=
  samples.foldlM (step protocol) (empty protocol)

end Tracker

end Bus

end Loom.Hw
