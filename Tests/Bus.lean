-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Bus

/-! # Typed same-clock request/response bus regressions -/

namespace Tests.Bus

open Loom.Hw

private inductive CoreClock
private instance : ClockDomain CoreClock where name := "core"

private def protocol : Bus.Protocol (BitVec 8) (BitVec 8) where
  name := "echo"
  maxOutstanding := 2
  responseTiming := .registered
  relates request response := request = response
  relatesDecidable := inferInstance

private def idleReq (payload : BitVec 8) : Stream.Sample (BitVec 8) :=
  ⟨false, true, payload⟩

private def idleRsp (payload : BitVec 8) : Stream.Sample (BitVec 8) :=
  ⟨false, true, payload⟩

private def sendReq (payload : BitVec 8) : Stream.Sample (BitVec 8) :=
  ⟨true, true, payload⟩

private def sendRsp (payload : BitVec 8) : Stream.Sample (BitVec 8) :=
  ⟨true, true, payload⟩

private def acceptedTrace : List (Bus.Sample (BitVec 8) (BitVec 8)) :=
  [⟨sendReq 11, idleRsp 0⟩,
   ⟨sendReq 12, sendRsp 11⟩,
   ⟨idleReq 0, sendRsp 12⟩]

#guard match Bus.Tracker.run protocol acceptedTrace with
  | .ok tracker => tracker.pending.isEmpty
  | .error _ => false

#guard match Bus.Tracker.run protocol [⟨idleReq 0, sendRsp 9⟩] with
  | .error _ => true
  | .ok _ => false

#guard match Bus.Tracker.run protocol
    [⟨sendReq 1, idleRsp 0⟩,
     ⟨sendReq 2, idleRsp 0⟩,
     ⟨sendReq 3, idleRsp 0⟩] with
  | .error _ => true
  | .ok _ => false

#guard match Bus.Tracker.run protocol [⟨sendReq 7, sendRsp 7⟩] with
  | .error _ => true
  | .ok _ => false

private def combinational : Bus.Protocol (BitVec 8) (BitVec 8) :=
  { protocol with name := "combinational-echo", responseTiming := .combinational }

#guard match Bus.Tracker.run combinational [⟨sendReq 7, sendRsp 7⟩] with
  | .ok tracker => tracker.pending.isEmpty
  | .error _ => false

private def busPorts : Bus.InitiatorPorts CoreClock (BitVec 16) (BitVec 32) :=
  Bus.initiatorPorts "ReadRequest" "ReadResponse"

#guard busPorts.decls.length == 6

end Tests.Bus
