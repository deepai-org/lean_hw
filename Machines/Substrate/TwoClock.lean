-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Dsl
import Machines.Tutorial.SatCounter

/-! # Small certified two-clock example -/

namespace Machines.Substrate.TwoClock

open Loom.Hw
open Loom.Hw.Dsl

def queue : Chan 8 := { name := "q", depth := 2, policy := .exchange }
def queueSource : Chan.SourceEndpoint 8 := queue.source
def queueSink : Chan.SinkEndpoint 8 := queue.sink

def clkA : ClockHandle := .named "clkA"
def clkB : ClockHandle := .named "clkB"
def clkC : ClockHandle := .named "clkC"

def producer : Design where
  name := "two_clock_producer"
  regs := [⟨"sent", 1, 0⟩]
  mems := []
  rules := [⟨"send", .ite (.and (.not (.reg 1 "sent")) queueSource.canSend)
    (.seq (queueSource.send (.lit 42)) (.write 1 "sent" (.lit 1))) .skip⟩]
  outputs := ["sent"]

def consumer : Design where
  name := "two_clock_consumer"
  regs := [⟨"got", 8, 0⟩]
  mems := []
  rules := [⟨"receive", .ite queueSink.hasData
    (.seq (.write 8 "got" queueSink.data) queueSink.consume) .skip⟩]
  outputs := ["got"]

def monitor : Design := Machines.Tutorial.SatCounter.design

def producerIsland : IslandHandle := .named "producer" producer clkA
def consumerIsland : IslandHandle := .named "consumer" consumer clkB
def monitorIsland : IslandHandle := .named "monitor" monitor clkC
def queueRoute : ChannelRoute 8 := queue.between producerIsland consumerIsland

def monitorOpenInvariant :
    (monitor.toAssumedOpenTSys (fun _ _ => True)).Invariant
      Machines.Tutorial.SatCounter.SatOk :=
  monitor.openInvariant_of_noInputs (by decide)
    Machines.Tutorial.SatCounter.satOk_invariant

def handwrittenBuilder : SystemBuilder :=
  System.empty
    |>.addIsland producerIsland
    |>.addIsland consumerIsland
    |>.addIsland monitorIsland
    |>.addChannel queueRoute
    |>.withClockRel .asynchronous

def handwrittenSystem : System := handwrittenBuilder.certify (by decide)

/-- The application-facing declaration. Its islands remain ordinary Designs;
the command contributes only named clocks, topology, reset policy, and the
explicit certified crossing choice. -/
system prettySystem where
  clock clkA
  clock clkB
  clock clkC
  clocks Clock.asynchronous
  reset Reset.together
  channel q : 8 depth 2 policy Chan.exchange
  island producer on clkA module two_clock_producer where
    output reg sent : 1
    rule «send» :=
      if ~sent & q.canSend then { send 42 to q, sent <- 1 }
  island consumer on clkB module two_clock_consumer where
    output reg got : 8
    rule «receive» :=
      receive value from q then got <- value
  island monitor on clkC := monitor
  connect q from producer to consumer
  realize q with Cdc.grayFifo

/-- Syntax lowering is exact, rather than merely behaviorally equivalent, to
the original builder retained here as a regression oracle. -/
theorem prettySystem_eq_handwritten : prettySystem = handwrittenSystem := rfl

def builder : SystemBuilder := prettySystem.builder
def system : System := prettySystem

theorem monitor_ok_system :
    system.Invariant
      (System.atIsland "monitor" Machines.Tutorial.SatCounter.SatOk) :=
  by system_lift prettySystem monitor using monitorOpenInvariant

def connection : SystemConnection := queueRoute.toSystemConnection

/-- The abstract mailbox remains within its declared capacity under every
admitted schedule. This system theorem uses only the public connection law. -/
theorem channel_capacity_system :
    system.Invariant
      (System.atChannel connection fun values => values.length ≤ queue.depth) :=
  system.channelCapacityInvariant connection (by rfl)

example : system.resetPolicy = .coordinated := rfl

def application : System.Application prettySystem := prettySystem.application

def handwrittenApplication : System.Application handwrittenSystem :=
  handwrittenSystem.realizePortable (by decide)

/-- The syntax-selected realization emits the same exact byte tree as the
pre-existing portable application path. -/
theorem prettyArtifact_eq_handwritten :
    application.artifact.renderedUTF8 =
      handwrittenApplication.artifact.renderedUTF8 := rfl

abbrev certified : CertifiedSystem prettySystem := application.certified

/-- Exact, compiler-only physical realization of the small System. Every
behavioral channel module is a `CertifiedDesign`; the storage witness has no
external leaf assumption. -/
abbrev certifiedArtifact : System.CertifiedRealizedSystem prettySystem certified :=
  application.artifact

theorem certifiedArtifact_bytes :
    certifiedArtifact.renderedUTF8 = certifiedArtifact.renderedVerilog.toUTF8 :=
  certifiedArtifact.renderedUTF8_eq

theorem certifiedArtifact_complete (emitted : System.EmissionArtifact)
    (member : emitted ∈ certifiedArtifact.emissionArtifacts) :
    emitted.crossingKeys =
      system.connections.map SystemConnection.key :=
  certifiedArtifact.every_emitted_artifact_complete emitted member

def got : Reg 8 := ⟨"got"⟩

def transferSchedule : SchedulePrefix := #[
  clkA.tick, clkA.tick,
  clkB.tick, clkB.tick, clkB.tick]

def final : application.State := application.run transferSchedule

#guard application.readReg final consumerIsland got == 42

end Machines.Substrate.TwoClock
