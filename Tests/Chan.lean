-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.System
import Loom.Hw.CompileCorrect
import Loom.Hw.ChanSync
import Loom.Hw.AsyncFifo
import Loom.Hw.AsyncQueueStorage
import Loom.Hw.AsyncQueueStorageDesign
import Loom.Hw.AsyncFifoDesign
import Loom.Hw.ToggleChan
import Loom.Hw.SystemRealize
import Loom.Hw.CertifiedSystem
import Evidence.ReferenceCdcRtl

/-! # Typed channel and named-system regressions -/

namespace Tests.Chan

open Loom.Hw

namespace Storage

private def parameters : Cdc.AsyncQueueStorage.Parameters :=
  { width := 8, depth := 4, readLatency := 2,
    depthPositive := by decide, readLatencyPositive := by decide }

private def initial : Fin parameters.depth → BitVec parameters.width := fun _ => 0

private def writeEvent : Cdc.AsyncQueueStorage.Event parameters :=
  { writeTick := true, write := some (⟨1, by decide⟩, 37#8) }

private def readEvent : Cdc.AsyncQueueStorage.Event parameters :=
  { readTick := true, read := some ⟨1, by decide⟩ }

private def advanceReadPipeline : Cdc.AsyncQueueStorage.Event parameters :=
  { readTick := true }

private def bank := Cdc.AsyncQueueStorage.registerBank parameters
private def afterWrite := bank.step (bank.reset initial) writeEvent
private def afterRead := bank.step afterWrite.state readEvent
private def afterLatency := bank.step afterRead.state advanceReadPipeline

/-- The unconditional storage witness has arbitrary initial contents,
independent clocks, and the declared synchronous read latency. -/
example : afterRead.response = none := by native_decide
example : afterLatency.response = some 37#8 := by native_decide
example : Cdc.AsyncQueueStorage.CollisionFree writeEvent := by native_decide

private def collidingEvent : Cdc.AsyncQueueStorage.Event parameters :=
  { writeTick := true, write := some (⟨1, by decide⟩, 99#8),
    readTick := true, read := some ⟨1, by decide⟩ }

example : ¬Cdc.AsyncQueueStorage.CollisionFree collidingEvent := by native_decide
example : (Cdc.AsyncQueueStorage.registerBankBinding parameters).externalAssumption = none := rfl

private def generatedBank := Cdc.AsyncQueueStorage.registerBankDesigns parameters

private theorem generatedBank_ready : generatedBank.compilerReady := by
  unfold Cdc.AsyncQueueStorage.RegisterBankDesigns.compilerReady
  constructor
  · native_decide
  constructor
  · native_decide
  constructor <;> native_decide

/-- The portable witness really enters the ordinary proved compiler and the
certificate-complete DAG simulator path on both clock-domain halves. -/
private def certifiedGeneratedBank :
    Cdc.AsyncQueueStorage.CertifiedRegisterBankDesigns parameters :=
  generatedBank.certify generatedBank_ready

example : certifiedGeneratedBank.writer.compiled =
    Compile.compile certifiedGeneratedBank.designs.writer :=
  certifiedGeneratedBank.writer.compiled_eq

example : certifiedGeneratedBank.reader.renderedUTF8 =
    (Loom.Emit.MicroVerilog.Print.print
      (Compile.compile certifiedGeneratedBank.designs.reader)).toUTF8 :=
  certifiedGeneratedBank.reader.renderedUTF8_eq

private def eventOrder : Cdc.AsyncQueueStorage.HappensBefore where
  before := (· < ·)
  transitive := Nat.lt_trans
  before_event := id

private def generation : Cdc.AsyncQueueStorage.SlotGeneration parameters eventOrder where
  address := ⟨1, by decide⟩
  generation := 7
  writeEvent := 10
  publishWriteEvent := 11
  acquireWriteEvent := 12
  readEvent := 13
  publishReadEvent := 14
  acquireReadEvent := 15
  reuseWriteEvent := 16
  write_published := by change 10 < 11; decide
  publication_acquired := by change 11 < 12; decide
  acquired_before_read := by change 12 < 13; decide
  read_published := by change 13 < 14; decide
  readPublication_acquired := by change 14 < 15; decide
  acquired_before_reuse := by change 15 < 16; decide

/-- The protocol certificate, rather than a timing-window axiom, discharges
the storage leaf's two possible same-slot co-tick collisions. -/
example : generation.writeEvent ≠ generation.readEvent := generation.write_ne_read_event
example : generation.readEvent ≠ generation.reuseWriteEvent := generation.read_ne_reuse_event

end Storage

namespace CompiledAsyncControl

private def parameters : Cdc.AsyncFifoDesign.Parameters :=
  { width := 8, depth := 4, depthAtLeastTwo := by decide,
    powerOfTwo := by decide }

/-- Both CDC-control halves take the exact ordinary Design compiler/DAG path.
No handwritten RTL or target binding participates in these certificates. -/
private def controls : Cdc.AsyncFifoDesign.Controls parameters :=
  Cdc.AsyncFifoDesign.certify parameters (by decide) (by decide)
    (by decide) (by decide)

example : controls.source.renderedUTF8 =
    (Loom.Emit.MicroVerilog.Print.print
      (Compile.compile (Cdc.AsyncFifoDesign.sourceControl parameters))).toUTF8 :=
  controls.source.renderedUTF8_eq

example : Cdc.AsyncFifoDesign.synchronizerRegisters parameters =
    [("async_fifo_source_control_w8_d4", ["read_gray_sync0", "read_gray_sync1"]),
     ("async_fifo_sink_control_w8_d4", ["write_gray_sync0", "write_gray_sync1"])] := rfl

end CompiledAsyncControl

namespace Sampling

private def sourceHistory : Cdc.AsyncFifo.PointerHistory where
  countAt := id
  monotone := fun _ _ h => h
  step := by
    intro tick
    exact Or.inr rfl

private def observation : Cdc.AsyncFifo.HistorySample sourceHistory 2 9 6
    (Cdc.Gray.encode (sourceHistory.countAt 6)) :=
  Cdc.AsyncFifo.sampledPointer_from_history sourceHistory (by decide) (by decide)

example : 2 ≤ 6 ∧ 6 ≤ 9 ∧
    Cdc.Gray.encode (sourceHistory.countAt 6) =
      Cdc.Gray.encode (sourceHistory.countAt 6) :=
  observation.valid_past_codeword

end Sampling

namespace ResetSkew

private def resetQ : Chan 8 := { name := "resetQ", depth := 2, policy := .exchange }

private def heldSource : Cdc.AsyncFifo.Request 8 :=
  { sourceReleased := false, sourceTick := true, push := some 55#8,
    sinkReleased := true, sinkTick := true }

example : (Cdc.AsyncFifo.step resetQ (Cdc.AsyncFifo.reset 8) heldSource).accepted = none := by
  exact (Cdc.AsyncFifo.source_held resetQ _ _ rfl).1

private def releaseTrace : List (Cdc.AsyncFifo.Request 8) :=
  [{ sourceReleased := false, sinkReleased := false },
   { sourceReleased := true, sinkReleased := false, sourceTick := true,
     push := some 9#8 },
   { sourceReleased := true, sinkReleased := true, sinkTick := true,
     writeSample := 1, pop := true }]

private theorem releaseTrace_valid : Cdc.AsyncFifo.ReleaseSchedule releaseTrace := by
  constructor <;> native_decide

example := Cdc.AsyncFifo.equivalent_under_release_skew resetQ (by decide)
  releaseTrace releaseTrace_valid

private def portableStorage : Cdc.AsyncQueueStorage.Implementation
    (Cdc.AsyncFifo.storageParameters resetQ (by decide)) :=
  Cdc.AsyncQueueStorage.DepthTwo.implementation 8

private def compiledParameters : Cdc.AsyncFifoDesign.Parameters :=
  { width := 8, depth := 2, depthAtLeastTwo := by decide,
    powerOfTwo := by decide }

private def storedFifoRefinement : Chan.Refinement resetQ :=
  Cdc.AsyncFifoDesign.Compiled.refinement compiledParameters resetQ rfl
    (by decide) portableStorage

/-- The compiler-produced controls and unconditional finite register-bank
witness instantiate the same parametric FIFO theorem. Its arbitrary
finite-trace result needs no physical leaf assumption. -/
example := storedFifoRefinement.equivalent releaseTrace

end ResetSkew

def q : Chan 8 := { name := "q", depth := 2, policy := .exchange }

private def producerCore (channel : Chan 8) : Design where
  name := "producer"
  regs := [⟨"sent", 1, 0⟩]
  mems := []
  rules := [⟨"send", .ite (.and (.not (.reg 1 "sent")) channel.canEnq)
    (.seq (channel.enq (.lit 42)) (.write 1 "sent" (.lit 1))) .skip⟩]
  outputs := ["sent"]

private def consumerCore (channel : Chan 8) : Design where
  name := "consumer"
  regs := [⟨"got", 8, 0⟩]
  mems := []
  rules := [⟨"receive", .ite channel.canDeq
    (.seq (.write 8 "got" channel.deq) channel.pop) .skip⟩]
  outputs := ["got"]

def producer : Design := q.withSource (producerCore q)
def consumer : Design := q.withSink (consumerCore q)

private def chipBuilder : SystemBuilder :=
  System.empty
    |>.island "producer" producer (clock := "clk")
    |>.island "consumer" consumer (clock := "clk")
    |>.connect q (source := "producer") (sink := "consumer")

def chip : System := chipBuilder.certify (by native_decide)

example : (match chip.check with | .ok _ => true | .error _ => false) = true := by
  native_decide

private def missingEndpointBuilder : SystemBuilder :=
  System.empty
    |>.island "producer" producer
    |>.connect q (source := "producer") (sink := "absent")

private def duplicateIslandBuilder : SystemBuilder :=
  System.empty
    |>.island "same" producer
    |>.island "same" consumer

/-- Malformed declaration data cannot cross the opaque `System` boundary. -/
example : !(missingEndpointBuilder.assemble.isOk) := by native_decide
example : !(duplicateIslandBuilder.assemble.isOk) := by native_decide

def chipDesign : Design :=
  match chip.elaborate with
  | .ok design => design
  | .error _ => { name := "invalid", regs := [], mems := [], rules := [], outputs := [] }

/-- Every generated endpoint input is consumed by assembly. -/
example : chipDesign.inputs = [] := by native_decide
example : Compile.DesignWF chipDesign :=
  Compile.designWFCheck_sound chipDesign (by native_decide)

/-- The real lowered Design transfers the payload through the depth-two FIFO. -/
example : (chipDesign.run 8 chipDesign.reset).regs "consumer__got" 8 = 42#8 := by
  native_decide

private def full : Chan.State 8 := [1#8, 2#8]

/-- Exchange consumes the old head and accepts a replacement atomically. -/
example : (q.step full { push := some 3#8, pop := true }).state = [2#8, 3#8] := by
  native_decide
example : (q.step full { push := some 3#8, pop := true }).accepted = true := by
  native_decide
example : (q.step full { push := some 3#8, pop := true }).delivered = some 1#8 := by
  native_decide

private def refuse : Chan 8 :=
  { name := "refuse", depth := 2, policy := .refusePush }

/-- Refuse-on-full makes the alternative co-tick choice explicit. -/
example : (refuse.step full { push := some 3#8, pop := true }).state = [2#8] := by
  native_decide
example : (refuse.step full { push := some 3#8, pop := true }).accepted = false := by
  native_decide

private def fillAndExchange (channel : Chan 8) : St :=
  let s1 := channel.adapter.cycleOpen (channel.drive (some 1#8) false)
    channel.adapter.reset
  let s2 := channel.adapter.cycleOpen (channel.drive (some 2#8) false) s1
  channel.adapter.cycleOpen (channel.drive (some 3#8) true) s2

/-- The generated hardware adapter implements exchange at full occupancy. -/
example : q.occupancy (fillAndExchange q) = 2 := by native_decide
example : q.headValue (fillAndExchange q) = 2#8 := by native_decide

/-- The generated refuse-policy adapter pops but rejects the replacement. -/
example : refuse.occupancy (fillAndExchange refuse) = 1 := by native_decide
example : refuse.headValue (fillAndExchange refuse) = 2#8 := by native_decide

def wrongClocks : SystemBuilder :=
  System.empty
    |>.island "producer" producer (clock := "a")
    |>.island "consumer" consumer (clock := "b")
    |>.connect q (source := "producer") (sink := "consumer")

/-- A cross-clock channel is a valid abstract system, but cannot silently use
the ordinary synchronous lowering. -/
example : wrongClocks.check.isOk := by
  native_decide
def wrongClockSystem : System := wrongClocks.certify (by native_decide)
example : (match wrongClockSystem.elaborate with | .error _ => true | .ok _ => false) = true := by
  native_decide

/-! ## Named multiclock execution and theorem lifting -/

def asyncQ : Chan 8 :=
  { name := "asyncQ", depth := 2, policy := .refusePush }

private def asyncProducer : Design := asyncQ.withSource (producerCore asyncQ)
private def asyncConsumer : Design := asyncQ.withSink (consumerCore asyncQ)

private def asyncProducerIsland : SystemIsland :=
  ⟨"producer", "clkA", asyncProducer⟩

private def asyncConnection : SystemConnection :=
  ⟨8, asyncQ, "producer", "consumer"⟩

private def asyncChipBuilder : SystemBuilder :=
  System.empty
    |>.island "producer" asyncProducer (clock := "clkA")
    |>.island "consumer" asyncConsumer (clock := "clkB")
    |>.connect asyncQ (source := "producer") (sink := "consumer")

def asyncChip : System := asyncChipBuilder.certify (by native_decide)

def interleavedChip : System :=
  (asyncChipBuilder.withClockRel .interleaved).certify (by native_decide)

def asynchronousChip : System :=
  (asyncChipBuilder.withClockRel .asynchronous).certify (by native_decide)

private def asyncProducerCertificate : CertifiedDesign asyncProducer :=
  .ofChecks (by native_decide) (by native_decide)

private def asyncConsumerCertificate : CertifiedDesign asyncConsumer :=
  .ofChecks (by native_decide) (by native_decide)

private def asyncFifoParameters : Cdc.AsyncFifoDesign.Parameters :=
  { width := 8, depth := 2, depthAtLeastTwo := by decide,
    powerOfTwo := by decide }

private def asyncChannelCertificate : Chan.Refinement asyncQ :=
  Cdc.AsyncFifoDesign.Compiled.refinement asyncFifoParameters asyncQ rfl
    (by decide) (Cdc.AsyncQueueStorage.DepthTwo.implementation 8)

private def certifiedInterleavedChip : CertifiedSystem interleavedChip where
  channelCertificate := by
    intro connection member
    have connectionEq : connection = asyncConnection := by
      simpa [interleavedChip, asyncChipBuilder, asyncConnection,
        System.empty, SystemBuilder.island, SystemBuilder.connect,
        SystemBuilder.withClockRel, System.connections_certify] using member
    subst connection
    exact asyncChannelCertificate
  islandCertificate := by
    intro name island found
    by_cases producerName : name = "producer"
    · subst name
      have islandEq : island = asyncProducerIsland := by
        simpa [interleavedChip, asyncChipBuilder, asyncProducerIsland,
          System.empty, SystemBuilder.island, SystemBuilder.connect,
          SystemBuilder.withClockRel, SystemBuilder.findIsland?,
          System.findIsland?_certify] using found.symm
      subst island
      exact asyncProducerCertificate
    · have consumerName : name = "consumer" := by
        by_contra notConsumer
        have producerName' : "producer" ≠ name := Ne.symm producerName
        have notConsumer' : "consumer" ≠ name := Ne.symm notConsumer
        have impossible : interleavedChip.findIsland? name = none := by
          simp [interleavedChip, asyncChipBuilder,
            System.empty, SystemBuilder.island, SystemBuilder.connect,
            SystemBuilder.withClockRel, SystemBuilder.findIsland?,
            System.findIsland?_certify, producerName', notConsumer']
        rw [impossible] at found
        contradiction
      subst name
      have islandEq : island =
          (⟨"consumer", "clkB", asyncConsumer⟩ : SystemIsland) := by
        simpa [interleavedChip, asyncChipBuilder,
          System.empty, SystemBuilder.island, SystemBuilder.connect,
          SystemBuilder.withClockRel, SystemBuilder.findIsland?,
          System.findIsland?_certify] using found.symm
      subst island
      exact asyncConsumerCertificate

def alignedChip : System :=
  (asyncChipBuilder.withClockRel (.aligned "clkA" "clkB")).certify (by native_decide)

/-- A typed cross-clock declaration passes the structural gate, but the
ordinary single-clock lowering refuses to invent a physical CDC. -/
example : asyncChip.check.isOk := by native_decide
example : (match asyncChip.elaborate with | .error _ => true | .ok _ => false) = true := by
  native_decide

/-- Clock relations consume the same replay prefix as the executable runner. -/
example : (interleavedChip.runPrefixChecked #[⟨["clkA"]⟩, ⟨["clkB"]⟩]).isOk := by
  native_decide
example : !(interleavedChip.runPrefixChecked #[⟨["clkA", "clkB"]⟩]).isOk := by
  native_decide
example : (asynchronousChip.runPrefixChecked #[⟨["clkA", "clkB"]⟩]).isOk := by
  native_decide
example : (alignedChip.runPrefixChecked #[⟨["clkA", "clkB"]⟩, ⟨[]⟩]).isOk := by
  native_decide
example : !(alignedChip.runPrefixChecked #[⟨["clkA"]⟩]).isOk := by
  native_decide

/-- Every public `System` carries the complete structural gate; its constructor
is private and malformed values remain only `SystemBuilder` data. -/
example : asyncChip.check.isOk := asyncChip.checked

private def transferSchedule : SchedulePrefix := #[
  ⟨["clkA"]⟩, ⟨["clkA"]⟩,
  ⟨["clkB"]⟩, ⟨["clkB"]⟩, ⟨["clkB"]⟩]

private def asyncConsumerIsland : SystemIsland :=
  ⟨"consumer", "clkB", asyncConsumer⟩

private theorem asyncConsumerFound :
    interleavedChip.findIsland? "consumer" = some asyncConsumerIsland := by
  simp [interleavedChip, asyncChipBuilder, asyncConsumerIsland,
    System.empty, SystemBuilder.island, SystemBuilder.connect,
    SystemBuilder.withClockRel, SystemBuilder.findIsland?,
    System.findIsland?_certify]

private def gotReg : Reg 8 := ⟨"got"⟩

private def gotSlot : FastEval.RegSlot asyncConsumer gotReg :=
  match found : FastEval.regSlot? asyncConsumer gotReg with
  | some slot => slot
  | none => False.elim <| by
      have ready : (FastEval.regSlot? asyncConsumer gotReg).isSome = true := by
        native_decide
      rw [found] at ready
      contradiction

private def gotView : CertifiedSystem.RegView certifiedInterleavedChip 8 where
  islandName := "consumer"
  island := asyncConsumerIsland
  found := asyncConsumerFound
  reg := gotReg
  slot := gotSlot

private def certifiedAsyncFinal : certifiedInterleavedChip.State :=
  certifiedInterleavedChip.runPrefix transferSchedule

/-- The optimized island state and System semantics remain joined after an
actual two-clock replay; typed readback observes the transferred payload. -/
example : gotView.read certifiedAsyncFinal = 42 := by native_decide

/-- Coverage is derived from all islands and channel slots. An empty oracle
fails closed and names every omitted coordinate. -/
example : !(CertifiedSystem.coverageGaps interleavedChip 4
    (fun _ => none)).isEmpty := by native_decide
example : (match CertifiedSystem.requireCoverage interleavedChip 4
    (fun _ => none) with | .error _ => true | .ok _ => false) = true := by
  native_decide

private def asyncFinal : asyncChip.State :=
  asyncChip.runPrefix transferSchedule

/-- The proof-side schedule value is directly executable and replayable. -/
example : (Expr.reg 8 "got").eval (asyncFinal.island "consumer") = 42#8 := by
  native_decide
example : (asyncFinal.channel "asyncQ").values.length = 0 := by
  native_decide

/-- Crossing reports are derived from the same typed assembly declaration. -/
example : asyncChip.crossingInventory.length = 1 := by native_decide
example : (asyncChip.crossingInventory.head?.map (fun row => row.sourceClock)) =
    some (some "clkA") := by native_decide

private theorem producerTrue :
    (asyncProducer.toAssumedOpenTSys (fun _ _ => True)).Invariant (fun _ => True) := by
  intro _ _
  trivial

/-- An ordinary open-Design theorem lifts without exposing a schedule in the
application proof. -/
example : asyncChip.Invariant (System.atIsland "producer" (fun _ => True)) :=
  asyncChip.liftIsland asyncProducerIsland (by rfl) producerTrue


/-- Channel safety lifts independently of endpoint implementation details and
composes with ordinary island invariants without exposing a schedule. -/
private theorem asyncCapacity : asyncChip.Invariant
    (System.atChannel asyncConnection
      fun queue => queue.length ≤ asyncQ.depth) :=
  asyncChip.channelCapacityInvariant asyncConnection (by rfl)

example : asyncChip.Invariant (fun state =>
    System.atIsland "producer" (fun _ => True) state ∧
    System.atChannel asyncConnection
      (fun queue => queue.length ≤ asyncQ.depth) state) :=
  asyncChip.invariantAnd
    (asyncChip.liftIsland asyncProducerIsland (by rfl) producerTrue)
    asyncCapacity

/-- Relational properties over the complete channel graph compose and lift
without exposing schedules or being encoded as island predicates. -/
example {left right : (String → System.PackedQueue) → Prop}
    (hLeft : System.ChannelInvariant asyncChip left)
    (hRight : System.ChannelInvariant asyncChip right) :
    asyncChip.Invariant (System.atChannels fun channels =>
      left channels ∧ right channels) :=
  asyncChip.liftChannels (hLeft.and hRight)

private def asyncBinding : System.BoundImplementation :=
  Loom.Evidence.ReferenceCdcRtl.asyncFifo asyncConnection (by decide) (by decide)

def realizedAsyncChip : System.RealizedSystem :=
  System.realizeChecked asyncChip [asyncBinding] (by native_decide) (by native_decide)

/-- Physical assembly covers the semantic crossing and its constraint group
exactly once; both completeness statements are kernel theorems. -/
example : realizedAsyncChip.artifacts.inventory.length = 1 := by native_decide
example : realizedAsyncChip.artifacts.topModule.channelInstances.length = 1 := by native_decide
example : realizedAsyncChip.artifacts.constraintFile.groups.length = 1 := by native_decide
example : realizedAsyncChip.emissionCheck.isOk := by native_decide
example : !(System.realize asyncChip []).isOk := by native_decide
example : !(System.realize asyncChip [asyncBinding, asyncBinding]).isOk := by native_decide
example := realizedAsyncChip.instance_keys_complete
example := realizedAsyncChip.constraint_keys_complete

/-! ## Optional certified channel implementations -/

/-- The actual generated synchronous FIFO is available through the generic
implementation interface and retains its reset-to-all-traces theorem. -/
example :
    let implementation := q.syncRefinement (by decide)
    let result := implementation.runConcrete implementation.reset
      [{ push := some 7#8 }, { pop := true }]
    result.accepted = [7#8] ∧ result.delivered = [7#8] := by
  native_decide

private def asyncRequests :
    List (Loom.Hw.Cdc.AsyncFifo.Request 8) := [
  { sourceTick := true, push := some 11#8 },
  { sinkTick := true, writeSample := 1 },
  { sinkTick := true, writeSample := 1 },
  { sinkTick := true, pop := true, writeSample := 1 }]

/-- The stock asynchronous implementation may wait for a synchronized pointer
view, then delivers the same FIFO trace; its all-request-traces theorem is
`Chan.Refinement.equivalent`. -/
example :
    let implementation := Loom.Hw.Cdc.AsyncFifo.refinement asyncQ (by decide)
    let result := implementation.runConcrete implementation.reset asyncRequests
    result.accepted = [11#8] ∧ result.delivered = [11#8] := by
  native_decide

private def mailbox : Chan 8 :=
  { name := "mailbox", depth := 1, policy := .refusePush }

private def toggleRequests :
    List (Loom.Hw.Cdc.ToggleChan.Request 8) := [
  { sourceTick := true, push := some 19#8 },
  { sinkTick := true, publish := true },
  { sinkTick := true, pop := true },
  { sourceTick := true, acknowledge := true }]

/-- The stock toggle mailbox has the same generic trace certificate; publish
and acknowledge delays are explicit adversarial request fields. -/
example :
    let implementation := Loom.Hw.Cdc.ToggleChan.refinement mailbox rfl
    let result := implementation.runConcrete implementation.reset toggleRequests
    result.accepted = [19#8] ∧ result.delivered = [19#8] := by
  native_decide

end Tests.Chan
