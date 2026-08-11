-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.System
import Loom.Hw.CompileCorrect

/-! # Typed channel and named-system regressions -/

namespace Tests.Chan

open Loom.Hw

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

def chip : System :=
  System.empty
    |>.island "producer" producer (clock := "clk")
    |>.island "consumer" consumer (clock := "clk")
    |>.connect q (source := "producer") (sink := "consumer")

example : (match chip.check with | .ok _ => true | .error _ => false) = true := by
  native_decide

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

def wrongClocks : System :=
  System.empty
    |>.island "producer" producer (clock := "a")
    |>.island "consumer" consumer (clock := "b")
    |>.connect q (source := "producer") (sink := "consumer")

/-- A synchronous realization cannot silently cross different clocks. -/
example : (match wrongClocks.check with | .error _ => true | .ok _ => false) = true := by
  native_decide

/-! ## Named multiclock execution and theorem lifting -/

def asyncQ : Chan 8 :=
  { name := "asyncQ", depth := 2, policy := .exchange,
    realization := .asyncFifo }

private def asyncProducer : Design := asyncQ.withSource (producerCore asyncQ)
private def asyncConsumer : Design := asyncQ.withSink (consumerCore asyncQ)

private def asyncProducerIsland : SystemIsland :=
  ⟨"producer", "clkA", asyncProducer⟩

def asyncChip : System :=
  System.empty
    |>.island "producer" asyncProducer (clock := "clkA")
    |>.island "consumer" asyncConsumer (clock := "clkB")
    |>.connect asyncQ (source := "producer") (sink := "consumer")

/-- A typed asynchronous declaration passes the structural gate, but the
ordinary single-clock lowering refuses to pretend it is a physical CDC. -/
example : asyncChip.check.isOk := by native_decide
example : (match asyncChip.elaborate with | .error _ => true | .ok _ => false) = true := by
  native_decide

private def transferSchedule : System.SchedulePrefix := #[
  ⟨["clkA"]⟩, ⟨["clkA"]⟩,
  ⟨["clkB"]⟩, ⟨["clkB"]⟩, ⟨["clkB"]⟩]

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
  asyncChip.liftIsland asyncProducerIsland (by native_decide) (by rfl)
    producerTrue

end Tests.Chan
