-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Multiclock

/-!
# Multiclock surface-qualification matrix

Eight independent lanes exercise every combination of portable FIFO depth
2/4/8/16 and the ordinary/full-rate destination presentation.  All producers
share one physical clock name and all consumers another; each lane retains its
own island so the generated endpoint fragment remains structurally local.

The hardware is deliberately self-checking.  A board wrapper supplies a common
run limit and source/sink enables.  Each source emits its sequence number; each
sink checks order, accumulates an XOR digest, records exact counts, and latches
sticky data/throughput failures.  Full-rate lanes additionally reject a bubble
after steady delivery begins while the sink is enabled and the run is not
complete.
-/

namespace Machines.Multiclock.SurfaceMatrix

open Loom.Hw

inductive EndpointMode where
  | ordinary
  | fullRate
  deriving DecidableEq, Repr

def EndpointMode.label : EndpointMode → String
  | .ordinary => "ordinary"
  | .fullRate => "full_rate"

structure LaneSpec where
  depth : Nat
  mode : EndpointMode
  depthAtLeastTwo : 2 ≤ depth
  powerOfTwo : 2 ^ Nat.log2 depth = depth

def LaneSpec.label (spec : LaneSpec) : String :=
  spec.mode.label ++ "_d" ++ toString spec.depth

def LaneSpec.channel (spec : LaneSpec) : Chan 32 :=
  { name := "surface_" ++ spec.label, depth := spec.depth, policy := .exchange }

def laneSpecs : List LaneSpec :=
  [ ⟨2, .ordinary, by decide, by decide⟩,
    ⟨2, .fullRate, by decide, by decide⟩,
    ⟨4, .ordinary, by decide, by decide⟩,
    ⟨4, .fullRate, by decide, by decide⟩,
    ⟨8, .ordinary, by decide, by decide⟩,
    ⟨8, .fullRate, by decide, by decide⟩,
    ⟨16, .ordinary, by decide, by decide⟩,
    ⟨16, .fullRate, by decide, by decide⟩ ]

def sourceClock : ClockHandle := .named "surface_source_clk"
def sinkClock : ClockHandle := .named "surface_sink_clk"

def limitInput := "run_limit"
def sourceEnableInput := "source_enable"
def sinkEnableInput := "sink_enable"

private def increment (width : Nat) (name : String) : Act :=
  .write width name (.add (.reg width name) (.lit 1))

def producerBody (spec : LaneSpec) : Design where
  name := "surface_source_" ++ spec.label
  regs := [
    ⟨"next_value", 32, 0⟩,
    ⟨"offered", 32, 0⟩,
    ⟨"accepted", 32, 0⟩,
    ⟨"backpressure", 32, 0⟩,
    ⟨"ticks", 32, 0⟩]
  mems := []
  inputs := [⟨limitInput, 32⟩, ⟨sourceEnableInput, 1⟩]
  rules := [
    ⟨"tick", increment 32 "ticks"⟩,
    ⟨"accepted", .ite spec.channel.sourceAccepted
      (increment 32 "accepted") .skip⟩,
    ⟨"offer", .ite
      (.and (.reg 1 sourceEnableInput)
        (.ult (.reg 32 "next_value") (.reg 32 limitInput)))
      (.ite spec.channel.canEnq
        (.seq (spec.channel.enq (.reg 32 "next_value"))
          (.seq (increment 32 "next_value") (increment 32 "offered")))
        (increment 32 "backpressure"))
      .skip⟩]
  outputs := ["next_value", "offered", "accepted", "backpressure", "ticks"]

def sinkAvailable (spec : LaneSpec) : Expr 1 :=
  match spec.mode with
  | .ordinary => spec.channel.canDeq
  | .fullRate => spec.channel.fullRateHasData

def sinkPayload (spec : LaneSpec) : Expr 32 :=
  match spec.mode with
  | .ordinary => spec.channel.deq
  | .fullRate => spec.channel.fullRateData

def sinkConsume (spec : LaneSpec) : Act :=
  match spec.mode with
  | .ordinary => spec.channel.pop
  | .fullRate => spec.channel.fullRateConsume

def LaneSpec.expectsBubbleFree (spec : LaneSpec) : Bool :=
  spec.mode == .fullRate && decide (4 ≤ spec.depth)

def checkerBody (spec : LaneSpec) : Design where
  name := "surface_sink_" ++ spec.label
  regs := [
    ⟨"delivered", 32, 0⟩,
    ⟨"expected_sequence", 32, 0⟩,
    ⟨"digest", 32, 0⟩,
    ⟨"sticky_data_error", 1, 0⟩,
    ⟨"sticky_gap_error", 1, 0⟩,
    ⟨"supply_gaps", 32, 0⟩,
    ⟨"delivery_started", 1, 0⟩,
    ⟨"backpressure_ticks", 32, 0⟩,
    ⟨"ticks", 32, 0⟩]
  mems := []
  inputs := [⟨limitInput, 32⟩, ⟨sinkEnableInput, 1⟩]
  rules := [
    ⟨"tick", increment 32 "ticks"⟩,
    ⟨"disabled", .ite (.not (.reg 1 sinkEnableInput))
      (increment 32 "backpressure_ticks") .skip⟩,
    ⟨"full_rate_gap", .ite
      (.and (.reg 1 sinkEnableInput)
        (.and (.reg 1 "delivery_started")
          (.and (.ult (.reg 32 "expected_sequence") (.reg 32 limitInput))
            (.not (sinkAvailable spec)))))
      (match spec.mode with
       | .ordinary => .skip
       | .fullRate => .seq (increment 32 "supply_gaps")
          (if spec.expectsBubbleFree then
            .write 1 "sticky_gap_error" (.lit 1)
           else .skip))
      .skip⟩,
    ⟨"check", .ite (.and (.reg 1 sinkEnableInput) (sinkAvailable spec))
      (.seq (.ite (.not (.eq (sinkPayload spec) (.reg 32 "expected_sequence")))
          (.write 1 "sticky_data_error" (.lit 1)) .skip)
        (.seq (.write 1 "delivery_started" (.lit 1))
          (.seq (.write 32 "digest"
              (.xor (.reg 32 "digest") (sinkPayload spec)))
            (.seq (increment 32 "expected_sequence")
              (.seq (increment 32 "delivered") (sinkConsume spec))))))
      .skip⟩]
  outputs := ["delivered", "expected_sequence", "digest",
    "sticky_data_error", "sticky_gap_error", "supply_gaps", "delivery_started",
    "backpressure_ticks", "ticks"]

def producerIsland (spec : LaneSpec) : IslandHandle :=
  .named ("source_" ++ spec.label) (producerBody spec) sourceClock

def sinkIsland (spec : LaneSpec) : IslandHandle :=
  .named ("sink_" ++ spec.label) (checkerBody spec) sinkClock

def route (spec : LaneSpec) := spec.channel.between (producerIsland spec) (sinkIsland spec)

private def addLane (builder : SystemBuilder) (spec : LaneSpec) : SystemBuilder :=
  let withIslands := builder
    |>.addErasedIsland (producerIsland spec)
    |>.addErasedIsland (sinkIsland spec)
  match spec.mode with
  | .ordinary => withIslands.addChannel (route spec)
  | .fullRate => withIslands.addFullRateChannel (route spec)

def builder : SystemBuilder :=
  (laneSpecs.foldl addLane System.empty)
    |>.withClockRel .asynchronous

def system : System := builder.certify (by decide)

def application : System.Application system :=
  system.realizePortable (by decide)

def certifiedArtifact : System.CertifiedRealizedSystem system application.certified :=
  application.artifact

def expectedLaneLabels : List String :=
  ["ordinary_d2", "full_rate_d2", "ordinary_d4", "full_rate_d4",
   "ordinary_d8", "full_rate_d8", "ordinary_d16", "full_rate_d16"]

example : laneSpecs.map LaneSpec.label = expectedLaneLabels := by decide
example : system.connections.map (fun connection => connection.chan.depth) =
    [2, 2, 4, 4, 8, 8, 16, 16] := by decide
example : system.crossingInventory.map (fun info => info.channel) =
    laneSpecs.map (fun spec => spec.channel.name) := by decide
end Machines.Multiclock.SurfaceMatrix
