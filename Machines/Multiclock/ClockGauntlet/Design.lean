-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.System

/-!
# Clock Gauntlet

A deliberately small three-clock pipeline used to exercise Loom's System
boundary.  The islands are ordinary `Design`s and the only inter-island edges
are the two typed channels below.
-/

namespace Machines.Multiclock.ClockGauntlet

open Loom.Hw

def packetCount : Nat := 256

def sourceToTransform : Chan 32 :=
  { name := "source_to_transform", depth := 2, policy := .exchange }

def transformToChecker : Chan 32 :=
  { name := "transform_to_checker", depth := 2, policy := .exchange }

/-- Odd multiply, xor, and fixed rotate.  This is intentionally modest; the
clock and channel behavior, not arithmetic complexity, is the experiment. -/
def transformExpr (value : Expr 32) : Expr 32 :=
  let mixed := .xor (.mul value (.lit (0x9e3779b1 : BitVec 32)))
    (.lit (0xa5a55a5a : BitVec 32))
  .or (.shl mixed (.lit (7 : BitVec 32)))
    (.shr mixed (.lit (25 : BitVec 32)))

def transformValue (value : BitVec 32) : BitVec 32 :=
  let mixed := value * (0x9e3779b1 : BitVec 32) ^^^
    (0xa5a55a5a : BitVec 32)
  (mixed <<< 7) ||| (mixed >>> 25)

def sourceBody : Design where
  name := "clock_gauntlet_source"
  regs := [
    ⟨"next_packet", 32, 0⟩,
    ⟨"packets_offered", 32, 0⟩,
    ⟨"packets_accepted", 32, 0⟩,
    ⟨"source_backpressure", 32, 0⟩,
    ⟨"source_write_wraps", 32, 0⟩,
    ⟨"source_progress", 2, 0⟩]
  mems := []
  rules := [
    ⟨"progress", .write 2 "source_progress" (.lit 1)⟩,
    ⟨"accepted", .ite sourceToTransform.sourceAccepted
      (.seq (.write 32 "packets_accepted"
        (.add (.reg 32 "packets_accepted") (.lit 1)))
        (.ite (.eq (.slice (.reg 32 "packets_accepted") 0 1) (.lit 1))
          (.write 32 "source_write_wraps"
            (.add (.reg 32 "source_write_wraps") (.lit 1))) .skip)) .skip⟩,
    ⟨"offer", .ite
      (.ult (.reg 32 "next_packet") (.lit (BitVec.ofNat 32 packetCount)))
      (.ite sourceToTransform.canEnq
        (.seq (sourceToTransform.enq (.reg 32 "next_packet"))
          (.seq (.write 32 "next_packet"
            (.add (.reg 32 "next_packet") (.lit 1)))
            (.write 32 "packets_offered"
              (.add (.reg 32 "packets_offered") (.lit 1)))))
        (.write 32 "source_backpressure"
          (.add (.reg 32 "source_backpressure") (.lit 1)))) .skip⟩]
  outputs := ["next_packet", "packets_offered", "packets_accepted",
    "source_backpressure", "source_write_wraps", "source_progress"]

def transformBody : Design where
  name := "clock_gauntlet_transform"
  regs := [
    ⟨"packets_transformed", 32, 0⟩,
    ⟨"packets_forwarded", 32, 0⟩,
    ⟨"transform_backpressure", 32, 0⟩,
    ⟨"transform_read_wraps", 32, 0⟩,
    ⟨"transform_write_wraps", 32, 0⟩,
    ⟨"transform_progress", 2, 0⟩]
  mems := []
  rules := [
    ⟨"progress", .write 2 "transform_progress" (.lit 1)⟩,
    ⟨"write_accepted", .ite transformToChecker.sourceAccepted
      (.seq (.write 32 "packets_forwarded"
        (.add (.reg 32 "packets_forwarded") (.lit 1)))
        (.ite (.eq (.slice (.reg 32 "packets_forwarded") 0 1) (.lit 1))
          (.write 32 "transform_write_wraps"
            (.add (.reg 32 "transform_write_wraps") (.lit 1))) .skip)) .skip⟩,
    ⟨"transfer", .ite sourceToTransform.canDeq
      (.ite transformToChecker.canEnq
        (.seq (transformToChecker.enq (transformExpr sourceToTransform.deq))
          (.seq sourceToTransform.pop
            (.seq (.write 32 "packets_transformed"
              (.add (.reg 32 "packets_transformed") (.lit 1)))
              (.ite (.eq (.slice (.reg 32 "packets_transformed") 0 1) (.lit 1))
                (.write 32 "transform_read_wraps"
                  (.add (.reg 32 "transform_read_wraps") (.lit 1))) .skip))))
        (.write 32 "transform_backpressure"
          (.add (.reg 32 "transform_backpressure") (.lit 1)))) .skip⟩]
  outputs := ["packets_transformed", "packets_forwarded", "transform_backpressure",
    "transform_read_wraps", "transform_write_wraps", "transform_progress"]

def checkerBody : Design where
  name := "clock_gauntlet_checker"
  regs := [
    ⟨"packets_delivered", 32, 0⟩,
    ⟨"expected_sequence", 32, 0⟩,
    ⟨"final_digest", 32, 0⟩,
    ⟨"sticky_error", 1, 0⟩,
    ⟨"checker_read_wraps", 32, 0⟩,
    ⟨"checker_progress", 2, 0⟩]
  mems := []
  rules := [
    ⟨"progress", .write 2 "checker_progress" (.lit 1)⟩,
    ⟨"check", .ite transformToChecker.canDeq
      (.seq (.ite (.not (.eq transformToChecker.deq
          (transformExpr (.reg 32 "expected_sequence"))))
        (.write 1 "sticky_error" (.lit 1)) .skip)
        (.seq (.write 32 "final_digest"
          (.xor (.reg 32 "final_digest") transformToChecker.deq))
          (.seq (.write 32 "expected_sequence"
            (.add (.reg 32 "expected_sequence") (.lit 1)))
            (.seq (.write 32 "packets_delivered"
              (.add (.reg 32 "packets_delivered") (.lit 1)))
              (.seq (.ite (.eq (.slice (.reg 32 "packets_delivered") 0 1) (.lit 1))
                (.write 32 "checker_read_wraps"
                  (.add (.reg 32 "checker_read_wraps") (.lit 1))) .skip)
                transformToChecker.pop))))) .skip⟩]
  outputs := ["packets_delivered", "expected_sequence", "final_digest",
    "sticky_error", "checker_read_wraps", "checker_progress"]

def source : Design := sourceToTransform.withSource sourceBody

def transform : Design :=
  transformToChecker.withSource (sourceToTransform.withSink transformBody)

def checker : Design := transformToChecker.withSink checkerBody

def builder : SystemBuilder :=
  System.empty
    |>.island "source" source (clock := "source_clk")
    |>.island "transform" transform (clock := "transform_clk")
    |>.island "checker" checker (clock := "checker_clk")
    |>.connect sourceToTransform (source := "source") (sink := "transform")
    |>.connect transformToChecker (source := "transform") (sink := "checker")
    |>.withClockRel .unconstrained

def system : System := builder.certify (by decide)

def firstConnection : SystemConnection :=
  ⟨32, sourceToTransform, "source", "transform"⟩

def secondConnection : SystemConnection :=
  ⟨32, transformToChecker, "transform", "checker"⟩

end Machines.Multiclock.ClockGauntlet
