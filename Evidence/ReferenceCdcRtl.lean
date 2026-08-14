-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.SystemRealize
import Loom.Hw.ChanSync
import Loom.Hw.AsyncFifo
import Loom.Hw.ToggleChan

/-!
# Unverified handwritten CDC RTL references

These renderers are deliberately outside `Loom`: each joins a proved
executable channel model to handwritten Verilog without proving the text
implements that model. They are useful for syntax, integration, and external
tool experiments, but they are not admissible in a certified System release.

The certified path will instead compile per-domain control `Design`s and
leave only an `AsyncQueueStorage` physical leaf contract. Keeping these
references in `Evidence` makes the current trust boundary mechanically
visible in the import graph.
-/

namespace Loom.Evidence.ReferenceCdcRtl

open Loom.Hw
open Loom.Hw.System

private def widthDecl (width : Nat) : String :=
  if width = 1 then "" else s!"[{width - 1}:0] "

private def asyncFifoModule (info : CrossingInfo) : String :=
  let aw := Nat.log2 info.depth
  let pw := aw + 1
  let wd := widthDecl info.width
  let fullTarget := if aw = 1 then "~rgray_sync2" else
    "{" ++ s!"~rgray_sync2[{aw}:{aw - 1}], rgray_sync2[{aw - 2}:0]" ++ "}"
  s!"module loom_async_fifo_{info.channel}(\n" ++
  "  input wire src_clk, input wire dst_clk, input wire rst,\n" ++
  s!"  input wire src_valid, input wire {wd}src_payload, output wire src_ready,\n" ++
  s!"  output wire dst_valid, output wire {wd}dst_payload, input wire dst_pop);\n" ++
  s!"  reg {wd}mem [0:{info.depth - 1}];\n" ++
  s!"  reg [{pw - 1}:0] wbin, wgray, rbin, rgray;\n" ++
  "  reg full;\n" ++
  s!"  (* ASYNC_REG = \"TRUE\" *) reg [{pw - 1}:0] rgray_sync1, rgray_sync2;\n" ++
  s!"  (* ASYNC_REG = \"TRUE\" *) reg [{pw - 1}:0] wgray_sync1, wgray_sync2;\n" ++
  s!"  wire [{pw - 1}:0] wbin_next = wbin + (src_valid && src_ready);\n" ++
  s!"  wire [{pw - 1}:0] rbin_next = rbin + (dst_valid && dst_pop);\n" ++
  s!"  wire [{pw - 1}:0] wgray_next = (wbin_next >> 1) ^ wbin_next;\n" ++
  s!"  wire [{pw - 1}:0] rgray_next = (rbin_next >> 1) ^ rbin_next;\n" ++
  s!"  wire full_next = (wgray_next == {fullTarget});\n" ++
  "  assign src_ready = !full;\n" ++
  "  assign dst_valid = (rgray != wgray_sync2);\n" ++
  s!"  assign dst_payload = mem[rbin[{aw - 1}:0]];\n" ++
  "  always @(posedge src_clk or posedge rst) begin\n" ++
  "    if (rst) begin wbin<=0; wgray<=0; full<=0; rgray_sync1<=0; rgray_sync2<=0; end\n" ++
  "    else begin rgray_sync1<=rgray; rgray_sync2<=rgray_sync1;\n" ++
  s!"      if (src_valid && src_ready) mem[wbin[{aw - 1}:0]]<=src_payload;\n" ++
  "      wbin<=wbin_next; wgray<=wgray_next; full<=full_next; end\n" ++
  "  end\n" ++
  "  always @(posedge dst_clk or posedge rst) begin\n" ++
  "    if (rst) begin rbin<=0; rgray<=0; wgray_sync1<=0; wgray_sync2<=0; end\n" ++
  "    else begin wgray_sync1<=wgray; wgray_sync2<=wgray_sync1;\n" ++
  "      rbin<=rbin_next; rgray<=rgray_next; end\n" ++
  "  end\nendmodule\n"

/-- Handwritten Gray FIFO reference. The returned refinement certifies the
Lean executable model, not `moduleText`; this value is evidence-only. -/
def asyncFifo (connection : SystemConnection)
    (depthAtLeastTwo : 2 ≤ connection.chan.depth)
    (_powerOfTwo : 2 ^ Nat.log2 connection.chan.depth = connection.chan.depth) :
    BoundImplementation :=
  BoundImplementation.custom connection "evidence.unverified-gray-async-fifo" .different
    (Cdc.AsyncFifo.refinement connection.chan (by omega))
    (fun info => "loom_async_fifo_" ++ info.channel) asyncFifoModule
    (fun info => match info.sourceClock, info.sinkClock with
      | some source, some sink => [.asynchronousClocks source sink]
      | _, _ => [])
    { sourceOfferStages := 1
      sinkConsumeStages := 1
      forwardSynchronizerStages := 2
      reverseSynchronizerStages := 2
      storageReadStages := 0
      sourceIssueInterval := .conditional 1 .sourceTicks
        [.sourceReadyEveryTick]
      sinkIssueInterval := .conditional 2 .sinkTicks
        [.sinkPayloadAvailableEveryTick, .sinkConsumesWhenAvailable]
      delivery := .scheduleDependent
        [.sinkContinuesTicking, .sinkConsumesWhenAvailable,
          .sinkEventuallyObservesSource] }

end Loom.Evidence.ReferenceCdcRtl
