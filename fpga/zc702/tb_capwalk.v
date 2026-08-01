// Copyright (c) 2026 Kevin Baragona
// SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
//
// tb_capwalk.v -- the Layer-2 acceptance ladder for the Loom-emitted LNP64
// §2.2 capability engine (`rtl/capwalk.v`): on-chip entry cache, the
// page-walker-class fill sequencer, and the AUTHENTICATED fill path.
//
// The stimulus is a literal transliteration of `Machines.CapWalk.Engine`'s
// `tbTrace`, and the printed event lines use exactly the format of
//   lake env lean --run Machines/CapWalk/Emit.lean predict
// so this leg of the ladder is a `diff` against the *verified* fast
// evaluator (`fastRunOpen_agrees`), not against a hand-written mirror.
//
// The DDR is BEHAVIOURAL AND HOSTILE. `ddr_mode` tells it how to lie:
//
//   0  honest        -- serves capwalk_ddr.hex
//   1  CORRUPT       -- slot 6's payload word arrives with a rights bit
//                       flipped, carrying its GENUINE tag
//   2  SUBSTITUTE    -- reads for slot 7 are answered from slot 6: a
//                       correctly-authenticated entry, for the wrong slot
//   3  RE-ISSUED     -- serves capwalk_ddr_remint.hex, in which slot 8's
//                       tag is the one a correct installer would write
//                       after the embedded cell was bumped to epoch 3
//
// and the REPLAY attack needs no mode at all: slot 5 is dropped and
// re-incarnated (embedded epoch 1 -> 3) and the honest, correctly-tagged,
// PREVIOUS-INCARNATION entry is served. It is well-formed, it is genuinely
// slot 5's, its tag verifies against everything except the one field that
// never spilled to DDR — and that is exactly why it is caught.
//
// Scenarios:
//   a  cold miss -> 3-beat walk -> MAC -> install -> ok
//   b  second use                                 -> ok, NO fabric transaction
//   c  slot 261 (same cache index)                -> ok, evicts slot 5
//   d  slot 5 again                               -> ok, re-filled
//   e  live current reference, no rights          -> -DENIED (§2.2 step 4)
//   f  wrong object/interface class               -> -BADREF (§2.2 step 5)
//   g  slot index >= 2^sw                         -> -BADREF (structural)
//   h  embedded epoch mismatch                    -> -STALE, answered on-chip
//   i  one §3 lineage bump                        -> -STALE (T-C4)
//   A1 corrupted entry                            -> FAULT, slot poisoned
//   A1b honest store afterwards                   -> FAULT, forever
//   A2 substituted entry                          -> FAULT
//   ctl drop+re-incarnate + re-issued entry       -> ok
//   A3 replayed previous-incarnation entry        -> FAULT
`timescale 1ns/1ps
module tb;
  reg clk = 0, rst = 1;
  always #5 clk = ~clk;

  // ---------------- DUT ports ----------------
  reg         req_valid = 0, req_wf = 1;
  reg  [1:0]  req_op = 0;
  reg  [23:0] req_slot = 0;
  reg  [31:0] req_epoch = 0;
  reg  [7:0]  req_need = 0, req_cls = 1;
  reg  [15:0] req_off = 0, req_len = 1;
  reg         m_done = 0;
  reg  [63:0] m_rdata = 0;
  reg         inval_valid = 0;
  reg  [8:0]  inval_cell = 0;
  reg  [31:0] inval_epoch = 0;

  wire        o_resp_valid, o_fault_valid, o_m_start_rd;
  wire [2:0]  o_resp_code;
  wire [23:0] o_fault_slot;
  wire [15:0] o_fill_count, o_fault_count, o_fill_cycles;
  wire [31:0] o_m_addr;

  capwalk dut (
    .clk(clk), .rst(rst),
    .req_valid(req_valid), .req_op(req_op), .req_slot(req_slot),
    .req_epoch(req_epoch), .req_need(req_need), .req_cls(req_cls),
    .req_off(req_off), .req_len(req_len), .req_wf(req_wf),
    .m_done(m_done), .m_rdata(m_rdata), .tbl_base(32'd0),
    .inval_valid(inval_valid), .inval_cell(inval_cell),
    .inval_epoch(inval_epoch),
    .o_resp_valid(o_resp_valid), .o_resp_code(o_resp_code),
    .o_fault_valid(o_fault_valid), .o_fault_slot(o_fault_slot),
    .o_fill_count(o_fill_count), .o_fault_count(o_fault_count),
    .o_fill_cycles(o_fill_cycles),
    .o_m_start_rd(o_m_start_rd), .o_m_addr(o_m_addr)
  );

  // ---------------- the behavioural (hostile) DDR ----------------
  // 512 slots x 4 words, exactly `Machines.CapWalk.Engine.ddrImage`.
  reg [63:0] img  [0:2047];  // honest
  reg [63:0] imgr [0:2047];  // slot 8 re-issued at embedded epoch 3
  reg [1:0]  ddr_mode = 0;

  localparam CORRUPT_BIT = 4;   // a RIGHTS bit: the corruption is an
                                // attempted rights amplification

  function [63:0] ddrword(input [31:0] addr);
    reg [31:0] widx, slot, src;
    reg [1:0]  j;
    reg [63:0] w;
    begin
      widx = addr >> 3;
      slot = widx >> 2;
      j    = widx[1:0];
      // SUBSTITUTION: a read for slot 7 is answered from slot 6
      src  = (ddr_mode == 2 && slot == 32'd7) ? 32'd6 : slot;
      w    = (ddr_mode == 3) ? imgr[{src[8:0], j}] : img[{src[8:0], j}];
      // CORRUPTION: flip one payload bit of slot 6, keep the genuine tag
      if (ddr_mode == 1 && src == 32'd6 && j == 2'd0)
        w = w ^ (64'd1 << CORRUPT_BIT);
      ddrword = w;
    end
  endfunction

  // one in-flight single-beat read, latency 2 (the Lean harness's `lat`)
  reg        pvalid = 0;
  reg [3:0]  pcnt = 0;
  reg [31:0] paddr = 0;

  integer k;

  // One cycle: drive the DDR response, clock, print, sample the request.
  task cyc; begin
    if (pvalid && pcnt == 0) begin
      m_done = 1; m_rdata = ddrword(paddr); pvalid = 0;
    end else begin
      m_done = 0; m_rdata = 0;
      if (pvalid) pcnt = pcnt - 1;
    end
    @(posedge clk); #1;
    if (o_resp_valid || o_fault_valid)
      $display("%0d rv=%0d rc=%0d fv=%0d fs=%0d fills=%0d faults=%0d",
               k, o_resp_valid, o_resp_code, o_fault_valid, o_fault_slot,
               o_fill_count, o_fault_count);
    if (o_m_start_rd) begin pvalid = 1; pcnt = 2; paddr = o_m_addr; end
    k = k + 1;
    req_valid = 0; inval_valid = 0;
  end endtask

  task gapn(input integer n); begin : G
    integer i;
    for (i = 0; i < n; i = i + 1) begin req_valid = 0; inval_valid = 0; cyc; end
  end endtask

  // a check + `g` idle cycles (9 total for a hit, 40 for a miss+fill)
  task docheck(input [23:0] slot, input [31:0] ep, input [7:0] need,
               input [7:0] cls, input [15:0] off, input [15:0] len,
               input wf, input [1:0] mode, input integer g);
  begin
    ddr_mode  = mode;
    req_valid = 1; req_op = 2'd0; req_slot = slot; req_epoch = ep;
    req_need  = need; req_cls = cls; req_off = off; req_len = len;
    req_wf    = wf;
    cyc; gapn(g);
  end endtask

  // OP_DROP = 1, OP_MINT = 2
  task doop(input [1:0] op, input [23:0] slot, input [1:0] mode); begin
    ddr_mode  = mode;
    req_valid = 1; req_op = op; req_slot = slot;
    cyc; gapn(5);
  end endtask

  // one §3 broadcast cycle (the epoch engine bumping a lineage cell)
  task doinval(input [8:0] c, input [31:0] e); begin
    ddr_mode = 0;
    inval_valid = 1; inval_cell = c; inval_epoch = e;
    cyc; gapn(3);
  end endtask

  initial begin
    $readmemh("fpga/zc702/capwalk_ddr.hex", img);
    $readmemh("fpga/zc702/capwalk_ddr_remint.hex", imgr);
    k = 0;
    rst = 1;
    @(posedge clk); @(posedge clk);
    #1 rst = 0;

    $display("--- capwalk ---");
    // (a) cold miss -> walk -> authenticate -> install -> ok
    docheck(24'd5,  32'd1, 8'h0F, 8'd1, 16'h100, 16'd1, 1'b1, 2'd0, 39);
    // (b) hit: no fabric transaction
    docheck(24'd5,  32'd1, 8'h0F, 8'd1, 16'h100, 16'd1, 1'b1, 2'd0, 8);
    // (c) slot 261 shares cache index 5 -> eviction
    docheck(24'd261, 32'd1, 8'hFF, 8'd1, 16'h000, 16'd1, 1'b1, 2'd0, 39);
    // (d) slot 5 must be re-filled
    docheck(24'd5,  32'd1, 8'h0F, 8'd1, 16'h100, 16'd1, 1'b1, 2'd0, 39);
    // (e) rights -> -DENIED
    docheck(24'd5,  32'd1, 8'hF0, 8'd1, 16'h100, 16'd1, 1'b1, 2'd0, 8);
    // (f) class -> -BADREF
    docheck(24'd5,  32'd1, 8'h0F, 8'd2, 16'h100, 16'd1, 1'b1, 2'd0, 8);
    // (g) slot index >= 2^sw -> -BADREF (structural)
    docheck(24'h100005, 32'd1, 8'h0F, 8'd1, 16'h100, 16'd1, 1'b1, 2'd0, 8);
    // (h) embedded epoch mismatch -> -STALE, on-chip, no DDR traffic
    docheck(24'd5,  32'd9, 8'h0F, 8'd1, 16'h100, 16'd1, 1'b1, 2'd0, 8);
    // (i) one §3 lineage bump -> the SAME cached entry is now -STALE
    doinval(9'd3, 32'd2);
    docheck(24'd5,  32'd1, 8'h0F, 8'd1, 16'h100, 16'd1, 1'b1, 2'd0, 8);
    // (A1) CORRUPTION
    docheck(24'd6,  32'd1, 8'h03, 8'd1, 16'h200, 16'd1, 1'b1, 2'd1, 39);
    // (A1b) the poison is permanent even against an honest store
    docheck(24'd6,  32'd1, 8'h03, 8'd1, 16'h200, 16'd1, 1'b1, 2'd0, 39);
    // (A2) SUBSTITUTION
    docheck(24'd7,  32'd1, 8'h0F, 8'd1, 16'h300, 16'd1, 1'b1, 2'd2, 39);
    // (ctl) drop + re-incarnate slot 8, store re-issues under the new epoch
    doop(2'd1, 24'd8, 2'd3);
    doop(2'd2, 24'd8, 2'd3);
    docheck(24'd8,  32'd3, 8'hFF, 8'd1, 16'h400, 16'd1, 1'b1, 2'd3, 39);
    // (A3) REPLAY: drop + re-incarnate slot 5, honest store serves the
    //      previous incarnation's correctly-tagged entry
    doop(2'd1, 24'd5, 2'd0);
    doop(2'd2, 24'd5, 2'd0);
    docheck(24'd5,  32'd3, 8'h0F, 8'd1, 16'h100, 16'd1, 1'b1, 2'd0, 39);

    $finish;
  end
endmodule
