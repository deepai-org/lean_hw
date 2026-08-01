// Copyright (c) 2026 Kevin Baragona
// SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
//
// tb_epochengine.v -- the Layer-2 acceptance ladder for the Loom-emitted
// LNP64 §3 epoch engine (`rtl/epochengine.v`) and its narrow-epoch twin
// (`rtl/epochengine_tiny.v`, ew=3, where saturation is reachable).
//
// The stimulus is a literal transliteration of `Machines.Epoch.Engine`'s
// `tbTrace` / `tbTraceTiny`, and the printed event lines use exactly the
// format of `lake env lean --run Machines/Epoch/Emit.lean predict`, so
// this leg of the ladder is a `diff` against the *verified* fast
// evaluator (`fastRunOpen_agrees`), not against a hand-written mirror.
//
// Scenarios (each named for the §3 sentence / Layer-1 theorem it covers):
//   a  check-hit                              -> ok        (Protocol.Init is coherent)
//   b  epoch mismatch                         -> -STALE
//   c  malformed handle                       -> -BADREF   (T-E4 structural first)
//   d  current live reference, no rights      -> -DENIED   (T-E4 rights last)
//   e  use concurrent with an in-flight bump  -> ok        (T-E7 in-flight liberty)
//   f  after the bump returns, the old epoch  -> -STALE at BOTH volumes (T-E1/T-E5)
//   g  the new epoch                          -> ok
//   h/i/j poison bump, then even *current*-epoch uses -> -POISONED, forever (T-E3)
//   tiny: 6 bumps saturate the counter; the cell is dead and no bump
//         revives it                          -> -STALE forever (T-E2)
`timescale 1ns/1ps
module tb;
  reg clk = 0, rst = 1;
  always #5 clk = ~clk;

  // ---------------- 32-bit engine ----------------
  reg        q0v = 0, q0op = 0, q0pol = 0;
  reg [8:0]  q0cell = 0;   reg [31:0] q0ep = 0;   reg [2:0] q0fl = 3'd7;
  reg        q1v = 0, q1op = 0, q1pol = 0;
  reg [8:0]  q1cell = 0;   reg [31:0] q1ep = 0;   reg [2:0] q1fl = 3'd7;

  wire        o_resp0_valid, o_resp1_valid, o_bump_done0, o_bump_done1;
  wire [2:0]  o_resp0_code, o_resp1_code;
  wire [15:0] o_bump_cycles;
  wire [1:0]  o_b_acked;
  wire        o_inval_valid;

  epochengine dut (
    .clk(clk), .rst(rst),
    .req0_valid(q0v), .req0_op(q0op), .req0_cell(q0cell),
    .req0_epoch(q0ep), .req0_policy(q0pol), .req0_flags(q0fl),
    .req1_valid(q1v), .req1_op(q1op), .req1_cell(q1cell),
    .req1_epoch(q1ep), .req1_policy(q1pol), .req1_flags(q1fl),
    .o_resp0_valid(o_resp0_valid), .o_resp0_code(o_resp0_code),
    .o_resp1_valid(o_resp1_valid), .o_resp1_code(o_resp1_code),
    .o_bump_done0(o_bump_done0), .o_bump_done1(o_bump_done1),
    .o_bump_cycles(o_bump_cycles), .o_b_acked(o_b_acked),
    .o_inval_valid(o_inval_valid)
  );

  // ---------------- narrow-epoch twin ----------------
  reg        t0v = 0, t0op = 0, t0pol = 0;
  reg [1:0]  t0cell = 0;   reg [2:0] t0ep = 0;   reg [2:0] t0fl = 3'd7;
  reg        t1v = 0, t1op = 0, t1pol = 0;
  reg [1:0]  t1cell = 0;   reg [2:0] t1ep = 0;   reg [2:0] t1fl = 3'd7;

  wire        u_resp0_valid, u_resp1_valid, u_bump_done0, u_bump_done1;
  wire [2:0]  u_resp0_code, u_resp1_code;
  wire [15:0] u_bump_cycles;

  epochengine_tiny tdut (
    .clk(clk), .rst(rst),
    .req0_valid(t0v), .req0_op(t0op), .req0_cell(t0cell),
    .req0_epoch(t0ep), .req0_policy(t0pol), .req0_flags(t0fl),
    .req1_valid(t1v), .req1_op(t1op), .req1_cell(t1cell),
    .req1_epoch(t1ep), .req1_policy(t1pol), .req1_flags(t1fl),
    .o_resp0_valid(u_resp0_valid), .o_resp0_code(u_resp0_code),
    .o_resp1_valid(u_resp1_valid), .o_resp1_code(u_resp1_code),
    .o_bump_done0(u_bump_done0), .o_bump_done1(u_bump_done1),
    .o_bump_cycles(u_bump_cycles)
  );

  integer k;    // cycle index of the engine phase
  integer tk;   // cycle index of the tiny phase
  integer maxacked;

  // ======== 32-bit engine drivers (one cycle each) ========
  task ecycle; begin
    @(posedge clk); #1;
    if (o_resp0_valid || o_resp1_valid || o_bump_done0 || o_bump_done1)
      $display("%0d r0v=%0d r0c=%0d r1v=%0d r1c=%0d bd0=%0d bd1=%0d bcyc=%0d",
               k, o_resp0_valid, o_resp0_code, o_resp1_valid, o_resp1_code,
               o_bump_done0, o_bump_done1, o_bump_cycles);
    if (o_b_acked > maxacked) maxacked = o_b_acked;
    k = k + 1;
    q0v = 0; q1v = 0;
  end endtask

  task eidle(input [15:0] n); begin : L
    integer i;
    for (i = 0; i < n; i = i + 1) begin
      q0v = 0; q1v = 0; ecycle;
    end
  end endtask

  // chkSeq k cidx ep flags = one check + 3 idle cycles
  task echk(input [1:0] vol, input [8:0] cidx, input [31:0] ep, input [2:0] fl);
  begin
    if (vol == 0) begin
      q0v = 1; q0op = 0; q0cell = cidx; q0ep = ep; q0pol = 0; q0fl = fl;
    end else begin
      q1v = 1; q1op = 0; q1cell = cidx; q1ep = ep; q1pol = 0; q1fl = fl;
    end
    ecycle; eidle(3);
  end endtask

  // bmpSeq k cidx poison = one bump + 9 idle cycles
  task ebmp(input [1:0] vol, input [8:0] cidx, input pol);
  begin
    if (vol == 0) begin
      q0v = 1; q0op = 1; q0cell = cidx; q0ep = 0; q0pol = pol; q0fl = 3'd7;
    end else begin
      q1v = 1; q1op = 1; q1cell = cidx; q1ep = 0; q1pol = pol; q1fl = 3'd7;
    end
    ecycle; eidle(9);
  end endtask

  // ======== tiny-engine drivers ========
  task tcycle; begin
    @(posedge clk); #1;
    if (u_resp0_valid || u_resp1_valid || u_bump_done0 || u_bump_done1)
      $display("%0d r0v=%0d r0c=%0d r1v=%0d r1c=%0d bd0=%0d bd1=%0d bcyc=%0d",
               tk, u_resp0_valid, u_resp0_code, u_resp1_valid, u_resp1_code,
               u_bump_done0, u_bump_done1, u_bump_cycles);
    tk = tk + 1;
    t0v = 0; t1v = 0;
  end endtask

  task tidle(input [15:0] n); begin : L2
    integer i;
    for (i = 0; i < n; i = i + 1) begin t0v = 0; t1v = 0; tcycle; end
  end endtask

  task tchk(input [1:0] vol, input [1:0] cidx, input [2:0] ep, input [2:0] fl);
  begin
    if (vol == 0) begin
      t0v = 1; t0op = 0; t0cell = cidx; t0ep = ep; t0pol = 0; t0fl = fl;
    end else begin
      t1v = 1; t1op = 0; t1cell = cidx; t1ep = ep; t1pol = 0; t1fl = fl;
    end
    tcycle; tidle(3);
  end endtask

  task tbmp(input [1:0] vol, input [1:0] cidx, input pol);
  begin
    if (vol == 0) begin
      t0v = 1; t0op = 1; t0cell = cidx; t0ep = 0; t0pol = pol; t0fl = 3'd7;
    end else begin
      t1v = 1; t1op = 1; t1cell = cidx; t1ep = 0; t1pol = pol; t1fl = 3'd7;
    end
    tcycle; tidle(9);
  end endtask

  integer i;
  initial begin
    k = 0; tk = 0; maxacked = 0;
    rst = 1;
    @(posedge clk); @(posedge clk);
    #1 rst = 0;

    $display("--- epochengine ---");
    echk(0, 9'd5, 32'd1, 3'd7);   // (a) check-hit           -> ok
    echk(0, 9'd5, 32'd9, 3'd7);   // (b) epoch mismatch      -> -STALE
    echk(0, 9'd5, 32'd1, 3'd6);   // (c) malformed handle    -> -BADREF
    echk(0, 9'd5, 32'd1, 3'd3);   // (d) no rights           -> -DENIED
    // (e) T-E7: volume 1 uses the pre-bump epoch in the very cycle the
    //     bump is issued, and MAY succeed.
    q0v = 1; q0op = 1; q0cell = 9'd5; q0ep = 0; q0pol = 0; q0fl = 3'd7;
    q1v = 1; q1op = 0; q1cell = 9'd5; q1ep = 32'd1; q1pol = 0; q1fl = 3'd7;
    ecycle; eidle(3);
    eidle(9);
    // (f) after the return: the old epoch is dead at BOTH volumes
    echk(0, 9'd5, 32'd1, 3'd7);
    echk(1, 9'd5, 32'd1, 3'd7);
    // (g) the new epoch validates
    echk(0, 9'd5, 32'd2, 3'd7);
    echk(1, 9'd5, 32'd2, 3'd7);
    // (h)(i)(j) poison: even current-epoch uses fail, forever
    ebmp(0, 9'd7, 1'b1);
    echk(0, 9'd7, 32'd2, 3'd7);
    echk(1, 9'd7, 32'd2, 3'd7);
    eidle(20);
    echk(0, 9'd7, 32'd2, 3'd7);

    $display("--- epochengine_tiny ---");
    for (i = 0; i < 6; i = i + 1) tbmp(0, 2'd1, 1'b0);
    tchk(0, 2'd1, 3'd7, 3'd7);
    tchk(1, 2'd1, 3'd7, 3'd7);
    tbmp(0, 2'd1, 1'b0);
    tchk(0, 2'd1, 3'd7, 3'd7);

    $display("ACKVEC_MAX=%0d", maxacked);
    $finish;
  end
endmodule
