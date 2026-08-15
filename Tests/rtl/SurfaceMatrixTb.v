`timescale 1ns/1ps
`default_nettype none

module surface_matrix_tb;
  reg source_clk = 1'b0;
  reg sink_clk = 1'b0;
  reg rst = 1'b1;
  reg source_enable = 1'b0;
  reg sink_enable = 1'b0;
  reg [31:0] run_limit = 32'd4096;

  // Deliberately unrelated periods; the source is faster so a full-rate sink
  // can remain supplied after its local presentation buffer is primed.
  always #2 source_clk = ~source_clk;
  // Ratio 3.5:1 approximates the board campaign's independent 156.25/50 MHz
  // roots while retaining non-harmonic edge phases in this integer-timescale test.
  always #7 sink_clk = ~sink_clk;

  loom_system dut (
    .surface_source_clk(source_clk),
    .surface_sink_clk(sink_clk),
    .rst(rst),
    .source_ordinary_d2__run_limit(run_limit),
    .source_ordinary_d2__source_enable(source_enable),
    .sink_ordinary_d2__run_limit(run_limit),
    .sink_ordinary_d2__sink_enable(sink_enable),
    .source_full_rate_d2__run_limit(run_limit),
    .source_full_rate_d2__source_enable(source_enable),
    .sink_full_rate_d2__run_limit(run_limit),
    .sink_full_rate_d2__sink_enable(sink_enable),
    .source_ordinary_d4__run_limit(run_limit),
    .source_ordinary_d4__source_enable(source_enable),
    .sink_ordinary_d4__run_limit(run_limit),
    .sink_ordinary_d4__sink_enable(sink_enable),
    .source_full_rate_d4__run_limit(run_limit),
    .source_full_rate_d4__source_enable(source_enable),
    .sink_full_rate_d4__run_limit(run_limit),
    .sink_full_rate_d4__sink_enable(sink_enable),
    .source_ordinary_d8__run_limit(run_limit),
    .source_ordinary_d8__source_enable(source_enable),
    .sink_ordinary_d8__run_limit(run_limit),
    .sink_ordinary_d8__sink_enable(sink_enable),
    .source_full_rate_d8__run_limit(run_limit),
    .source_full_rate_d8__source_enable(source_enable),
    .sink_full_rate_d8__run_limit(run_limit),
    .sink_full_rate_d8__sink_enable(sink_enable),
    .source_ordinary_d16__run_limit(run_limit),
    .source_ordinary_d16__source_enable(source_enable),
    .sink_ordinary_d16__run_limit(run_limit),
    .sink_ordinary_d16__sink_enable(sink_enable),
    .source_full_rate_d16__run_limit(run_limit),
    .source_full_rate_d16__source_enable(source_enable),
    .sink_full_rate_d16__run_limit(run_limit),
    .sink_full_rate_d16__sink_enable(sink_enable)
  );

  wire all_done =
    dut.sink_ordinary_d2__o_delivered == run_limit &&
    dut.sink_full_rate_d2__o_delivered == run_limit &&
    dut.sink_ordinary_d4__o_delivered == run_limit &&
    dut.sink_full_rate_d4__o_delivered == run_limit &&
    dut.sink_ordinary_d8__o_delivered == run_limit &&
    dut.sink_full_rate_d8__o_delivered == run_limit &&
    dut.sink_ordinary_d16__o_delivered == run_limit &&
    dut.sink_full_rate_d16__o_delivered == run_limit;

  wire all_accepted =
    dut.source_ordinary_d2__o_accepted == run_limit &&
    dut.source_full_rate_d2__o_accepted == run_limit &&
    dut.source_ordinary_d4__o_accepted == run_limit &&
    dut.source_full_rate_d4__o_accepted == run_limit &&
    dut.source_ordinary_d8__o_accepted == run_limit &&
    dut.source_full_rate_d8__o_accepted == run_limit &&
    dut.source_ordinary_d16__o_accepted == run_limit &&
    dut.source_full_rate_d16__o_accepted == run_limit;

  wire any_data_error =
    dut.sink_ordinary_d2__o_sticky_data_error |
    dut.sink_full_rate_d2__o_sticky_data_error |
    dut.sink_ordinary_d4__o_sticky_data_error |
    dut.sink_full_rate_d4__o_sticky_data_error |
    dut.sink_ordinary_d8__o_sticky_data_error |
    dut.sink_full_rate_d8__o_sticky_data_error |
    dut.sink_ordinary_d16__o_sticky_data_error |
    dut.sink_full_rate_d16__o_sticky_data_error;

  wire any_full_rate_gap =
    dut.sink_full_rate_d2__o_sticky_gap_error |
    dut.sink_full_rate_d4__o_sticky_gap_error |
    dut.sink_full_rate_d8__o_sticky_gap_error |
    dut.sink_full_rate_d16__o_sticky_gap_error;

  wire qualified_full_rate_supply_continuous =
    dut.sink_full_rate_d4__o_supply_gaps == 0 &&
    dut.sink_full_rate_d8__o_supply_gaps == 0 &&
    dut.sink_full_rate_d16__o_supply_gaps == 0;

  wire all_digest_zero =
    dut.sink_ordinary_d2__o_digest == 32'd0 &&
    dut.sink_full_rate_d2__o_digest == 32'd0 &&
    dut.sink_ordinary_d4__o_digest == 32'd0 &&
    dut.sink_full_rate_d4__o_digest == 32'd0 &&
    dut.sink_ordinary_d8__o_digest == 32'd0 &&
    dut.sink_full_rate_d8__o_digest == 32'd0 &&
    dut.sink_ordinary_d16__o_digest == 32'd0 &&
    dut.sink_full_rate_d16__o_digest == 32'd0;

  wire all_source_backpressured =
    dut.source_ordinary_d2__o_backpressure != 0 &&
    dut.source_full_rate_d2__o_backpressure != 0 &&
    dut.source_ordinary_d4__o_backpressure != 0 &&
    dut.source_full_rate_d4__o_backpressure != 0 &&
    dut.source_ordinary_d8__o_backpressure != 0 &&
    dut.source_full_rate_d8__o_backpressure != 0 &&
    dut.source_ordinary_d16__o_backpressure != 0 &&
    dut.source_full_rate_d16__o_backpressure != 0;

  wire all_sink_stalled =
    dut.sink_ordinary_d2__o_backpressure_ticks != 0 &&
    dut.sink_full_rate_d2__o_backpressure_ticks != 0 &&
    dut.sink_ordinary_d4__o_backpressure_ticks != 0 &&
    dut.sink_full_rate_d4__o_backpressure_ticks != 0 &&
    dut.sink_ordinary_d8__o_backpressure_ticks != 0 &&
    dut.sink_full_rate_d8__o_backpressure_ticks != 0 &&
    dut.sink_ordinary_d16__o_backpressure_ticks != 0 &&
    dut.sink_full_rate_d16__o_backpressure_ticks != 0;

  integer waited;

  task common_reset;
    begin
      rst = 1'b1;
      repeat (12) @(posedge sink_clk);
      repeat (12) @(posedge source_clk);
      rst = 1'b0;
      repeat (8) @(posedge sink_clk);
    end
  endtask

  task wait_for_completion;
    begin
      waited = 0;
      while (!all_done && waited < 200000) begin
        @(posedge sink_clk);
        waited = waited + 1;
      end
      if (!all_done) $fatal(1, "surface matrix timed out");
      repeat (12) @(posedge sink_clk);
      if (!all_accepted) $fatal(1, "accepted counts did not reach run limit");
      if (any_data_error) $fatal(1, "sequence checker failed");
      if (any_full_rate_gap) begin
        $display("FULL_RATE_GAPS d2=%0d d4=%0d d8=%0d d16=%0d",
          dut.sink_full_rate_d2__o_sticky_gap_error,
          dut.sink_full_rate_d4__o_sticky_gap_error,
          dut.sink_full_rate_d8__o_sticky_gap_error,
          dut.sink_full_rate_d16__o_sticky_gap_error);
        $fatal(1, "full-rate endpoint inserted a steady-state bubble");
      end
      if (!qualified_full_rate_supply_continuous)
        $fatal(1, "qualified full-rate lanes observed a supply gap");
      if (!all_digest_zero) $fatal(1, "rolling digest mismatch");
    end
  endtask

  initial begin
    $display("SURFACE_MATRIX campaign=continuous begin");
    source_enable = 1'b1;
    sink_enable = 1'b0;
    common_reset();
    repeat (100) @(posedge sink_clk);
    sink_enable = 1'b1;
    wait_for_completion();
    $display("SURFACE_MATRIX campaign=continuous PASS");

    $display("SURFACE_MATRIX campaign=stall_backpressure begin");
    sink_enable = 1'b0;
    common_reset();
    repeat (300) @(posedge sink_clk);
    if (!all_source_backpressured)
      $fatal(1, "not every lane observed source backpressure while sink stalled");
    sink_enable = 1'b1;
    wait_for_completion();
    if (!all_sink_stalled) $fatal(1, "sink stall counters remained zero");
    $display("SURFACE_MATRIX campaign=stall_backpressure PASS");

    $display("SURFACE_MATRIX campaign=coordinated_reset_under_load begin");
    sink_enable = 1'b0;
    common_reset();
    repeat (100) @(posedge sink_clk);
    sink_enable = 1'b1;
    while (dut.sink_full_rate_d16__o_delivered < 32'd128)
      @(posedge sink_clk);
    rst = 1'b1;
    repeat (20) @(posedge sink_clk);
    if (dut.sink_full_rate_d16__o_delivered != 0 ||
        dut.source_ordinary_d2__o_accepted != 0)
      $fatal(1, "coordinated reset did not clear matrix state");
    sink_enable = 1'b0;
    rst = 1'b0;
    repeat (100) @(posedge sink_clk);
    sink_enable = 1'b1;
    wait_for_completion();
    $display("SURFACE_MATRIX campaign=coordinated_reset_under_load PASS");
    $display("SURFACE_MATRIX_RTL_PASS lanes=8 depths=2,4,8,16 endpoints=ordinary,full_rate");
    $finish;
  end
endmodule

`default_nettype wire
