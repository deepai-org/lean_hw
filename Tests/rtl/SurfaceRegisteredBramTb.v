`timescale 1ns/1ps
`default_nettype none

module surface_registered_bram_tb;
  reg source_clk = 0;
  reg sink_clk = 0;
  reg rst = 1;
  reg source_enable = 0;
  reg sink_enable = 0;
  reg [31:0] run_limit = 32'd4096;
  always #2 source_clk = ~source_clk;
  always #7 sink_clk = ~sink_clk;

  wire [31:0] next_value, offered, accepted, source_backpressure, source_ticks;
  wire [31:0] delivered, expected_sequence, digest, supply_gaps;
  wire [31:0] sink_backpressure, sink_ticks;
  wire data_error, gap_error, delivery_started;

  loom_system dut (
    .surface_source_clk(source_clk), .surface_sink_clk(sink_clk), .rst(rst),
    .source_ordinary_d4__run_limit(run_limit),
    .source_ordinary_d4__source_enable(source_enable),
    .source_ordinary_d4__o_next_value(next_value),
    .source_ordinary_d4__o_offered(offered),
    .source_ordinary_d4__o_accepted(accepted),
    .source_ordinary_d4__o_backpressure(source_backpressure),
    .source_ordinary_d4__o_ticks(source_ticks),
    .sink_ordinary_d4__run_limit(run_limit),
    .sink_ordinary_d4__sink_enable(sink_enable),
    .sink_ordinary_d4__o_delivered(delivered),
    .sink_ordinary_d4__o_expected_sequence(expected_sequence),
    .sink_ordinary_d4__o_digest(digest),
    .sink_ordinary_d4__o_sticky_data_error(data_error),
    .sink_ordinary_d4__o_sticky_gap_error(gap_error),
    .sink_ordinary_d4__o_supply_gaps(supply_gaps),
    .sink_ordinary_d4__o_delivery_started(delivery_started),
    .sink_ordinary_d4__o_backpressure_ticks(sink_backpressure),
    .sink_ordinary_d4__o_ticks(sink_ticks));

  task wait_delivery(input [31:0] target);
    integer timeout;
    begin
      timeout = 0;
      while (delivered != target && timeout < 1000000) begin
        @(posedge sink_clk);
        timeout = timeout + 1;
      end
      if (delivered != target) begin
        $display("SURFACE_REGISTERED_BRAM_FAIL timeout target=%0d delivered=%0d", target, delivered);
        $fatal(1);
      end
    end
  endtask

  task check_clean(input [255:0] campaign);
    begin
      if (accepted !== run_limit || delivered !== run_limit ||
          expected_sequence !== run_limit || digest !== 0 || data_error !== 0) begin
        $display("SURFACE_REGISTERED_BRAM_FAIL campaign=%0s accepted=%0d delivered=%0d expected=%0d digest=%08x data_error=%b",
          campaign, accepted, delivered, expected_sequence, digest, data_error);
        $fatal(1);
      end
      $display("SURFACE_REGISTERED_BRAM campaign=%0s PASS accepted=%0d delivered=%0d source_bp=%0d",
        campaign, accepted, delivered, source_backpressure);
    end
  endtask

  initial begin
    repeat (12) @(posedge source_clk);
    repeat (5) @(posedge sink_clk);
    rst = 0;
    source_enable = 1;
    sink_enable = 1;
    wait_delivery(32'd4096);
    repeat (6) @(posedge sink_clk);
    check_clean("continuous");

    run_limit = 32'd8192;
    wait_delivery(32'd4224);
    source_enable = 0;
    sink_enable = 0;
    rst = 1;
    repeat (12) @(posedge source_clk);
    repeat (5) @(posedge sink_clk);
    run_limit = 32'd4096;
    rst = 0;
    source_enable = 1;
    sink_enable = 1;
    wait_delivery(32'd4096);
    repeat (6) @(posedge sink_clk);
    check_clean("coordinated_reset_under_load");
    $display("SURFACE_REGISTERED_BRAM_RTL_PASS width=32 depth=4 presentation=registered");
    $finish;
  end
endmodule

`default_nettype wire
