`timescale 1ns/1ps
`default_nettype none

module surface_matrix_recovery_tb;
  reg source_clk = 1'b0;
  reg sink_clk = 1'b0;
  reg rst = 1'b1;
  reg source_recover = 1'b0;
  reg sink_recover = 1'b0;
  reg source_enable = 1'b1;
  reg sink_enable = 1'b0;
  reg [31:0] run_limit = 32'd4096;

  always #2 source_clk = ~source_clk;
  always #7 sink_clk = ~sink_clk;

  loom_system dut (
    .surface_source_clk(source_clk),
    .surface_sink_clk(sink_clk),
    .rst(rst),
    .source_full_rate_d8__recover(source_recover),
    .sink_full_rate_d8__recover(sink_recover),
    .source_full_rate_d8__run_limit(run_limit),
    .source_full_rate_d8__source_enable(source_enable),
    .sink_full_rate_d8__run_limit(run_limit),
    .sink_full_rate_d8__sink_enable(sink_enable)
  );

  integer waited;

  task wait_complete;
    begin
      waited = 0;
      while (dut.sink_full_rate_d8__o_delivered != run_limit && waited < 100000) begin
        @(posedge sink_clk);
        waited = waited + 1;
      end
      if (dut.sink_full_rate_d8__o_delivered != run_limit)
        $fatal(1, "recovery restart epoch timed out");
      repeat (12) @(posedge sink_clk);
      if (dut.source_full_rate_d8__o_accepted != run_limit)
        $fatal(1, "source accepted count mismatch after recovery");
      if (dut.sink_full_rate_d8__o_expected_sequence != run_limit ||
          dut.sink_full_rate_d8__o_digest != 0 ||
          dut.sink_full_rate_d8__o_sticky_data_error ||
          dut.sink_full_rate_d8__o_sticky_gap_error)
        $fatal(1, "checked recovery restart epoch failed");
    end
  endtask

  initial begin
    repeat (16) @(posedge sink_clk);
    rst = 1'b0;
    repeat (80) @(posedge sink_clk);
    sink_enable = 1'b1;
    while (dut.sink_full_rate_d8__o_delivered < 32'd128)
      @(posedge sink_clk);

    $display("SURFACE_MATRIX_RECOVERY request_under_load delivered=%0d accepted=%0d",
      dut.sink_full_rate_d8__o_delivered,
      dut.source_full_rate_d8__o_accepted);
    source_recover = 1'b1;
    sink_recover = 1'b1;
    waited = 0;
    while (!(dut.source_full_rate_d8__recovered &&
             dut.sink_full_rate_d8__recovered) && waited < 1000) begin
      @(posedge sink_clk);
      waited = waited + 1;
    end
    if (!(dut.source_full_rate_d8__recovered &&
          dut.sink_full_rate_d8__recovered))
      $fatal(1, "recovery acknowledgement timed out");
    repeat (12) @(posedge sink_clk);
    if (dut.sink_full_rate_d8__o_delivered != 0 ||
        dut.source_full_rate_d8__o_accepted != 0)
      $fatal(1, "recovered islands did not reset");

    sink_enable = 1'b0;
    source_recover = 1'b0;
    sink_recover = 1'b0;
    repeat (80) @(posedge sink_clk);
    sink_enable = 1'b1;
    wait_complete();
    $display("SURFACE_MATRIX_RECOVERY_RTL_PASS depth=8 endpoint=full_rate");
    $finish;
  end
endmodule

`default_nettype wire
