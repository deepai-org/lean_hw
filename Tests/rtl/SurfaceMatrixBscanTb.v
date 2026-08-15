`timescale 1ns/1ps
`default_nettype none

module surface_matrix_bscan_tb;
  reg tck = 0, sel = 1, capture = 0, shift = 0, update = 0, tdi = 0;
  wire tdo;
  reg clocks_ready = 1, system_reset = 0;
  reg [31:0] source_heartbeat = 32'h1357_2468;
  reg [31:0] sink_heartbeat = 32'h89ab_cdef;
  reg [255:0] accepted = 256'd0, delivered = 256'd0, expected_sequence = 256'd0;
  reg [255:0] digest = 256'd0;
  reg [255:0] supply_gaps = 256'd0, source_backpressure = 256'd0;
  reg [255:0] sink_backpressure = 256'd0, sink_ticks = 256'd0;
  reg [7:0] data_errors = 8'h81, gap_errors = 8'h42;
  reg [1:0] recovery_status = 2'b10;
  wire command_epoch;
  wire [7:0] control;
  wire [31:0] run_limit;

  surface_matrix_bscan dut (
    .tck(tck), .sel(sel), .capture(capture), .shift(shift),
    .update(update), .tdi(tdi), .tdo(tdo),
    .clocks_ready(clocks_ready), .system_reset(system_reset),
    .source_heartbeat(source_heartbeat), .sink_heartbeat(sink_heartbeat),
    .accepted(accepted), .delivered(delivered),
    .expected_sequence(expected_sequence), .digest(digest),
    .supply_gaps(supply_gaps), .source_backpressure(source_backpressure),
    .sink_backpressure(sink_backpressure), .sink_ticks(sink_ticks),
    .data_errors(data_errors), .gap_errors(gap_errors),
    .recovery_status(recovery_status),
    .command_epoch(command_epoch), .control(control), .run_limit(run_limit));

  task tick;
    begin #1; tck = 1; #1; tck = 0; end
  endtask

  task shift_command(input [41:0] command);
    integer bit_index;
    begin
      capture = 0; update = 0; shift = 1;
      for (bit_index = 0; bit_index < 42; bit_index = bit_index + 1) begin
        tdi = command[bit_index];
        tick();
      end
      shift = 0; tdi = 0;
    end
  endtask

  task commit;
    begin update = 1; tick(); update = 0; end
  endtask

  task read_index(input [6:0] index, output [31:0] result);
    integer bit_index;
    reg [41:0] response;
    begin
      shift_command({1'b0, 1'b0, 1'b0, index, 32'd0});
      commit();
      capture = 1; tick(); capture = 0;
      shift = 1;
      response = 42'd0;
      for (bit_index = 0; bit_index < 42; bit_index = bit_index + 1) begin
        response[bit_index] = tdo;
        tick();
      end
      shift = 0;
      result = response[31:0];
    end
  endtask

  task expect_read(input [6:0] index, input [31:0] expected);
    reg [31:0] actual;
    begin
      read_index(index, actual);
      if (actual !== expected) begin
        $display("SURFACE_MATRIX_BSCAN_FAIL index=%0d expected=%08x actual=%08x", index, expected, actual);
        $fatal(1);
      end
    end
  endtask

  initial begin
    accepted[3*32 +: 32] = 32'ha003_0003;
    delivered[6*32 +: 32] = 32'hd006_0006;
    expected_sequence[4*32 +: 32] = 32'he000_0004;
    digest[1*32 +: 32] = 32'h600d_0001;
    supply_gaps[4*32 +: 32] = 32'h5a90_0004;
    source_backpressure[5*32 +: 32] = 32'hbacc_0005;
    sink_backpressure[2*32 +: 32] = 32'h51ac_0002;
    sink_ticks[7*32 +: 32] = 32'h71c0_0007;

    expect_read(7'd0, 32'h534d_4154);
    expect_read(7'd3, 32'h89ab_cdef);
    expect_read(7'd19, 32'ha003_0003);
    expect_read(7'd30, 32'hd006_0006);
    expect_read(7'd33, 32'h600d_0001);
    expect_read(7'd52, 32'h5a90_0004);
    expect_read(7'd61, 32'hbacc_0005);
    expect_read(7'd66, 32'h51ac_0002);
    expect_read(7'd79, 32'h71c0_0007);
    expect_read(7'd84, 32'he000_0004);
    expect_read(7'd40, 32'h0000_0081);
    expect_read(7'd41, 32'h0000_0042);
    expect_read(7'd42, 32'h0000_0002);

    if (command_epoch !== 0) $fatal(1, "unexpected initial command epoch");
    shift_command({1'b0, 1'b1, 1'b0, 7'd2, 32'd100000000});
    commit();
    if (run_limit !== 32'd100000000 || command_epoch !== 1)
      $fatal(1, "run-limit command failed");
    shift_command({1'b0, 1'b1, 1'b0, 7'd1, 32'h0000_0003});
    commit();
    if (control !== 8'h03 || command_epoch !== 0)
      $fatal(1, "control command failed");
    expect_read(7'd2, 32'd100000000);
    expect_read(7'd1, 32'h0000_0003);
    $display("SURFACE_MATRIX_BSCAN_RTL_PASS single_clock=tck xsdb_dr_bits=42 observations=stable commands=epoch");
    $finish;
  end
endmodule

`default_nettype wire
