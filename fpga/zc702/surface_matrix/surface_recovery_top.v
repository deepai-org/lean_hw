`timescale 1ns/1ps
`default_nettype none

// Board wrapper for the certified depth-eight full-rate independent-flush
// realization.  Control bits 3/4 are held recovery levels for source/sink.
module surface_recovery_top (
    input wire sys_clk_p, input wire sys_clk_n,
    input wire usr_clk_p, input wire usr_clk_n,
    output wire [3:0] leds
);
    wire clk200_raw, clk200, clk156_raw;
    IBUFDS #(.DIFF_TERM("TRUE"), .IBUF_LOW_PWR("FALSE"))
      u_sys_ibuf (.I(sys_clk_p), .IB(sys_clk_n), .O(clk200_raw));
    BUFG u_sys_bufg (.I(clk200_raw), .O(clk200));
    IBUFDS #(.DIFF_TERM("TRUE"), .IBUF_LOW_PWR("FALSE"))
      u_usr_ibuf (.I(usr_clk_p), .IB(usr_clk_n), .O(clk156_raw));
    wire [3:0] ps_fclk;
    PS7 u_ps7 (.FCLKCLK(ps_fclk));
    wire surface_clocks_enable, surface_source_clk, surface_sink_clk;
    BUFGCE #(.CE_TYPE("SYNC")) u_source_gate
      (.I(clk156_raw), .CE(surface_clocks_enable), .O(surface_source_clk));
    BUFGCE #(.CE_TYPE("SYNC")) u_sink_gate
      (.I(ps_fclk[0]), .CE(surface_clocks_enable), .O(surface_sink_clk));

    wire capture, drck, bscan_reset, runtest, sel, shift, tck, tdi, tms, update, tdo;
    wire [7:0] control;
    wire [31:0] run_limit;
    wire command_epoch;
    (* ASYNC_REG = "TRUE" *) reg source_command_sync0 = 1'b0;
    (* ASYNC_REG = "TRUE" *) reg source_command_sync1 = 1'b0;
    reg source_command_seen = 1'b0;
    reg [31:0] source_run_limit = 32'd4096;
    reg source_enable = 1'b0;
    reg source_recover = 1'b0;
    (* ASYNC_REG = "TRUE" *) reg sink_command_sync0 = 1'b0;
    (* ASYNC_REG = "TRUE" *) reg sink_command_sync1 = 1'b0;
    reg sink_command_seen = 1'b0;
    reg [31:0] sink_run_limit = 32'd4096;
    reg sink_enable = 1'b0;
    reg sink_recover = 1'b0;
    always @(posedge surface_source_clk) begin
      source_command_sync0 <= command_epoch;
      source_command_sync1 <= source_command_sync0;
      if (source_command_sync1 != source_command_seen) begin
        source_command_seen <= source_command_sync1;
        source_run_limit <= run_limit;
        source_enable <= control[0];
        source_recover <= control[3];
      end
    end
    always @(posedge surface_sink_clk) begin
      sink_command_sync0 <= command_epoch;
      sink_command_sync1 <= sink_command_sync0;
      if (sink_command_sync1 != sink_command_seen) begin
        sink_command_seen <= sink_command_sync1;
        sink_run_limit <= run_limit;
        sink_enable <= control[1];
        sink_recover <= control[4];
      end
    end

    reg [7:0] startup_count = 8'd0;
    always @(posedge clk200)
      if (!startup_count[7]) startup_count <= startup_count + 8'd1;
    wire startup_ready = startup_count[7];
    wire rst, clocks_ready;
    surface_reset_release u_reset_release (
      .clk200(clk200), .startup_ready(startup_ready),
      .reset_request_async(control[2]),
      .clocks_enable(surface_clocks_enable), .rst(rst), .ready(clocks_ready));

    reg [31:0] source_heartbeat = 32'd0;
    reg [31:0] sink_heartbeat = 32'd0;
    always @(posedge surface_source_clk) source_heartbeat <= source_heartbeat + 1;
    always @(posedge surface_sink_clk) sink_heartbeat <= sink_heartbeat + 1;

    wire [31:0] accepted, delivered, expected_sequence, digest, supply_gaps;
    wire [31:0] source_backpressure, sink_backpressure, sink_ticks;
    wire data_error, gap_error, source_recovered, sink_recovered;
    loom_system u_matrix (
      .surface_source_clk(surface_source_clk),
      .surface_sink_clk(surface_sink_clk), .rst(rst),
      .source_full_rate_d8__recover(source_recover),
      .source_full_rate_d8__recovered(source_recovered),
      .sink_full_rate_d8__recover(sink_recover),
      .sink_full_rate_d8__recovered(sink_recovered),
      .source_full_rate_d8__run_limit(source_run_limit),
      .source_full_rate_d8__source_enable(source_enable),
      .source_full_rate_d8__o_accepted(accepted),
      .source_full_rate_d8__o_backpressure(source_backpressure),
      .sink_full_rate_d8__run_limit(sink_run_limit),
      .sink_full_rate_d8__sink_enable(sink_enable),
      .sink_full_rate_d8__o_delivered(delivered),
      .sink_full_rate_d8__o_expected_sequence(expected_sequence),
      .sink_full_rate_d8__o_digest(digest),
      .sink_full_rate_d8__o_sticky_data_error(data_error),
      .sink_full_rate_d8__o_sticky_gap_error(gap_error),
      .sink_full_rate_d8__o_supply_gaps(supply_gaps),
      .sink_full_rate_d8__o_backpressure_ticks(sink_backpressure),
      .sink_full_rate_d8__o_ticks(sink_ticks));

    BSCANE2 #(.JTAG_CHAIN(1)) u_bscan (
      .CAPTURE(capture), .DRCK(drck), .RESET(bscan_reset), .RUNTEST(runtest),
      .SEL(sel), .SHIFT(shift), .TCK(tck), .TDI(tdi), .TMS(tms),
      .UPDATE(update), .TDO(tdo));
    surface_matrix_bscan u_transport (
      .tck(tck), .sel(sel), .capture(capture), .shift(shift),
      .update(update), .tdi(tdi), .tdo(tdo),
      .clocks_ready(clocks_ready), .system_reset(rst),
      .source_heartbeat(source_heartbeat), .sink_heartbeat(sink_heartbeat),
      .accepted({224'd0, accepted}), .delivered({224'd0, delivered}),
      .expected_sequence({224'd0, expected_sequence}),
      .digest({224'd0, digest}), .supply_gaps({224'd0, supply_gaps}),
      .source_backpressure({224'd0, source_backpressure}),
      .sink_backpressure({224'd0, sink_backpressure}),
      .sink_ticks({224'd0, sink_ticks}),
      .data_errors({7'd0, data_error}), .gap_errors({7'd0, gap_error}),
      .recovery_status({sink_recovered, source_recovered}),
      .command_epoch(command_epoch), .control(control), .run_limit(run_limit));

    assign leds[0] = clocks_ready;
    assign leds[1] = data_error | gap_error;
    assign leds[2] = source_recovered & sink_recovered;
    assign leds[3] = source_heartbeat[22] ^ sink_heartbeat[22];
endmodule

`default_nettype wire
