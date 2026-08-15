`timescale 1ns/1ps
`default_nettype none

module surface_matrix_top (
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

    // Independent roots: the programmable Si570 user oscillator and PS FCLK0
    // referenced to the board's separate 33.333 MHz PS oscillator. FCLK0 is
    // supplied by the running board image at 100 MHz; RTL simulation also
    // exercises the resulting 156.25:100 source/sink ratio.
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
    (* ASYNC_REG = "TRUE" *) reg sink_command_sync0 = 1'b0;
    (* ASYNC_REG = "TRUE" *) reg sink_command_sync1 = 1'b0;
    reg sink_command_seen = 1'b0;
    reg [31:0] sink_run_limit = 32'd4096;
    reg sink_enable = 1'b0;

    always @(posedge surface_source_clk) begin
      source_command_sync0 <= command_epoch;
      source_command_sync1 <= source_command_sync0;
      if (source_command_sync1 != source_command_seen) begin
        source_command_seen <= source_command_sync1;
        source_run_limit <= run_limit;
        source_enable <= control[0];
      end
    end
    always @(posedge surface_sink_clk) begin
      sink_command_sync0 <= command_epoch;
      sink_command_sync1 <= sink_command_sync0;
      if (sink_command_sync1 != sink_command_seen) begin
        sink_command_seen <= sink_command_sync1;
        sink_run_limit <= run_limit;
        sink_enable <= control[1];
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

`define DECLARE_LANE(label) \
    wire [31:0] accepted_``label, delivered_``label, expected_``label, digest_``label; \
    wire [31:0] supply_gaps_``label, source_bp_``label, sink_bp_``label, sink_ticks_``label; \
    wire data_error_``label, gap_error_``label;
    `DECLARE_LANE(ordinary_d2)
    `DECLARE_LANE(full_rate_d2)
    `DECLARE_LANE(ordinary_d4)
    `DECLARE_LANE(full_rate_d4)
    `DECLARE_LANE(ordinary_d8)
    `DECLARE_LANE(full_rate_d8)
    `DECLARE_LANE(ordinary_d16)
    `DECLARE_LANE(full_rate_d16)

`define CONNECT_LANE(label) \
      .source_``label``__run_limit(source_run_limit), \
      .source_``label``__source_enable(source_enable), \
      .source_``label``__o_accepted(accepted_``label), \
      .source_``label``__o_backpressure(source_bp_``label), \
      .sink_``label``__run_limit(sink_run_limit), \
      .sink_``label``__sink_enable(sink_enable), \
      .sink_``label``__o_delivered(delivered_``label), \
      .sink_``label``__o_expected_sequence(expected_``label), \
      .sink_``label``__o_digest(digest_``label), \
      .sink_``label``__o_sticky_data_error(data_error_``label), \
      .sink_``label``__o_sticky_gap_error(gap_error_``label), \
      .sink_``label``__o_supply_gaps(supply_gaps_``label), \
      .sink_``label``__o_backpressure_ticks(sink_bp_``label), \
      .sink_``label``__o_ticks(sink_ticks_``label)

    loom_system u_matrix (
      .surface_source_clk(surface_source_clk),
      .surface_sink_clk(surface_sink_clk),
      .rst(rst),
      `CONNECT_LANE(ordinary_d2),
      `CONNECT_LANE(full_rate_d2),
      `CONNECT_LANE(ordinary_d4),
      `CONNECT_LANE(full_rate_d4),
      `CONNECT_LANE(ordinary_d8),
      `CONNECT_LANE(full_rate_d8),
      `CONNECT_LANE(ordinary_d16),
      `CONNECT_LANE(full_rate_d16)
    );

    wire [255:0] accepted = {accepted_full_rate_d16, accepted_ordinary_d16,
      accepted_full_rate_d8, accepted_ordinary_d8, accepted_full_rate_d4,
      accepted_ordinary_d4, accepted_full_rate_d2, accepted_ordinary_d2};
    wire [255:0] delivered = {delivered_full_rate_d16, delivered_ordinary_d16,
      delivered_full_rate_d8, delivered_ordinary_d8, delivered_full_rate_d4,
      delivered_ordinary_d4, delivered_full_rate_d2, delivered_ordinary_d2};
    wire [255:0] expected_sequence = {expected_full_rate_d16, expected_ordinary_d16,
      expected_full_rate_d8, expected_ordinary_d8, expected_full_rate_d4,
      expected_ordinary_d4, expected_full_rate_d2, expected_ordinary_d2};
    wire [255:0] digest = {digest_full_rate_d16, digest_ordinary_d16,
      digest_full_rate_d8, digest_ordinary_d8, digest_full_rate_d4,
      digest_ordinary_d4, digest_full_rate_d2, digest_ordinary_d2};
    wire [255:0] supply_gaps = {supply_gaps_full_rate_d16, supply_gaps_ordinary_d16,
      supply_gaps_full_rate_d8, supply_gaps_ordinary_d8, supply_gaps_full_rate_d4,
      supply_gaps_ordinary_d4, supply_gaps_full_rate_d2, supply_gaps_ordinary_d2};
    wire [255:0] source_backpressure = {source_bp_full_rate_d16, source_bp_ordinary_d16,
      source_bp_full_rate_d8, source_bp_ordinary_d8, source_bp_full_rate_d4,
      source_bp_ordinary_d4, source_bp_full_rate_d2, source_bp_ordinary_d2};
    wire [255:0] sink_backpressure = {sink_bp_full_rate_d16, sink_bp_ordinary_d16,
      sink_bp_full_rate_d8, sink_bp_ordinary_d8, sink_bp_full_rate_d4,
      sink_bp_ordinary_d4, sink_bp_full_rate_d2, sink_bp_ordinary_d2};
    wire [255:0] sink_ticks = {sink_ticks_full_rate_d16, sink_ticks_ordinary_d16,
      sink_ticks_full_rate_d8, sink_ticks_ordinary_d8, sink_ticks_full_rate_d4,
      sink_ticks_ordinary_d4, sink_ticks_full_rate_d2, sink_ticks_ordinary_d2};
    wire [7:0] data_errors = {data_error_full_rate_d16, data_error_ordinary_d16,
      data_error_full_rate_d8, data_error_ordinary_d8, data_error_full_rate_d4,
      data_error_ordinary_d4, data_error_full_rate_d2, data_error_ordinary_d2};
    wire [7:0] gap_errors = {gap_error_full_rate_d16, gap_error_ordinary_d16,
      gap_error_full_rate_d8, gap_error_ordinary_d8, gap_error_full_rate_d4,
      gap_error_ordinary_d4, gap_error_full_rate_d2, gap_error_ordinary_d2};

    BSCANE2 #(.JTAG_CHAIN(1)) u_bscan (
      .CAPTURE(capture), .DRCK(drck), .RESET(bscan_reset), .RUNTEST(runtest),
      .SEL(sel), .SHIFT(shift), .TCK(tck), .TDI(tdi), .TMS(tms),
      .UPDATE(update), .TDO(tdo));
    surface_matrix_bscan u_transport (
      .tck(tck), .sel(sel), .capture(capture), .shift(shift),
      .update(update), .tdi(tdi), .tdo(tdo),
      .clocks_ready(clocks_ready), .system_reset(rst),
      .source_heartbeat(source_heartbeat), .sink_heartbeat(sink_heartbeat),
      .accepted(accepted), .delivered(delivered),
      .expected_sequence(expected_sequence), .digest(digest),
      .supply_gaps(supply_gaps), .source_backpressure(source_backpressure),
      .sink_backpressure(sink_backpressure), .sink_ticks(sink_ticks),
      .data_errors(data_errors), .gap_errors(gap_errors),
      .recovery_status(2'b00),
      .command_epoch(command_epoch),
      .control(control), .run_limit(run_limit));

    assign leds[0] = clocks_ready;
    assign leds[1] = |data_errors | |gap_errors;
    assign leds[2] = &({delivered_full_rate_d16 == sink_run_limit,
                        delivered_ordinary_d16 == sink_run_limit,
                        delivered_full_rate_d8 == sink_run_limit,
                        delivered_ordinary_d8 == sink_run_limit,
                        delivered_full_rate_d4 == sink_run_limit,
                        delivered_ordinary_d4 == sink_run_limit,
                        delivered_full_rate_d2 == sink_run_limit,
                        delivered_ordinary_d2 == sink_run_limit});
    assign leds[3] = source_heartbeat[22] ^ sink_heartbeat[22];

`undef CONNECT_LANE
`undef DECLARE_LANE
endmodule

`default_nettype wire
