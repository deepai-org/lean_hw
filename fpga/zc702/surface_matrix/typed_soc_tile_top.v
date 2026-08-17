`timescale 1ns/1ps
`default_nettype none

// Board shell for the Typed SoC Composition Tile.  It deliberately reuses the
// Surface Matrix independent roots, coordinated reset release, and BSCAN
// transport; only the application controls and ledger packing differ.
module typed_soc_tile_top (
    input wire sys_clk_p, input wire sys_clk_n,
    input wire usr_clk_p, input wire usr_clk_n,
    output wire [3:0] leds
);
    wire clk200_raw, clk200;
    IBUFDS #(.DIFF_TERM("TRUE"), .IBUF_LOW_PWR("FALSE"))
      u_sys_ibuf (.I(sys_clk_p), .IB(sys_clk_n), .O(clk200_raw));
    BUFG u_sys_bufg (.I(clk200_raw), .O(clk200));
    wire [3:0] ps_fclk;
    PS7 u_ps7 (.FCLKCLK(ps_fclk));
    wire clocks_enable, core_clk, memory_clk;
    // openXC7 0.8.2 neither produced a locking MMCM configuration nor exposes
    // BUFR sites in this chip database.  Keep its target-only fallback visible:
    // a two-bit divider followed by global glitch-free distribution.  The
    // divider itself never pauses; BUFGCE owns coordinated clock stopping.
    // 50:100 MHz gives periodically coincident edges and ample routed margin.
    (* keep = "true" *) reg [1:0] core_divider = 2'd0;
    always @(posedge clk200) core_divider <= core_divider + 1'b1;
    BUFGCE #(.CE_TYPE("SYNC")) u_core_gate
      (.I(core_divider[1]), .CE(clocks_enable), .O(core_clk));
    BUFGCE #(.CE_TYPE("SYNC")) u_memory_gate
      (.I(ps_fclk[0]), .CE(clocks_enable), .O(memory_clk));

    wire capture, drck, bscan_reset, runtest, sel, shift, tck, tdi, tms, update, tdo;
    wire [7:0] control;
    wire [31:0] run_limit;
    wire command_epoch;
    (* ASYNC_REG = "TRUE" *) reg core_command_sync0 = 1'b0;
    (* ASYNC_REG = "TRUE" *) reg core_command_sync1 = 1'b0;
    reg core_command_seen = 1'b0;
    reg [19:0] core_run_limit = 20'd0;
    reg core_enable = 1'b0;
    reg flush_enable = 1'b0;
    reg force_response_hold = 1'b0;
    (* ASYNC_REG = "TRUE" *) reg memory_command_sync0 = 1'b0;
    (* ASYNC_REG = "TRUE" *) reg memory_command_sync1 = 1'b0;
    reg memory_command_seen = 1'b0;
    reg memory_enable = 1'b0;
    reg force_memory_hold = 1'b0;

    always @(posedge core_clk) begin
      core_command_sync0 <= command_epoch;
      core_command_sync1 <= core_command_sync0;
      if (core_command_sync1 != core_command_seen) begin
        core_command_seen <= core_command_sync1;
        core_run_limit <= run_limit[19:0];
        core_enable <= control[0];
        flush_enable <= control[3];
        force_response_hold <= control[4];
      end
    end
    always @(posedge memory_clk) begin
      memory_command_sync0 <= command_epoch;
      memory_command_sync1 <= memory_command_sync0;
      if (memory_command_sync1 != memory_command_seen) begin
        memory_command_seen <= memory_command_sync1;
        memory_enable <= control[1];
        force_memory_hold <= control[5];
      end
    end

    reg [7:0] startup_count = 8'd0;
    always @(posedge clk200)
      if (!startup_count[7]) startup_count <= startup_count + 8'd1;
    wire rst, clocks_ready;
    surface_reset_release u_reset_release (
      .clk200(clk200), .startup_ready(startup_count[7]),
      .reset_request_async(control[2]),
      .clocks_enable(clocks_enable), .rst(rst), .ready(clocks_ready));

    reg [31:0] core_ticks = 32'd0;
    reg [31:0] memory_ticks = 32'd0;
    always @(posedge core_clk) core_ticks <= core_ticks + 1'b1;
    always @(posedge memory_clk) memory_ticks <= memory_ticks + 1'b1;

    wire producer_hold_a = !core_enable ||
      ((core_ticks[7:0] >= 8'd31) && (core_ticks[7:0] < 8'd35));
    wire producer_hold_b = !core_enable ||
      ((core_ticks[8:0] >= 9'd173) && (core_ticks[8:0] < 9'd179));
    wire memory_hold_internal = !memory_enable || force_memory_hold ||
      ((memory_ticks[7:0] >= 8'd71) && (memory_ticks[7:0] < 8'd75));
    wire memory_hold_contract = !memory_enable || force_memory_hold ||
      ((memory_ticks[8:0] >= 9'd299) && (memory_ticks[8:0] < 9'd304));
    wire response_hold = !core_enable || force_response_hold ||
      ((core_ticks[8:0] >= 9'd411) && (core_ticks[8:0] < 9'd418));

    wire pipeline_0_full, pipeline_1_full, pipeline_2_full;
    reg flush_done = 1'b0;
    reg pipeline_flush = 1'b0;
    always @(posedge core_clk) begin
      if (rst) begin
        flush_done <= 1'b0;
        pipeline_flush <= 1'b0;
      end else begin
        pipeline_flush <= 1'b0;
        if (flush_enable && !flush_done && pipeline_1_full) begin
          pipeline_flush <= 1'b1;
          flush_done <= 1'b1;
        end
      end
    end

    wire [19:0] sequence_a, sequence_b;
    wire [31:0] accepted_a, accepted_b, source_stalls_a, source_stalls_b;
    wire [31:0] grant_a, grant_b, contention, endpoint_sent;
    wire endpoint_valid;
    wire [65:0] endpoint_payload;
    wire pending_internal, pending_contract;
    wire [31:0] commits_internal, commits_contract;
    wire [31:0] request_stalls_internal, request_stalls_contract;
    wire [31:0] response_stalls_internal, response_stalls_contract;
    wire [19:0] expected_a, expected_b;
    wire [31:0] records, discarded, digest, pair_skew_ticks, response_hold_ticks;
    wire discarded_client;
    wire [19:0] discarded_sequence;
    wire flush_gap_seen, sticky_error;

    loom_system u_tile (
      .tile_core_clk(core_clk), .tile_memory_clk(memory_clk), .rst(rst),
      .tile_core__source_a__run_limit(core_run_limit),
      .tile_core__source_a__producer_hold(producer_hold_a),
      .tile_core__source_b__run_limit(core_run_limit),
      .tile_core__source_b__producer_hold(producer_hold_b),
      .tile_core__pipeline_1__flush(pipeline_flush),
      .tile_core__o_pipeline_0__full(pipeline_0_full),
      .tile_core__o_pipeline_1__full(pipeline_1_full),
      .tile_core__o_pipeline_2__full(pipeline_2_full),
      .tile_core__o_source_a__sequence(sequence_a),
      .tile_core__o_source_a__accepted(accepted_a),
      .tile_core__o_source_a__stalls(source_stalls_a),
      .tile_core__o_source_b__sequence(sequence_b),
      .tile_core__o_source_b__accepted(accepted_b),
      .tile_core__o_source_b__stalls(source_stalls_b),
      .tile_core__o_arbiter__grant_a(grant_a),
      .tile_core__o_arbiter__grant_b(grant_b),
      .tile_core__o_arbiter__contention(contention),
      .tile_core__o_request_endpoint__valid(endpoint_valid),
      .tile_core__o_request_endpoint__payload(endpoint_payload),
      .tile_core__o_request_endpoint__sent(endpoint_sent),
      .tile_memory_internal__memory_hold(memory_hold_internal),
      .tile_memory_internal__o_pending(pending_internal),
      .tile_memory_internal__o_commits(commits_internal),
      .tile_memory_internal__o_request_stalls(request_stalls_internal),
      .tile_memory_internal__o_response_stalls(response_stalls_internal),
      .tile_memory_contract__memory_hold(memory_hold_contract),
      .tile_memory_contract__o_pending(pending_contract),
      .tile_memory_contract__o_commits(commits_contract),
      .tile_memory_contract__o_request_stalls(request_stalls_contract),
      .tile_memory_contract__o_response_stalls(response_stalls_contract),
      .tile_monitor__response_hold(response_hold),
      .tile_monitor__o_expected_a(expected_a),
      .tile_monitor__o_expected_b(expected_b),
      .tile_monitor__o_records(records),
      .tile_monitor__o_discarded(discarded),
      .tile_monitor__o_digest(digest),
      .tile_monitor__o_discarded_client(discarded_client),
      .tile_monitor__o_discarded_sequence(discarded_sequence),
      .tile_monitor__o_flush_gap_seen(flush_gap_seen),
      .tile_monitor__o_sticky_error(sticky_error),
      .tile_monitor__o_pair_skew_ticks(pair_skew_ticks),
      .tile_monitor__o_response_hold_ticks(response_hold_ticks));

    // Reuse the Surface Matrix 8-lane scan frame as eight named 32-bit banks.
    wire [255:0] accepted_words = {grant_b, grant_a, source_stalls_b,
      source_stalls_a, endpoint_sent, accepted_b, accepted_a, {12'd0, sequence_a}};
    wire [255:0] delivered_words = {response_hold_ticks, pair_skew_ticks,
      response_stalls_contract, response_stalls_internal,
      request_stalls_contract, request_stalls_internal, commits_contract, records};
    wire [255:0] expected_words = {128'd0,
      {12'd0, expected_b}, {12'd0, expected_a},
      {12'd0, sequence_b}, {12'd0, sequence_a}};
    wire [255:0] digest_words = {224'd0, digest};
    wire [255:0] status_words = {225'd0, 22'd0, endpoint_valid,
      pending_contract, pending_internal, pipeline_2_full, pipeline_1_full,
      pipeline_0_full, flush_done, flush_gap_seen, sticky_error};
    wire [7:0] error_words = {7'd0, sticky_error};

    BSCANE2 #(.JTAG_CHAIN(1)) u_bscan (
      .CAPTURE(capture), .DRCK(drck), .RESET(bscan_reset), .RUNTEST(runtest),
      .SEL(sel), .SHIFT(shift), .TCK(tck), .TDI(tdi), .TMS(tms),
      .UPDATE(update), .TDO(tdo));
    surface_matrix_bscan #(
      .ID_MAGIC_VALUE(32'h5453_4354), .UPDATE_SHIFT(1)) u_transport (
      .tck(tck), .sel(sel), .capture(capture), .shift(shift),
      .update(update), .tdi(tdi), .tdo(tdo),
      .clocks_ready(clocks_ready), .system_reset(rst),
      .source_heartbeat(core_ticks), .sink_heartbeat(memory_ticks),
      .accepted(accepted_words), .delivered(delivered_words),
      .expected_sequence(expected_words), .digest(digest_words),
      .supply_gaps(status_words),
      .source_backpressure({160'd0, commits_internal, discarded, contention}),
      .sink_backpressure({224'd0, 11'd0, discarded_client, discarded_sequence}),
      .sink_ticks(256'd0),
      .data_errors(error_words), .gap_errors(8'd0),
      .recovery_status({flush_gap_seen, flush_done}),
      .command_epoch(command_epoch), .control(control), .run_limit(run_limit));

    assign leds[0] = clocks_ready;
    assign leds[1] = sticky_error;
    assign leds[2] = (records + discarded == {12'd0, sequence_a} + {12'd0, sequence_b});
    assign leds[3] = core_ticks[22] ^ memory_ticks[22];
endmodule

`default_nettype wire
