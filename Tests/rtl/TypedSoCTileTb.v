`timescale 1ns/1ps

module TypedSoCTileTb #(
  parameter integer LIMIT = 2048
);
  localparam integer EXPECTED = 2 * LIMIT - 1;

  reg core_clk = 0;
  reg memory_clk = 0;
  reg rst = 1;
  always #5 core_clk = ~core_clk;
  always #7 memory_clk = ~memory_clk;

  reg [19:0] run_a = LIMIT;
  reg [19:0] run_b = LIMIT;
  reg hold_a = 0;
  reg hold_b = 0;
  reg flush = 0;
  reg memory_hold_internal = 0;
  reg memory_hold_contract = 0;
  reg response_hold = 0;

  wire pipeline0_full, pipeline1_full, pipeline2_full;
  wire [19:0] source_sequence_a, source_sequence_b;
  wire [31:0] source_accepted_a, source_accepted_b;
  wire [31:0] source_stalls_a, source_stalls_b;
  wire [31:0] grant_a, grant_b, contention, endpoint_sent;
  wire endpoint_valid;
  wire [65:0] endpoint_payload;
  wire internal_pending, contract_pending;
  wire [31:0] internal_commits, contract_commits;
  wire [31:0] internal_request_stalls, internal_response_stalls;
  wire [31:0] contract_request_stalls, contract_response_stalls;
  wire [19:0] expected_a, expected_b;
  wire [31:0] records, discarded, digest;
  wire discarded_client;
  wire [19:0] discarded_sequence;
  wire flush_gap_seen, sticky_error;
  wire [31:0] pair_skew_ticks, response_hold_ticks;

  loom_system dut (
    .tile_core_clk(core_clk), .tile_memory_clk(memory_clk), .rst(rst),
    .tile_core__source_a__run_limit(run_a),
    .tile_core__source_a__producer_hold(hold_a),
    .tile_core__source_b__run_limit(run_b),
    .tile_core__source_b__producer_hold(hold_b),
    .tile_core__pipeline_1__flush(flush),
    .tile_core__o_pipeline_0__full(pipeline0_full),
    .tile_core__o_pipeline_1__full(pipeline1_full),
    .tile_core__o_pipeline_2__full(pipeline2_full),
    .tile_core__o_source_a__sequence(source_sequence_a),
    .tile_core__o_source_a__accepted(source_accepted_a),
    .tile_core__o_source_a__stalls(source_stalls_a),
    .tile_core__o_source_b__sequence(source_sequence_b),
    .tile_core__o_source_b__accepted(source_accepted_b),
    .tile_core__o_source_b__stalls(source_stalls_b),
    .tile_core__o_arbiter__grant_a(grant_a),
    .tile_core__o_arbiter__grant_b(grant_b),
    .tile_core__o_arbiter__contention(contention),
    .tile_core__o_request_endpoint__valid(endpoint_valid),
    .tile_core__o_request_endpoint__payload(endpoint_payload),
    .tile_core__o_request_endpoint__sent(endpoint_sent),
    .tile_memory_internal__memory_hold(memory_hold_internal),
    .tile_memory_internal__o_pending(internal_pending),
    .tile_memory_internal__o_commits(internal_commits),
    .tile_memory_internal__o_request_stalls(internal_request_stalls),
    .tile_memory_internal__o_response_stalls(internal_response_stalls),
    .tile_memory_contract__memory_hold(memory_hold_contract),
    .tile_memory_contract__o_pending(contract_pending),
    .tile_memory_contract__o_commits(contract_commits),
    .tile_memory_contract__o_request_stalls(contract_request_stalls),
    .tile_memory_contract__o_response_stalls(contract_response_stalls),
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
    .tile_monitor__o_response_hold_ticks(response_hold_ticks)
  );

  integer core_ticks = 0;
  integer memory_ticks = 0;
  reg restarted = 0;
  reg loading_reset = 0;
  reg flushed = 0;

  always @(posedge core_clk) begin
    if (rst) begin
      core_ticks <= 0;
      flushed <= 0;
      flush <= 0;
      hold_a <= 0;
      hold_b <= 0;
      response_hold <= 0;
    end else begin
      core_ticks <= core_ticks + 1;
      hold_a <= !loading_reset && ((core_ticks % 47) == 9);
      hold_b <= !loading_reset && ((core_ticks % 61) >= 54);
      response_hold <= loading_reset || ((core_ticks % 83) >= 75);
      flush <= 0;
      if (restarted && !flushed && pipeline1_full && records > 50) begin
        flush <= 1;
        flushed <= 1;
      end
    end
  end

  always @(posedge memory_clk) begin
    if (rst) begin
      memory_ticks <= 0;
      memory_hold_internal <= 0;
      memory_hold_contract <= 0;
    end else begin
      memory_ticks <= memory_ticks + 1;
      memory_hold_internal <= !loading_reset && ((memory_ticks % 43) >= 39);
      memory_hold_contract <= !loading_reset && ((memory_ticks % 71) == 17);
    end
  end

  task fail;
    input [8*120-1:0] why;
    begin
      $display("TYPED_SOC_TILE_FAIL %0s records=%0d commits=%0d/%0d expected=%0d/%0d discarded=%0d sticky=%0d",
        why, records, internal_commits, contract_commits, expected_a, expected_b,
        discarded, sticky_error);
      $finish(1);
    end
  endtask

  initial begin
    repeat (8) @(posedge core_clk);
    rst = 0;

    // Create simultaneous request and response residency, then exercise the
    // supported coordinated reset with both clocks continuing to run.
    wait (records >= 200);
    loading_reset = 1;
    wait (pipeline0_full && internal_pending && contract_pending);
    repeat (20) @(posedge core_clk);
    rst = 1;
    repeat (8) @(posedge core_clk);
    rst = 0;
    loading_reset = 0;
    restarted = 1;

    wait (records == EXPECTED);
    repeat (30) @(posedge core_clk);
    if (sticky_error) fail("sticky checker");
    if (!flush_gap_seen || discarded != 1) fail("flush accounting");
    if (internal_commits != EXPECTED || contract_commits != EXPECTED)
      fail("lane ledger mismatch");
    if (source_sequence_a != LIMIT || source_sequence_b != LIMIT ||
        source_accepted_a != LIMIT || source_accepted_b != LIMIT)
      fail("source ledger mismatch");
    if (grant_a != LIMIT || grant_b != LIMIT ||
        grant_a != source_accepted_a || grant_b != source_accepted_b)
      fail("round-robin arbitration ledger mismatch");
    if (contention == 0 || endpoint_sent != EXPECTED)
      fail("arbiter/endpoint coverage mismatch");
    if (expected_a != LIMIT || expected_b != LIMIT)
      fail("per-client sequence mismatch");
    if (digest != 32'h0000_0022) fail("exact response digest mismatch");
    if (internal_request_stalls == 0 || contract_request_stalls == 0 ||
        response_hold_ticks == 0) fail("pause coverage absent");
    $display("TYPED_SOC_TILE_PASS records=%0d digest=%08x request_stalls=%0d/%0d response_stalls=%0d/%0d pair_skew=%0d",
      records, digest, internal_request_stalls, contract_request_stalls,
      internal_response_stalls, contract_response_stalls, pair_skew_ticks);
    $finish(0);
  end

  initial begin
    repeat (LIMIT * 8 + 100000) @(posedge core_clk);
    fail("timeout");
  end
endmodule
