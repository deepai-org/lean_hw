`timescale 1ns/1ps

// Physical-protocol corroboration for the pretty-authored independent-reset
// SoC Fabric.  A fabric recovery is requested with all three traffic classes
// resident.  The lossy epoch is measured, all twelve incident endpoint halves
// must complete, and a separate common reset starts the fresh application
// epoch whose full result is checked.
module tb_soc_fabric_recovery;
  reg cpu_fabric_clk = 0;
  reg dma_clk = 0;
  reg mem_clk = 0;
  reg mon_clk = 0;
  reg mon_run = 1;
  reg rst = 1;
  reg cpu_hold_issue = 0;
  reg dma_hold_issue = 0;
  reg fabric_recover = 0;

  always #5 cpu_fabric_clk = ~cpu_fabric_clk;
  always #7 dma_clk = ~dma_clk;
  always #9 mem_clk = ~mem_clk;
  always #11 if (mon_run) mon_clk = ~mon_clk;

  wire cpu_recovered, dma_recovered, fabric_recovered;
  wire service_recovered, monitor_recovered;
  wire [31:0] cpu_accepted, cpu_responses, cpu_digest;
  wire [31:0] dma_accepted, dma_responses, dma_digest;
  wire [31:0] cpu_grants, dma_grants, total_grants, routed;
  wire [31:0] commits, records, audit_digest, expected_digest;
  wire cpu_error, dma_error, fabric_error, monitor_error;

  // Exact physical FIFO occupancy at the recovery linearization cut. Pointer
  // widths are log2(depth)+1; early in the run ordinary subtraction is exact.
  wire [31:0] request_occupancy =
    ((dut.u_cpu_request.write_binary - dut.u_cpu_request.read_binary) & 3) +
    ((dut.u_dma_request.write_binary - dut.u_dma_request.read_binary) & 7) +
    ((dut.u_target_request.write_binary - dut.u_target_request.read_binary) & 7);
  wire [31:0] response_occupancy =
    ((dut.u_cpu_response.write_binary - dut.u_cpu_response.read_binary) & 3) +
    ((dut.u_dma_response.write_binary - dut.u_dma_response.read_binary) & 7) +
    ((dut.u_target_response.write_binary - dut.u_target_response.read_binary) & 7);
  wire [31:0] audit_occupancy =
    ((dut.u_audit.write_binary - dut.u_audit.read_binary) & 7);
  wire [31:0] incident_occupancy = request_occupancy + response_occupancy;

  integer lost_requests;
  integer lost_responses;
  integer retained_audit;

  localparam [31:0] LIMIT = 32'd256;

  loom_system dut (
    .cpu_fabric_clk(cpu_fabric_clk), .dma_clk(dma_clk),
    .mem_clk(mem_clk), .mon_clk(mon_clk), .rst(rst),
    .cpu__recover(1'b0), .cpu__recovered(cpu_recovered),
    .dma__recover(1'b0), .dma__recovered(dma_recovered),
    .fabric__recover(fabric_recover), .fabric__recovered(fabric_recovered),
    .service__recover(1'b0), .service__recovered(service_recovered),
    .monitor__recover(1'b0), .monitor__recovered(monitor_recovered),
    .cpu__hold_issue(cpu_hold_issue), .cpu__hold_response(1'b0),
    .cpu__transaction_limit(LIMIT),
    .cpu__o_requests_accepted(cpu_accepted),
    .cpu__o_responses_received(cpu_responses),
    .cpu__o_response_digest(cpu_digest),
    .cpu__o_sticky_error(cpu_error),
    .dma__hold_issue(dma_hold_issue), .dma__hold_response(1'b0),
    .dma__transaction_limit(LIMIT),
    .dma__o_requests_accepted(dma_accepted),
    .dma__o_responses_received(dma_responses),
    .dma__o_response_digest(dma_digest),
    .dma__o_sticky_error(dma_error),
    .fabric__hold_arbitration(1'b0),
    .fabric__o_cpu_grants(cpu_grants),
    .fabric__o_dma_grants(dma_grants),
    .fabric__o_total_grants(total_grants),
    .fabric__o_responses_routed(routed),
    .fabric__o_double_grant_error(fabric_error),
    .service__o_commits(commits),
    .monitor__o_records(records),
    .monitor__o_audit_digest(audit_digest),
    .monitor__o_expected_digest(expected_digest),
    .monitor__o_sticky_error(monitor_error)
  );

  task fail;
    input [255:0] reason;
    begin
      $display("SOC_RECOVERY_FAIL reason=%0s req_occ=%0d resp_occ=%0d audit_occ=%0d",
        reason, request_occupancy, response_occupancy, audit_occupancy);
      $finish_and_return(1);
    end
  endtask

  initial begin
    // Every domain samples the common initial reset before the adversarial
    // monitor pause creates simultaneous request/response/audit pressure.
    #115 rst = 0;
    #44 mon_run = 0;

    wait (request_occupancy > 0 && response_occupancy > 0 && audit_occupancy > 0);
    cpu_hold_issue = 1;
    dma_hold_issue = 1;
    lost_requests = request_occupancy;
    lost_responses = response_occupancy;
    retained_audit = audit_occupancy;
    $display("RECOVERY_CUT lost_requests=%0d lost_responses=%0d unaffected_audit=%0d accepted=%0d/%0d responses=%0d/%0d",
      lost_requests, lost_responses, retained_audit,
      cpu_accepted, dma_accepted, cpu_responses, dma_responses);

    fabric_recover = 1;
    wait (fabric_recovered === 1'b1);
    repeat (2) @(posedge cpu_fabric_clk);
    if (incident_occupancy != 0)
      fail("incident queues not empty at completion");
    if (lost_requests == 0 || lost_responses == 0 || retained_audit == 0)
      fail("traffic class absent at cut");
    $display("RECOVERY_COMPLETE endpoints=12 discarded=%0d incident_occupancy=%0d",
      lost_requests + lost_responses, incident_occupancy);
    fabric_recover = 0;

    // Loss-explicit channel recovery is not application replay.  Resume the
    // monitor so every domain samples the supported common reset, then start a
    // fresh application epoch and require full forward progress.
    mon_run = 1;
    rst = 1;
    repeat (20) @(posedge cpu_fabric_clk);
    rst = 0;
    cpu_hold_issue = 0;
    dma_hold_issue = 0;

    wait (cpu_responses == LIMIT && dma_responses == LIMIT &&
          records == (LIMIT << 1));
    repeat (12) @(posedge cpu_fabric_clk);
    $display("RESTART_METRICS cpu_accepted=%0d cpu_responses=%0d cpu_digest=%08x dma_accepted=%0d dma_responses=%0d dma_digest=%08x cpu_grants=%0d dma_grants=%0d total_grants=%0d routed=%0d commits=%0d records=%0d audit_digest=%08x expected_digest=%08x errors=%0d%0d%0d%0d",
      cpu_accepted, cpu_responses, cpu_digest,
      dma_accepted, dma_responses, dma_digest,
      cpu_grants, dma_grants, total_grants, routed, commits, records,
      audit_digest, expected_digest,
      cpu_error, dma_error, fabric_error, monitor_error);
    if (cpu_accepted != LIMIT || cpu_responses != LIMIT ||
        dma_accepted != LIMIT || dma_responses != LIMIT ||
        cpu_grants != LIMIT || dma_grants != LIMIT ||
        total_grants != (LIMIT << 1) || routed != (LIMIT << 1) ||
        commits != (LIMIT << 1) || records != (LIMIT << 1))
      fail("fresh epoch counts");
    if (cpu_digest != 0 || dma_digest != 0 || audit_digest != 0 ||
        expected_digest != 0 || cpu_error || dma_error ||
        fabric_error || monitor_error)
      fail("fresh epoch oracle");
    $display("SOC_RECOVERY_PASS");
    $finish;
  end

  initial begin
    #4000000;
    fail("timeout");
  end
endmodule
