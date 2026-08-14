`timescale 1ns/1ps

// The same testbench is compiled once with the neutral system.v and once with
// the registered-BRAM target system.v.  It intentionally observes only the
// public Loom top, so physical-leaf selection cannot alter the oracle.
module tb_soc_fabric_storage_neutrality;
  reg cpu_fabric_clk = 0;
  reg dma_clk = 0;
  reg mem_clk = 0;
  reg mon_clk = 0;
  reg rst = 1;

  always #5  cpu_fabric_clk = ~cpu_fabric_clk;
  always #7  dma_clk = ~dma_clk;
  always #9  mem_clk = ~mem_clk;
  always #11 mon_clk = ~mon_clk;

  wire [31:0] cpu_staged, cpu_accepted, cpu_responses, cpu_digest;
  wire [31:0] dma_staged, dma_accepted, dma_responses, dma_digest;
  wire [31:0] cpu_grants, dma_grants, total_grants, routed;
  wire [31:0] commits, records, audit_digest, expected_digest;
  wire cpu_error, dma_error, fabric_error, monitor_error;

  localparam [31:0] LIMIT = 32'd256;

  loom_system dut (
    .cpu_fabric_clk(cpu_fabric_clk), .dma_clk(dma_clk),
    .mem_clk(mem_clk), .mon_clk(mon_clk), .rst(rst),
    .cpu__hold_issue(1'b0), .cpu__hold_response(1'b0),
    .cpu__transaction_limit(LIMIT),
    .cpu__o_requests_staged(cpu_staged),
    .cpu__o_requests_accepted(cpu_accepted),
    .cpu__o_responses_received(cpu_responses),
    .cpu__o_response_digest(cpu_digest),
    .cpu__o_sticky_error(cpu_error),
    .dma__hold_issue(1'b0), .dma__hold_response(1'b0),
    .dma__transaction_limit(LIMIT),
    .dma__o_requests_staged(dma_staged),
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
      $display("STORAGE_NEUTRALITY_FAIL reason=%0s", reason);
      $finish_and_return(1);
    end
  endtask

  initial begin
    #115 rst = 0;
    wait (cpu_responses == LIMIT && dma_responses == LIMIT &&
          records == (LIMIT << 1));
    repeat (12) @(posedge cpu_fabric_clk);
    $display("METRICS cpu_staged=%0d cpu_accepted=%0d cpu_responses=%0d cpu_digest=%08x dma_staged=%0d dma_accepted=%0d dma_responses=%0d dma_digest=%08x cpu_grants=%0d dma_grants=%0d total_grants=%0d routed=%0d commits=%0d records=%0d audit_digest=%08x expected_digest=%08x errors=%0d%0d%0d%0d",
      cpu_staged, cpu_accepted, cpu_responses, cpu_digest,
      dma_staged, dma_accepted, dma_responses, dma_digest,
      cpu_grants, dma_grants, total_grants, routed, commits, records,
      audit_digest, expected_digest,
      cpu_error, dma_error, fabric_error, monitor_error);
    if (cpu_staged != LIMIT || cpu_accepted != LIMIT ||
        cpu_responses != LIMIT || dma_staged != LIMIT ||
        dma_accepted != LIMIT || dma_responses != LIMIT)
      fail("client counts");
    if (cpu_grants != LIMIT || dma_grants != LIMIT ||
        total_grants != (LIMIT << 1) || routed != (LIMIT << 1) ||
        commits != (LIMIT << 1) || records != (LIMIT << 1))
      fail("fabric/service counts");
    if (cpu_digest != 0 || dma_digest != 0 || audit_digest != 0 ||
        expected_digest != 0)
      fail("digest");
    if (cpu_error || dma_error || fabric_error || monitor_error)
      fail("sticky error");
    $display("STORAGE_NEUTRALITY_PASS");
    $finish;
  end

  initial begin
    #2000000;
    fail("timeout");
  end
endmodule
