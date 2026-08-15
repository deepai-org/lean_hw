`timescale 1ns/1ps
`default_nettype none

module surface_reset_release_tb;
  reg clk200 = 1'b0;
  reg startup_ready = 1'b0;
  reg reset_request_async = 1'b1;
  wire clocks_enable, rst, ready;
  reg saw_gated_reset_release = 1'b0;
  reg previous_rst = 1'b1;

  always #2.5 clk200 = ~clk200;
  surface_reset_release dut (
    .clk200(clk200), .startup_ready(startup_ready),
    .reset_request_async(reset_request_async),
    .clocks_enable(clocks_enable), .rst(rst), .ready(ready));

  always @(posedge clk200) begin
    #1;
    if (previous_rst && !rst) begin
      if (clocks_enable) $fatal(1, "reset deasserted while domain clocks enabled");
      saw_gated_reset_release = 1'b1;
    end
    previous_rst = rst;
  end

  task wait_ready;
    integer timeout;
    begin
      timeout = 0;
      while (!ready && timeout < 100) begin
        @(posedge clk200); #1;
        timeout = timeout + 1;
      end
      if (!ready) $fatal(1, "reset release timed out");
      if (rst || !clocks_enable) $fatal(1, "ready asserted in wrong state");
    end
  endtask

  initial begin
    repeat (4) @(posedge clk200);
    startup_ready = 1'b1;
    reset_request_async = 1'b0;
    wait_ready();
    if (!saw_gated_reset_release) $fatal(1, "startup release was not gated");

    reset_request_async = 1'b1;
    repeat (6) @(posedge clk200); #1;
    if (!rst || !clocks_enable || ready)
      $fatal(1, "asserted reset did not run both clocks");
    saw_gated_reset_release = 1'b0;
    reset_request_async = 1'b0;
    wait_ready();
    if (!saw_gated_reset_release) $fatal(1, "runtime release was not gated");
    $display("SURFACE_RESET_RELEASE_RTL_PASS assertion=clocks_running release=clocks_gated restart=synchronous_bufgce");
    $finish;
  end
endmodule

`default_nettype wire
