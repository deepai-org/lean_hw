`timescale 1ns/1ps
`default_nettype none

// Target-only realization of Loom's common synchronous-reset contract for
// unrelated clocks. Assertion is held while both domains run. Release gates
// both roots, lowers reset while they are stopped, then restarts them after a
// settling interval. BUFGCE supplies the glitch-free clock gating itself.
module surface_reset_release (
    input wire clk200,
    input wire startup_ready,
    input wire reset_request_async,
    output wire clocks_enable,
    output wire rst,
    output wire ready
);
    (* ASYNC_REG = "TRUE" *) reg request_sync0 = 1'b1;
    (* ASYNC_REG = "TRUE" *) reg request_sync1 = 1'b1;
    reg [4:0] release_count = 5'd0;
    reg clocks_enable_reg = 1'b1;
    reg rst_reg = 1'b1;

    always @(posedge clk200) begin
      request_sync0 <= reset_request_async;
      request_sync1 <= request_sync0;
      if (!startup_ready || request_sync1) begin
        release_count <= 5'd0;
        clocks_enable_reg <= 1'b1;
        rst_reg <= 1'b1;
      end else if (release_count < 5'd21) begin
        release_count <= release_count + 5'd1;
        if (release_count == 5'd0)
          clocks_enable_reg <= 1'b0;
        if (release_count == 5'd8)
          rst_reg <= 1'b0;
        if (release_count == 5'd16)
          clocks_enable_reg <= 1'b1;
      end
    end

    assign clocks_enable = clocks_enable_reg;
    assign rst = rst_reg;
    assign ready = startup_ready && release_count == 5'd21 &&
      clocks_enable_reg && !rst_reg;
endmodule

`default_nettype wire
