// s0blinky_top.v -- ZC702 board top for the Loom-emitted s0blinky core.
//
// Untrusted wrapper (testbench role): LVDS clock input buffers, a small
// power-on reset stretcher, and the LED pin mapping. All synchronous logic
// is the Loom-emitted module rtl/s0blinky.v (Machines/Substrate/S0Blinky.lean).
`timescale 1ns/1ps
`default_nettype none

module s0blinky_top (
    input  wire       sys_clk_p,
    input  wire       sys_clk_n,
    output wire [3:0] leds
);
    wire clk_ibuf, clk;
    IBUFDS u_ibufds (.I(sys_clk_p), .IB(sys_clk_n), .O(clk_ibuf));
    BUFG   u_bufg   (.I(clk_ibuf), .O(clk));

    // power-on reset: hold rst for 15 cycles out of configuration
    reg [3:0] por = 4'd0;
    always @(posedge clk) if (por != 4'hF) por <= por + 4'd1;
    wire rst = (por != 4'hF);

    wire [27:0] o_cnt;
    s0blinky u_core (.clk(clk), .rst(rst), .o_cnt(o_cnt));

    // 200 MHz / 2^24..27 -> visibly staggered blink across the 4 LEDs
    assign leds = {o_cnt[27], o_cnt[26], o_cnt[25], o_cnt[24]};
endmodule

`default_nettype wire
