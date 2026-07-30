// s0bscan_top.v -- ZC702 board top for the Loom-emitted s0bscan core (the
// first OPEN Loom design: D15 input ports driven by the JTAG bridge).
//
// Untrusted wrapper: clock buffers, POR, BSCANE2 USER1 + 41-bit DR
// (jtag_lib.tcl protocol: [40]=wr, [39]=region, [38:32]=idx, [31:0]=data;
// the library shifts 42 bits -- the PS TAP in BYPASS eats one), and the
// UPDATE->sysclk toggle-sync CDC (s1/s13 lineage) that delivers each JTAG
// transaction as a one-cycle cmd_valid pulse on the Loom module's ports.
// Reads: rd_reg is latched by the core one sysclk after the pulse and is
// stable microseconds before the next scan's CAPTURE samples it.
`timescale 1ns/1ps
`default_nettype none

module s0bscan_top (
    input  wire       sys_clk_p,
    input  wire       sys_clk_n,
    output wire [3:0] leds
);
    wire clk_ibuf, clk;
    IBUFDS u_ibufds (.I(sys_clk_p), .IB(sys_clk_n), .O(clk_ibuf));
    BUFG   u_bufg   (.I(clk_ibuf), .O(clk));

    reg [3:0] por = 4'd0;
    always @(posedge clk) if (por != 4'hF) por <= por + 4'd1;
    wire rst = (por != 4'hF);

    // ---- BSCANE2 USER1 + DR shift (DRCK/UPDATE domains) ----
    wire capture, drck, sel, shift, tdi, update, tdo;
    BSCANE2 #(.JTAG_CHAIN(1)) u_bscan (
        .CAPTURE(capture), .DRCK(drck), .RESET(), .RUNTEST(),
        .SEL(sel), .SHIFT(shift), .TCK(), .TDI(tdi), .TMS(),
        .UPDATE(update), .TDO(tdo)
    );

    wire [31:0] o_rd_reg;
    reg  [40:0] dr = 41'd0;
    always @(posedge drck) begin
        if (sel) begin
            if (capture)    dr <= {9'b0, o_rd_reg};
            else if (shift) dr <= {tdi, dr[40:1]};
        end
    end
    assign tdo = dr[0];

    // UPDATE latches the transaction and flips the toggle
    reg        cmd_tog = 1'b0;
    reg        lat_wr = 1'b0, lat_bram = 1'b0;
    reg [6:0]  lat_idx = 7'd0;
    reg [31:0] lat_dat = 32'd0;
    always @(posedge update) begin
        if (sel) begin
            lat_wr   <= dr[40];
            lat_bram <= dr[39];
            lat_idx  <= dr[38:32];
            lat_dat  <= dr[31:0];
            cmd_tog  <= ~cmd_tog;
        end
    end

    // toggle-sync into sysclk -> one-cycle cmd_valid pulse
    reg t0 = 1'b0, t1 = 1'b0, t2 = 1'b0;
    always @(posedge clk) begin t0 <= cmd_tog; t1 <= t0; t2 <= t1; end
    wire cmd_valid = t1 ^ t2;

    // ---- the Loom core (open design: D15 input ports) ----
    wire [31:0] o_scratch, o_hb;
    wire [3:0]  o_led;
    wire [4:0]  o_con_idx;
    s0bscan u_core (
        .clk(clk), .rst(rst),
        .cmd_valid(cmd_valid), .cmd_wr(lat_wr), .cmd_bram(lat_bram),
        .cmd_idx(lat_idx), .cmd_wdata(lat_dat),
        .o_scratch(o_scratch), .o_led(o_led), .o_con_idx(o_con_idx),
        .o_rd_reg(o_rd_reg), .o_hb(o_hb)
    );

    assign leds = o_led;
endmodule

`default_nettype wire
