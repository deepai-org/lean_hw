// s13soak_top.v -- ZC702 board top for the Loom-emitted s13soak core.
//
// Untrusted wrapper (testbench role): clock buffers + divider, power-on
// reset, a BSCANE2 USER1 register bridge for reading the frozen engine
// state, and LED status. All synchronous soak logic is the Loom-emitted
// module rtl/s13soak.v (Machines/Substrate/S13Soak.lean).
//
// The core self-times: it runs exactly K=100000 cycles from reset and
// freezes. Reads of the frozen outputs over BSCAN are CDC-safe (static
// values); only the heartbeat is live (sampled 2FF, tearing acceptable).
//
// JTAG protocol = lnp64mini3's (jtag_lib.tcl rd/wr work unchanged):
// 41-bit DR on USER1: [40]=write, [38:32]=index, [31:0]=data. The library
// shifts 42 bits per scan — the Zynq PS TAP sits in BYPASS in the same
// chain and eats one bit. Reads are pipelined: scan N issues the index,
// scan N+1's capture returns the value.
//
// Register map:
//   0  ID        = 0x5330100E  (Loom s13soak)
//   1  SCRATCH   rw            (bridge sanity)
//   2  HEARTBEAT ro            (live sysclk counter, CDC-sampled)
//   3  RSTCTL    rw [0]=hold core in reset (re-arm: write 1, then 0)
//   81 cyc  82 injected  83 serviced  84 err  85 maxout
//   86 dma_sub  87 dma_comp  88 tmr_exp
//   90 lfsr  91 ptr  92 tmr  93 {dma_cd,dma_busy}  94 pending byte
//   100..107 age0..age7
`timescale 1ns/1ps
`default_nettype none

module s13soak_top (
    input  wire       sys_clk_p,
    input  wire       sys_clk_n,
    output wire [3:0] leds
);
    // 200 MHz board clock; the soak core runs at /8 = 25 MHz (the emitted
    // popcount/accounting adder chains need the slack; determinism is
    // cycle-based so the divider does not affect the frozen state).
    wire clk_ibuf, clk200;
    IBUFDS u_ibufds (.I(sys_clk_p), .IB(sys_clk_n), .O(clk_ibuf));
    BUFG   u_bufg   (.I(clk_ibuf), .O(clk200));

    reg [2:0] div = 3'd0;
    always @(posedge clk200) div <= div + 3'd1;
    wire clk;
    BUFG u_bufg_core (.I(div[2]), .O(clk));

    reg [31:0] heartbeat = 32'd0;
    always @(posedge clk200) heartbeat <= heartbeat + 32'd1;

    // power-on reset (core clock domain) + JTAG re-arm hold
    reg [3:0] por = 4'd0;
    always @(posedge clk) if (por != 4'hF) por <= por + 4'd1;
    reg rst_hold = 1'b0;                    // set over BSCAN to re-arm
    wire rst = (por != 4'hF) | rst_hold;

    // ---- Loom core ----
    wire [31:0] o_cyc, o_injected, o_serviced, o_err, o_maxout;
    wire [31:0] o_dma_sub, o_dma_comp, o_tmr_exp;
    wire [15:0] o_lfsr, o_tmr;
    wire [2:0]  o_ptr;
    wire        o_dma_busy;
    wire [3:0]  o_dma_cd;
    wire [7:0]  o_pend;
    wire [10:0] o_age [0:7];
    s13soak u_core (
        .clk(clk), .rst(rst),
        .o_cyc(o_cyc), .o_lfsr(o_lfsr), .o_ptr(o_ptr), .o_tmr(o_tmr),
        .o_dma_busy(o_dma_busy), .o_dma_cd(o_dma_cd),
        .o_injected(o_injected), .o_serviced(o_serviced), .o_err(o_err),
        .o_maxout(o_maxout), .o_dma_sub(o_dma_sub), .o_dma_comp(o_dma_comp),
        .o_tmr_exp(o_tmr_exp),
        .o_pend0(o_pend[0]), .o_pend1(o_pend[1]), .o_pend2(o_pend[2]),
        .o_pend3(o_pend[3]), .o_pend4(o_pend[4]), .o_pend5(o_pend[5]),
        .o_pend6(o_pend[6]), .o_pend7(o_pend[7]),
        .o_age0(o_age[0]), .o_age1(o_age[1]), .o_age2(o_age[2]),
        .o_age3(o_age[3]), .o_age4(o_age[4]), .o_age5(o_age[5]),
        .o_age6(o_age[6]), .o_age7(o_age[7])
    );

    wire done = (o_cyc == 32'd100000);
    assign leds = {heartbeat[24], 1'b0, (o_err != 32'd0), done};

    // ---- BSCANE2 USER1 register bridge (s0/s13 lineage, 42-bit DR) ----
    wire capture, drck, sel, shift, tdi, update, tdo;
    BSCANE2 #(.JTAG_CHAIN(1)) u_bscan (
        .CAPTURE(capture), .DRCK(drck), .RESET(), .RUNTEST(),
        .SEL(sel), .SHIFT(shift), .TCK(), .TDI(tdi), .TMS(),
        .UPDATE(update), .TDO(tdo)
    );

    // heartbeat CDC into DRCK domain (liveness read; tearing acceptable)
    reg [31:0] hb_meta = 32'd0, hb_sync = 32'd0;
    always @(posedge drck) begin hb_meta <= heartbeat; hb_sync <= hb_meta; end

    reg [31:0] scratch = 32'd0;
    reg [31:0] rd_reg  = 32'd0;
    reg [40:0] dr      = 41'd0;
    always @(posedge drck) begin
        if (sel) begin
            if (capture)    dr <= {9'b0, rd_reg};
            else if (shift) dr <= {tdi, dr[40:1]};
        end
    end
    assign tdo = dr[0];

    wire        w_wr  = dr[40];
    wire [6:0]  w_idx = dr[38:32];
    wire [31:0] w_dat = dr[31:0];

    always @(posedge update) begin
        if (sel) begin
            if (w_wr) case (w_idx)
                7'd1: scratch  <= w_dat;
                7'd3: rst_hold <= w_dat[0];
                default: ;
            endcase
            case (w_idx)
                7'd0:  rd_reg <= 32'h5330_100E;
                7'd1:  rd_reg <= scratch;
                7'd2:  rd_reg <= hb_sync;
                7'd3:  rd_reg <= {31'd0, rst_hold};
                7'd81: rd_reg <= o_cyc;
                7'd82: rd_reg <= o_injected;
                7'd83: rd_reg <= o_serviced;
                7'd84: rd_reg <= o_err;
                7'd85: rd_reg <= o_maxout;
                7'd86: rd_reg <= o_dma_sub;
                7'd87: rd_reg <= o_dma_comp;
                7'd88: rd_reg <= o_tmr_exp;
                7'd90: rd_reg <= {16'd0, o_lfsr};
                7'd91: rd_reg <= {29'd0, o_ptr};
                7'd92: rd_reg <= {16'd0, o_tmr};
                7'd93: rd_reg <= {27'd0, o_dma_cd, o_dma_busy};
                7'd94: rd_reg <= {24'd0, o_pend};
                7'd100: rd_reg <= {21'd0, o_age[0]};
                7'd101: rd_reg <= {21'd0, o_age[1]};
                7'd102: rd_reg <= {21'd0, o_age[2]};
                7'd103: rd_reg <= {21'd0, o_age[3]};
                7'd104: rd_reg <= {21'd0, o_age[4]};
                7'd105: rd_reg <= {21'd0, o_age[5]};
                7'd106: rd_reg <= {21'd0, o_age[6]};
                7'd107: rd_reg <= {21'd0, o_age[7]};
                default: rd_reg <= 32'hDEAD_0000;
            endcase
        end
    end
endmodule

`default_nettype wire
