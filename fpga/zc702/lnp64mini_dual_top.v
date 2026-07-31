// lnp64mini_dual_top.v -- ZC702 board top for the ALL-LEAN dual-core
// lnp64mini_dual (core0 || core1 || HpArbiter || HP master || GP master,
// ALL inside the composed Lean design).
//
// Derived from lnp64mini_soc_top.v; the wrapper still holds ONLY the
// irreducibly-non-single-clock plumbing (clock buffers + /8 divider, POR
// ramps, BSCANE2 USER1 + 41-bit DR + UPDATE/DRCK CDC, the read register
// map, and the PS7). Everything synchronous to sysclk is Loom-emitted.
//
// ---- Dual BSCAN surface (DUAL_SPEC "CORE1_HOLD + BSCAN") ----
// The mini DR is {wr, idx[6:0], data[31:0]} in dr[40:32]/dr[31:0], leaving
// dr[39] unused. dr[39] is now the CORE-SELECT region bit:
//     dr[39]=0 -> core 0    dr[39]=1 -> core 1
// which is exactly what jtag_lib.tcl's `wr [expr 0x80|idx]` produces (it
// writes an 8-bit index into dr[39:32]), so the library is unchanged. The
// bit is latched at UPDATE alongside idx, for BOTH the write path (which
// cmd port the pulse goes to) and the read path (which core's readback
// register the case statement returns).
//
// Wrapper-level command:  idx 56, data[0] = CORE1_HOLD (reset value 1, so
// core 1 comes up held). Read idx 56 returns {CORE1_HOLD, core-1 status}.
// idx 56 is a wrapper register and is accepted regardless of dr[39].
//
// ID reads 0x53301018 ("Loom dual edition") so a host can tell the dual
// bitstream from the single-core one (0x53301017).
`timescale 1ns/1ps
`default_nettype none

module lnp64mini_dual_top (
    input  wire       sys_clk_p,
    input  wire       sys_clk_n,
    output wire [3:0] leds
);
    localparam [31:0] ID_MAGIC = 32'h5330_1018;

    wire clk_ibuf, clk_bufg, sysclk;
    IBUFDS u_ibufds (.I(sys_clk_p), .IB(sys_clk_n), .O(clk_ibuf));
    BUFG   u_bufg   (.I(clk_ibuf), .O(clk_bufg));
    // 200 MHz / 8 = 25 MHz core clock (see the Fmax datapoint in README).
    reg [3:0] divc = 4'b0000;
    always @(posedge clk_bufg) divc <= divc + 4'b0001;
    BUFG   u_bufgd  (.I(divc[2]), .O(sysclk));

    reg [7:0] arstc = 0; always @(posedge sysclk) if (~&arstc) arstc <= arstc + 1;
    wire hp_aresetn = &arstc;
    wire gp_aresetn = &arstc;
    reg [7:0] rstc = 0; always @(posedge sysclk) if (~&rstc) rstc <= rstc + 1;
    wire local_rstn = &rstc;
    wire rst = ~local_rstn;

    reg [31:0] heartbeat = 0; always @(posedge sysclk) heartbeat <= heartbeat + 1;

    // ---- BSCANE2 USER1 + 41-bit DR (jtag_lib.tcl protocol) ----
    wire capture, drck, sel, shift, tdi, update, tdo;
    BSCANE2 #(.JTAG_CHAIN(1)) u_bscan (
        .CAPTURE(capture), .DRCK(drck), .RESET(), .RUNTEST(),
        .SEL(sel), .SHIFT(shift), .TCK(), .TDI(tdi), .TMS(),
        .UPDATE(update), .TDO(tdo)
    );

    reg [31:0] rd_reg = 0;
    reg [40:0] dr = 41'd0;
    always @(posedge drck) begin
        if (sel) begin
            if (capture)    dr <= {9'b0, rd_reg};
            else if (shift) dr <= {tdi, dr[40:1]};
        end
    end
    assign tdo = dr[0];
    wire        w_wr   = dr[40];
    wire        w_core = dr[39];          // <-- core select (region bit)
    wire [6:0]  w_idx  = dr[38:32];
    wire [31:0] w_dat  = dr[31:0];

    reg        cmd_tog = 0;
    reg        lat_core = 0;
    reg [6:0]  lat_idx = 0;
    reg [31:0] lat_dat = 0;
    reg [31:0] scratch = 0;
    reg        core1_hold = 1'b1;         // CORE1_HOLD: held at power-on
    always @(posedge update) begin
        if (sel && w_wr) begin
            if (w_idx == 7'd1)       scratch    <= w_dat;
            else if (w_idx == 7'd56) core1_hold <= w_dat[0];   // wrapper reg
            else begin
                lat_core <= w_core; lat_idx <= w_idx; lat_dat <= w_dat;
                cmd_tog <= ~cmd_tog;
            end
        end
    end
    reg t0=0, t1=0, t2=0;
    always @(posedge sysclk) begin t0 <= cmd_tog; t1 <= t0; t2 <= t1; end
    wire cmd_pulse  = t1 ^ t2;
    // one pulse, routed to the selected core's cmd port
    wire c0_cmd_valid = cmd_pulse & ~lat_core;
    wire c1_cmd_valid = cmd_pulse &  lat_core;

    // CORE1_HOLD into the sysclk domain (2FF; it is a level, not a pulse)
    reg h0=1, h1=1; always @(posedge sysclk) begin h0 <= core1_hold; h1 <= h0; end

    // ---- the all-Lean dual soc ----
    wire        o_c0_running, o_c0_halted, o_c0_trap_active, o_c0_bus_req;
    wire        o_c1_running, o_c1_halted, o_c1_trap_active, o_c1_bus_req;
    wire [4:0]  o_c0_st, o_c1_st;
    wire [63:0] o_c0_pc, o_c0_ir, o_c0_ddr_rd_l, o_c0_reg_rd, o_c0_dmem_rd;
    wire [63:0] o_c1_pc, o_c1_ir, o_c1_ddr_rd_l, o_c1_reg_rd, o_c1_dmem_rd;
    wire [31:0] o_c0_retire, o_c1_retire;
    wire [7:0]  o_c0_trapped_op, o_c0_uart_byte, o_c1_trapped_op, o_c1_uart_byte;
    wire [8:0]  o_c0_uart_wptr, o_c1_uart_wptr;
    wire        o_hp_busy;
    wire [2:0]  o_gpm_dbg_state; wire o_gpm_busy, o_gpm_done, o_gpm_err;
    // HP AXI master ports (dual -> PS7)
    wire [31:0] hp_awaddr, hp_araddr; wire [3:0] hp_awlen, hp_arlen;
    wire [2:0] hp_awsize, hp_arsize; wire [1:0] hp_awburst, hp_arburst;
    wire [5:0] hp_awid, hp_arid, hp_wid; wire [63:0] hp_wdata; wire [7:0] hp_wstrb;
    wire hp_awvalid, hp_wvalid, hp_wlast, hp_bready, hp_arvalid, hp_rready;
    wire hp_awready, hp_wready, hp_bvalid, hp_arready, hp_rvalid;
    wire [1:0] hp_bresp, hp_rresp; wire [63:0] hp_rdata;
    // GP AXI master ports (dual -> PS7)
    wire [31:0] gpm_awaddr, gpm_araddr, gpm_wdata; wire [3:0] gpm_awlen, gpm_arlen, gpm_wstrb;
    wire [2:0] gpm_awsize, gpm_arsize; wire [1:0] gpm_awburst, gpm_arburst;
    wire [5:0] gpm_awid, gpm_arid, gpm_wid;
    wire gpm_awvalid, gpm_wvalid, gpm_wlast, gpm_bready, gpm_arvalid, gpm_rready;
    wire gpm_awready, gpm_wready, gpm_bvalid, gpm_arready, gpm_rvalid;
    wire [1:0] gpm_bresp, gpm_rresp; wire [31:0] gpm_rdata;

    lnp64mini_dual u_dual (
        .clk(sysclk), .rst(rst),
        .c0_cmd_valid(c0_cmd_valid), .c0_cmd_idx(lat_idx), .c0_cmd_data(lat_dat),
        .c1_cmd_valid(c1_cmd_valid), .c1_cmd_idx(lat_idx), .c1_cmd_data(lat_dat),
        .c1_hold(h1),
        .hp_m_awready(hp_awready), .hp_m_wready(hp_wready),
        .hp_m_bvalid(hp_bvalid), .hp_m_bresp(hp_bresp),
        .hp_m_arready(hp_arready), .hp_m_rvalid(hp_rvalid),
        .hp_m_rdata_in(hp_rdata), .hp_m_rresp(hp_rresp),
        .gpm_m_awready(gpm_awready), .gpm_m_wready(gpm_wready),
        .gpm_m_bvalid(gpm_bvalid), .gpm_m_bresp(gpm_bresp),
        .gpm_m_arready(gpm_arready), .gpm_m_rvalid(gpm_rvalid),
        .gpm_m_rdata_in(gpm_rdata), .gpm_m_rresp(gpm_rresp),
        // core 0 observability
        .o_c0_running(o_c0_running), .o_c0_halted(o_c0_halted), .o_c0_st(o_c0_st),
        .o_c0_pc(o_c0_pc), .o_c0_retire(o_c0_retire), .o_c0_ir(o_c0_ir),
        .o_c0_trap_active(o_c0_trap_active), .o_c0_trapped_op(o_c0_trapped_op),
        .o_c0_bus_req(o_c0_bus_req), .o_c0_ddr_rd_l(o_c0_ddr_rd_l),
        .o_c0_reg_rd(o_c0_reg_rd), .o_c0_dmem_rd(o_c0_dmem_rd),
        .o_c0_uart_wptr(o_c0_uart_wptr), .o_c0_uart_byte(o_c0_uart_byte),
        // core 1 observability
        .o_c1_running(o_c1_running), .o_c1_halted(o_c1_halted), .o_c1_st(o_c1_st),
        .o_c1_pc(o_c1_pc), .o_c1_retire(o_c1_retire), .o_c1_ir(o_c1_ir),
        .o_c1_trap_active(o_c1_trap_active), .o_c1_trapped_op(o_c1_trapped_op),
        .o_c1_bus_req(o_c1_bus_req), .o_c1_ddr_rd_l(o_c1_ddr_rd_l),
        .o_c1_reg_rd(o_c1_reg_rd), .o_c1_dmem_rd(o_c1_dmem_rd),
        .o_c1_uart_wptr(o_c1_uart_wptr), .o_c1_uart_byte(o_c1_uart_byte),
        .o_hp_busy(o_hp_busy),
        .o_gpm_dbg_state(o_gpm_dbg_state), .o_gpm_busy(o_gpm_busy),
        .o_gpm_done(o_gpm_done), .o_gpm_err(o_gpm_err),
        // HP AXI master out
        .o_hp_m_awaddr(hp_awaddr), .o_hp_m_awlen(hp_awlen), .o_hp_m_awsize(hp_awsize),
        .o_hp_m_awburst(hp_awburst), .o_hp_m_awid(hp_awid), .o_hp_m_awvalid(hp_awvalid),
        .o_hp_m_wdata(hp_wdata), .o_hp_m_wstrb(hp_wstrb), .o_hp_m_wvalid(hp_wvalid),
        .o_hp_m_wlast(hp_wlast), .o_hp_m_wid(hp_wid), .o_hp_m_bready(hp_bready),
        .o_hp_m_araddr(hp_araddr), .o_hp_m_arlen(hp_arlen), .o_hp_m_arsize(hp_arsize),
        .o_hp_m_arburst(hp_arburst), .o_hp_m_arid(hp_arid), .o_hp_m_arvalid(hp_arvalid),
        .o_hp_m_rready(hp_rready),
        // GP AXI master out
        .o_gpm_m_awaddr(gpm_awaddr), .o_gpm_m_awlen(gpm_awlen), .o_gpm_m_awsize(gpm_awsize),
        .o_gpm_m_awburst(gpm_awburst), .o_gpm_m_awid(gpm_awid), .o_gpm_m_awvalid(gpm_awvalid),
        .o_gpm_m_wdata(gpm_wdata), .o_gpm_m_wstrb(gpm_wstrb), .o_gpm_m_wvalid(gpm_wvalid),
        .o_gpm_m_wlast(gpm_wlast), .o_gpm_m_wid(gpm_wid), .o_gpm_m_bready(gpm_bready),
        .o_gpm_m_araddr(gpm_araddr), .o_gpm_m_arlen(gpm_arlen), .o_gpm_m_arsize(gpm_arsize),
        .o_gpm_m_arburst(gpm_arburst), .o_gpm_m_arid(gpm_arid), .o_gpm_m_arvalid(gpm_arvalid),
        .o_gpm_m_rready(gpm_rready)
    );

    // bus_granted for the status read: JTAG owns the DDR window when BOTH
    // cores yield it (the single-core formula, generalized over the pair).
    wire c0_owns = o_c0_running && (o_c0_st != 5'd6) && (o_c0_st != 5'd10) && (o_c0_st != 5'd17);
    wire c1_owns = o_c1_running && (o_c1_st != 5'd6) && (o_c1_st != 5'd10) && (o_c1_st != 5'd17);
    wire bus_granted = ~c0_owns && ~c1_owns;

    // ---- PS-alive probe (FCLK0-domain counter, BSCAN reg 27) ----
    wire [3:0] fclk; wire fclk0_bufg;
    BUFG u_bufgf (.I(fclk[0]), .O(fclk0_bufg));
    reg [31:0] fclk_cnt_r = 0; always @(posedge fclk0_bufg) fclk_cnt_r <= fclk_cnt_r + 1;

    // ---- read-side register map (mini3-compatible), DRCK-domain 2FF ----
    // Every per-core register is sampled for BOTH cores; the case statement
    // below picks with the latched region bit w_core.
    reg [31:0] hb0=0,hb1=0;   always @(posedge drck) begin hb0<=heartbeat; hb1<=hb0; end
    reg [31:0] fc0=0,fc1=0;   always @(posedge drck) begin fc0<=fclk_cnt_r; fc1<=fc0; end

    reg [31:0] rt0a=0,rt1a=0; always @(posedge drck) begin rt0a<=o_c0_retire; rt1a<=rt0a; end
    reg [31:0] rt0b=0,rt1b=0; always @(posedge drck) begin rt0b<=o_c1_retire; rt1b<=rt0b; end
    reg [31:0] pc0a=0,pc1a=0; always @(posedge drck) begin pc0a<=o_c0_pc[31:0]; pc1a<=pc0a; end
    reg [31:0] pc0b=0,pc1b=0; always @(posedge drck) begin pc0b<=o_c1_pc[31:0]; pc1b<=pc0b; end
    reg [4:0]  ss0a=0,ss1a=0; always @(posedge drck) begin ss0a<={o_c0_bus_req,bus_granted,o_hp_busy,o_c0_halted,o_c0_running}; ss1a<=ss0a; end
    reg [4:0]  ss0b=0,ss1b=0; always @(posedge drck) begin ss0b<={o_c1_bus_req,bus_granted,o_hp_busy,o_c1_halted,o_c1_running}; ss1b<=ss0b; end
    reg [63:0] rv0a=0,rv1a=0; always @(posedge drck) begin rv0a<=o_c0_reg_rd; rv1a<=rv0a; end
    reg [63:0] rv0b=0,rv1b=0; always @(posedge drck) begin rv0b<=o_c1_reg_rd; rv1b<=rv0b; end
    reg [63:0] dv0a=0,dv1a=0; always @(posedge drck) begin dv0a<=o_c0_dmem_rd; dv1a<=dv0a; end
    reg [63:0] dv0b=0,dv1b=0; always @(posedge drck) begin dv0b<=o_c1_dmem_rd; dv1b<=dv0b; end
    reg [63:0] dd0a=0,dd1a=0; always @(posedge drck) begin dd0a<=o_c0_ddr_rd_l; dd1a<=dd0a; end
    reg [63:0] dd0b=0,dd1b=0; always @(posedge drck) begin dd0b<=o_c1_ddr_rd_l; dd1b<=dd0b; end
    reg [8:0]  uw0a=0,uw1a=0; always @(posedge drck) begin uw0a<=o_c0_uart_wptr; uw1a<=uw0a; end
    reg [8:0]  uw0b=0,uw1b=0; always @(posedge drck) begin uw0b<=o_c1_uart_wptr; uw1b<=uw0b; end
    reg [7:0]  ub0a=0,ub1a=0; always @(posedge drck) begin ub0a<=o_c0_uart_byte; ub1a<=ub0a; end
    reg [7:0]  ub0b=0,ub1b=0; always @(posedge drck) begin ub0b<=o_c1_uart_byte; ub1b<=ub0b; end
    reg        tra0a=0,tra1a=0; always @(posedge drck) begin tra0a<=o_c0_trap_active; tra1a<=tra0a; end
    reg        tra0b=0,tra1b=0; always @(posedge drck) begin tra0b<=o_c1_trap_active; tra1b<=tra0b; end
    reg [7:0]  tro0a=0,tro1a=0; always @(posedge drck) begin tro0a<=o_c0_trapped_op; tro1a<=tro0a; end
    reg [7:0]  tro0b=0,tro1b=0; always @(posedge drck) begin tro0b<=o_c1_trapped_op; tro1b<=tro0b; end
    reg [63:0] ir0a=0,ir1a=0; always @(posedge drck) begin ir0a<=o_c0_ir; ir1a<=ir0a; end
    reg [63:0] ir0b=0,ir1b=0; always @(posedge drck) begin ir0b<=o_c1_ir; ir1b<=ir0b; end
    reg [4:0]  cs0a=0,cs1a=0; always @(posedge drck) begin cs0a<=o_c0_st; cs1a<=cs0a; end
    reg [4:0]  cs0b=0,cs1b=0; always @(posedge drck) begin cs0b<=o_c1_st; cs1b<=cs0b; end
    reg [2:0]  gps0=0,gps1=0; always @(posedge drck) begin gps0<=o_gpm_dbg_state; gps1<=gps0; end
    reg [2:0]  gpf0=0,gpf1=0; always @(posedge drck) begin gpf0<={o_gpm_err,o_gpm_done,o_gpm_busy}; gpf1<=gpf0; end

    // core-selected views (w_core is stable at UPDATE, like w_idx)
    wire [31:0] s_rt  = w_core ? rt1b     : rt1a;
    wire [31:0] s_pc  = w_core ? pc1b     : pc1a;
    wire [4:0]  s_ss  = w_core ? ss1b     : ss1a;
    wire [63:0] s_rv  = w_core ? rv1b     : rv1a;
    wire [63:0] s_dv  = w_core ? dv1b     : dv1a;
    wire [63:0] s_dd  = w_core ? dd1b     : dd1a;
    wire [8:0]  s_uw  = w_core ? uw1b     : uw1a;
    wire [7:0]  s_ub  = w_core ? ub1b     : ub1a;
    wire        s_tra = w_core ? tra1b    : tra1a;
    wire [7:0]  s_tro = w_core ? tro1b    : tro1a;
    wire [63:0] s_ir  = w_core ? ir1b     : ir1a;
    wire [4:0]  s_cst = w_core ? cs1b     : cs1a;

    always @(posedge update) begin
        if (sel) begin
            case (w_idx)
                7'd0:  rd_reg <= ID_MAGIC;
                7'd1:  rd_reg <= scratch;
                7'd2:  rd_reg <= hb1;
                7'd20: rd_reg <= {27'd0, s_ss};
                7'd21: rd_reg <= s_rt;
                7'd22: rd_reg <= s_pc;
                7'd23: rd_reg <= s_rv[31:0];
                7'd24: rd_reg <= s_rv[63:32];
                7'd25: rd_reg <= s_dv[31:0];
                7'd26: rd_reg <= s_dv[63:32];
                7'd27: rd_reg <= fc1;
                7'd28: rd_reg <= {16'd0, gpf1, s_cst, gps1};
                7'd30: rd_reg <= {23'd0, s_uw};
                7'd31: rd_reg <= {24'd0, s_ub};
                7'd40: rd_reg <= {16'd0, s_tro, 7'd0, s_tra};
                7'd41: rd_reg <= s_ir[31:0];
                7'd42: rd_reg <= s_ir[63:32];
                7'd45: rd_reg <= s_dd[31:0];
                7'd46: rd_reg <= s_dd[63:32];
                // CORE1_HOLD + core-1 status (always core 1, region-independent)
                7'd56: rd_reg <= {26'd0, core1_hold, ss1b};
                default: rd_reg <= 32'hDEAD_0000;
            endcase
        end
    end

    assign leds = {heartbeat[24], o_c1_running, o_c0_halted, o_c0_running};

    // ---- PS7 (S_AXI_HP1 + S_AXI_GP0, as the single-core soc) ----
    PS7 u_ps7 (
        .FCLKCLK(fclk),
        .SAXIHP1ACLK(sysclk), .SAXIHP1ARESETN(hp_aresetn),
        .SAXIHP1AWADDR(hp_awaddr), .SAXIHP1AWLEN(hp_awlen), .SAXIHP1AWSIZE(hp_awsize),
        .SAXIHP1AWBURST(hp_awburst), .SAXIHP1AWID(hp_awid), .SAXIHP1AWVALID(hp_awvalid),
        .SAXIHP1AWREADY(hp_awready), .SAXIHP1AWLOCK(2'b0), .SAXIHP1AWCACHE(4'b0),
        .SAXIHP1AWPROT(3'b0), .SAXIHP1AWQOS(4'b0),
        .SAXIHP1WDATA(hp_wdata), .SAXIHP1WSTRB(hp_wstrb), .SAXIHP1WLAST(hp_wlast),
        .SAXIHP1WID(hp_wid), .SAXIHP1WVALID(hp_wvalid), .SAXIHP1WREADY(hp_wready),
        .SAXIHP1BRESP(hp_bresp), .SAXIHP1BVALID(hp_bvalid), .SAXIHP1BREADY(hp_bready),
        .SAXIHP1ARADDR(hp_araddr), .SAXIHP1ARLEN(hp_arlen), .SAXIHP1ARSIZE(hp_arsize),
        .SAXIHP1ARBURST(hp_arburst), .SAXIHP1ARID(hp_arid), .SAXIHP1ARVALID(hp_arvalid),
        .SAXIHP1ARREADY(hp_arready), .SAXIHP1ARLOCK(2'b0), .SAXIHP1ARCACHE(4'b0),
        .SAXIHP1ARPROT(3'b0), .SAXIHP1ARQOS(4'b0),
        .SAXIHP1RDATA(hp_rdata), .SAXIHP1RRESP(hp_rresp), .SAXIHP1RVALID(hp_rvalid),
        .SAXIHP1RREADY(hp_rready),
        .SAXIHP1RDISSUECAP1EN(1'b0), .SAXIHP1WRISSUECAP1EN(1'b0),
        .SAXIGP0ACLK(sysclk), .SAXIGP0ARESETN(gp_aresetn),
        .SAXIGP0AWADDR(gpm_awaddr), .SAXIGP0AWLEN(gpm_awlen), .SAXIGP0AWSIZE(gpm_awsize),
        .SAXIGP0AWBURST(gpm_awburst), .SAXIGP0AWID(gpm_awid), .SAXIGP0AWVALID(gpm_awvalid),
        .SAXIGP0AWREADY(gpm_awready), .SAXIGP0AWLOCK(2'b0), .SAXIGP0AWCACHE(4'b0),
        .SAXIGP0AWPROT(3'b0), .SAXIGP0AWQOS(4'b0),
        .SAXIGP0WDATA(gpm_wdata), .SAXIGP0WSTRB(gpm_wstrb), .SAXIGP0WLAST(gpm_wlast),
        .SAXIGP0WID(gpm_wid), .SAXIGP0WVALID(gpm_wvalid), .SAXIGP0WREADY(gpm_wready),
        .SAXIGP0BRESP(gpm_bresp), .SAXIGP0BVALID(gpm_bvalid), .SAXIGP0BREADY(gpm_bready),
        .SAXIGP0ARADDR(gpm_araddr), .SAXIGP0ARLEN(gpm_arlen), .SAXIGP0ARSIZE(gpm_arsize),
        .SAXIGP0ARBURST(gpm_arburst), .SAXIGP0ARID(gpm_arid), .SAXIGP0ARVALID(gpm_arvalid),
        .SAXIGP0ARREADY(gpm_arready), .SAXIGP0ARLOCK(2'b0), .SAXIGP0ARCACHE(4'b0),
        .SAXIGP0ARPROT(3'b0), .SAXIGP0ARQOS(4'b0),
        .SAXIGP0RDATA(gpm_rdata), .SAXIGP0RRESP(gpm_rresp), .SAXIGP0RVALID(gpm_rvalid),
        .SAXIGP0RREADY(gpm_rready)
    );
endmodule

`default_nettype wire
