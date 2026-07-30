// lnp64mini_soc_top.v -- ZC702 board top for the ALL-LEAN lnp64mini_soc.
//
// Thin wrapper over the Loom-emitted rtl/lnp64mini_soc.v (core + HP master +
// GP master + the HP ownership mux, ALL now inside the composed Lean design).
// The wrapper keeps ONLY the irreducibly-non-single-clock plumbing:
//   * clock buffers + /8 (200 -> 25 MHz) divider + POR/reset ramps,
//   * BSCANE2 USER1 + 41-bit DR shift + UPDATE/DRCK clock-domain crossing,
//   * the mini3-compatible BSCAN read register map (DRCK-domain 2FF-sampled
//     from the soc's o_* observability ports -- port names adjusted),
//   * PS7, with AXI wires running STRAIGHT from soc master outputs to PS7 and
//     PS7 slave responses straight back into soc inputs.
// NO axi_hp_master / axi_gp_master modules and NO HP mux here -- both are
// absorbed into the soc. ID reads 0x53301017 ("Loom edition"), so jtag_lib.tcl
// and the whole §61 boot flow drive the composed core unchanged.
`timescale 1ns/1ps
`default_nettype none

module lnp64mini_soc_top (
    input  wire       sys_clk_p,
    input  wire       sys_clk_n,
    output wire [3:0] leds
);
    localparam [31:0] ID_MAGIC = 32'h5330_1017;

    wire clk_ibuf, clk_bufg, sysclk;
    IBUFDS u_ibufds (.I(sys_clk_p), .IB(sys_clk_n), .O(clk_ibuf));
    BUFG   u_bufg   (.I(clk_ibuf), .O(clk_bufg));
    // 200 MHz / 8 = 25 MHz core clock.  divc[2] toggles every 4 clk_bufg
    // edges -> a 25 MHz square wave.  (Was divc[3] = 200/16 = 12.5 MHz, set
    // when the emitted soc routed at 13.1 MHz; after the balanced-tree
    // restructuring of Machines/Lnp64mini/Core.lean nextpnr-xilinx reports
    // 31.69 MHz for sysclk, so 25 MHz has ~27% margin.)
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
    wire        w_wr  = dr[40];
    wire [6:0]  w_idx = dr[38:32];
    wire [31:0] w_dat = dr[31:0];

    reg        cmd_tog = 0;
    reg [6:0]  lat_idx = 0;
    reg [31:0] lat_dat = 0;
    reg [31:0] scratch = 0;
    always @(posedge update) begin
        if (sel && w_wr) begin
            if (w_idx == 7'd1) scratch <= w_dat;
            else begin lat_idx <= w_idx; lat_dat <= w_dat; cmd_tog <= ~cmd_tog; end
        end
    end
    reg t0=0, t1=0, t2=0;
    always @(posedge sysclk) begin t0 <= cmd_tog; t1 <= t0; t2 <= t1; end
    wire cmd_valid = t1 ^ t2;

    // ---- the all-Lean soc ----
    // observability
    wire        o_running, o_halted, o_trap_active, o_bus_req;
    wire [4:0]  o_st;
    wire [63:0] o_pc, o_ir, o_ddr_rd_l, o_reg_rd, o_dmem_rd;
    wire [31:0] o_retire;
    wire [7:0]  o_trapped_op, o_uart_byte;
    wire [8:0]  o_uart_wptr;
    // HP master status (for the status read map)
    wire        o_hp_busy;
    // GP master debug
    wire [2:0]  o_gpm_dbg_state; wire o_gpm_busy, o_gpm_done, o_gpm_err;
    // HP AXI master ports (soc -> PS7)
    wire [31:0] hp_awaddr, hp_araddr; wire [3:0] hp_awlen, hp_arlen;
    wire [2:0] hp_awsize, hp_arsize; wire [1:0] hp_awburst, hp_arburst;
    wire [5:0] hp_awid, hp_arid, hp_wid; wire [63:0] hp_wdata; wire [7:0] hp_wstrb;
    wire hp_awvalid, hp_wvalid, hp_wlast, hp_bready, hp_arvalid, hp_rready;
    // HP AXI responses (PS7 -> soc)
    wire hp_awready, hp_wready, hp_bvalid, hp_arready, hp_rvalid;
    wire [1:0] hp_bresp, hp_rresp; wire [63:0] hp_rdata;
    // GP AXI master ports (soc -> PS7)
    wire [31:0] gpm_awaddr, gpm_araddr, gpm_wdata; wire [3:0] gpm_awlen, gpm_arlen, gpm_wstrb;
    wire [2:0] gpm_awsize, gpm_arsize; wire [1:0] gpm_awburst, gpm_arburst;
    wire [5:0] gpm_awid, gpm_arid, gpm_wid;
    wire gpm_awvalid, gpm_wvalid, gpm_wlast, gpm_bready, gpm_arvalid, gpm_rready;
    // GP AXI responses (PS7 -> soc)
    wire gpm_awready, gpm_wready, gpm_bvalid, gpm_arready, gpm_rvalid;
    wire [1:0] gpm_bresp, gpm_rresp; wire [31:0] gpm_rdata;

    lnp64mini_soc u_soc (
        .clk(sysclk), .rst(rst),
        .cmd_valid(cmd_valid), .cmd_idx(lat_idx), .cmd_data(lat_dat),
        // HP responses in
        .hp_m_awready(hp_awready), .hp_m_wready(hp_wready),
        .hp_m_bvalid(hp_bvalid), .hp_m_bresp(hp_bresp),
        .hp_m_arready(hp_arready), .hp_m_rvalid(hp_rvalid),
        .hp_m_rdata_in(hp_rdata), .hp_m_rresp(hp_rresp),
        // GP responses in
        .gpm_m_awready(gpm_awready), .gpm_m_wready(gpm_wready),
        .gpm_m_bvalid(gpm_bvalid), .gpm_m_bresp(gpm_bresp),
        .gpm_m_arready(gpm_arready), .gpm_m_rvalid(gpm_rvalid),
        .gpm_m_rdata_in(gpm_rdata), .gpm_m_rresp(gpm_rresp),
        // observability
        .o_running(o_running), .o_halted(o_halted), .o_st(o_st),
        .o_pc(o_pc), .o_retire(o_retire), .o_ir(o_ir),
        .o_trap_active(o_trap_active), .o_trapped_op(o_trapped_op),
        .o_bus_req(o_bus_req), .o_ddr_rd_l(o_ddr_rd_l),
        .o_reg_rd(o_reg_rd), .o_dmem_rd(o_dmem_rd),
        .o_uart_wptr(o_uart_wptr), .o_uart_byte(o_uart_byte),
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

    // bus_granted for the status read (same formula the soc uses internally):
    // hp_core_owns = running && st∉{6,10,17}.
    wire hp_core_owns = o_running && (o_st != 5'd6) && (o_st != 5'd10) && (o_st != 5'd17);
    wire bus_granted  = ~hp_core_owns;

    // ---- PS-alive probe (FCLK0-domain counter, BSCAN reg 27) ----
    wire [3:0] fclk; wire fclk0_bufg;
    BUFG u_bufgf (.I(fclk[0]), .O(fclk0_bufg));
    reg [31:0] fclk_cnt_r = 0; always @(posedge fclk0_bufg) fclk_cnt_r <= fclk_cnt_r + 1;

    // ---- read-side register map (mini3-compatible), DRCK-domain 2FF ----
    reg [31:0] hb0=0,hb1=0;   always @(posedge drck) begin hb0<=heartbeat; hb1<=hb0; end
    reg [31:0] rt0=0,rt1=0;   always @(posedge drck) begin rt0<=o_retire; rt1<=rt0; end
    reg [31:0] pc0=0,pc1=0;   always @(posedge drck) begin pc0<=o_pc[31:0]; pc1<=pc0; end
    reg [4:0]  ss0=0,ss1=0;   always @(posedge drck) begin ss0<={o_bus_req,bus_granted,o_hp_busy,o_halted,o_running}; ss1<=ss0; end
    reg [63:0] rv0=0,rv1=0;   always @(posedge drck) begin rv0<=o_reg_rd; rv1<=rv0; end
    reg [63:0] dv0=0,dv1=0;   always @(posedge drck) begin dv0<=o_dmem_rd; dv1<=dv0; end
    reg [63:0] dd0=0,dd1=0;   always @(posedge drck) begin dd0<=o_ddr_rd_l; dd1<=dd0; end
    reg [8:0]  uw0=0,uw1=0;   always @(posedge drck) begin uw0<=o_uart_wptr; uw1<=uw0; end
    reg [7:0]  ub0=0,ub1=0;   always @(posedge drck) begin ub0<=o_uart_byte; ub1<=ub0; end
    reg        tra0=0,tra1=0; always @(posedge drck) begin tra0<=o_trap_active; tra1<=tra0; end
    reg [7:0]  tro0=0,tro1=0; always @(posedge drck) begin tro0<=o_trapped_op; tro1<=tro0; end
    reg [63:0] ir0=0,ir1=0;   always @(posedge drck) begin ir0<=o_ir; ir1<=ir0; end
    reg [31:0] fc0=0,fc1=0;   always @(posedge drck) begin fc0<=fclk_cnt_r; fc1<=fc0; end
    reg [4:0]  cst0=0,cst1=0; always @(posedge drck) begin cst0<=o_st; cst1<=cst0; end
    reg [2:0]  gps0=0,gps1=0; always @(posedge drck) begin gps0<=o_gpm_dbg_state; gps1<=gps0; end
    reg [2:0]  gpf0=0,gpf1=0; always @(posedge drck) begin gpf0<={o_gpm_err,o_gpm_done,o_gpm_busy}; gpf1<=gpf0; end

    always @(posedge update) begin
        if (sel) begin
            case (w_idx)
                7'd0:  rd_reg <= ID_MAGIC;
                7'd1:  rd_reg <= scratch;
                7'd2:  rd_reg <= hb1;
                7'd20: rd_reg <= {27'd0, ss1};
                7'd21: rd_reg <= rt1;
                7'd22: rd_reg <= pc1;
                7'd23: rd_reg <= rv1[31:0];
                7'd24: rd_reg <= rv1[63:32];
                7'd25: rd_reg <= dv1[31:0];
                7'd26: rd_reg <= dv1[63:32];
                7'd27: rd_reg <= fc1;
                7'd28: rd_reg <= {16'd0, gpf1, cst1, gps1};
                7'd30: rd_reg <= {23'd0, uw1};
                7'd31: rd_reg <= {24'd0, ub1};
                7'd40: rd_reg <= {16'd0, tro1, 7'd0, tra1};
                7'd41: rd_reg <= ir1[31:0];
                7'd42: rd_reg <= ir1[63:32];
                7'd45: rd_reg <= dd1[31:0];
                7'd46: rd_reg <= dd1[63:32];
                default: rd_reg <= 32'hDEAD_0000;
            endcase
        end
    end

    assign leds = {heartbeat[24], o_trap_active, o_halted, o_running};

    // ---- PS7 (S_AXI_HP1 + S_AXI_GP0, as mini3) ----
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
