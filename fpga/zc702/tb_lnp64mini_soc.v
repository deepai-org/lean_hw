// tb_lnp64mini_soc.v -- full-system testbench for the ALL-LEAN composed
// lnp64mini_soc (core + hp master + gp master, Loom-emitted). Unlike
// tb_lnp64mini.v (which modelled the DDR behind the mini3 handshake), this
// tb drives the soc's *AXI3 master* ports with a behavioral single-beat
// AXI3 slave -- exactly the transaction the in-soc axi_hp_master issues
// (serialized AW->W->B for writes, AR->R for reads, LEN=0, 8-byte beats).
// The DDR is a word array behind that slave. GP AXI is tied to a trivial
// always-ready slave (this program touches no GP MMIO).
//
// Program image: $readmemh PROG_HEX into ddr at word (0x1000>>3). Dumps the
// architectural state in the SAME format as tb_lnp64mini.v for the emulator
// cross-check. The cycle count may differ (AXI-slave latency != behavioral
// DDR latency) but HALTED/pc/retire/r1..r9/dmem32 must match exactly.
`timescale 1ns/1ps
module tb;
  reg clk = 0, rst = 1;
  always #5 clk = ~clk;

  // ---- soc control inputs ----
  reg         cmd_valid = 0;
  reg  [6:0]  cmd_idx = 0;
  reg  [31:0] cmd_data = 0;

  // ---- soc observability ----
  wire        o_running, o_halted, o_trap_active;
  wire [4:0]  o_st;
  wire [63:0] o_pc;
  wire [31:0] o_retire;
  wire [7:0]  o_trapped_op;

  // ---- HP AXI master ports (soc -> slave) ----
  wire [31:0] o_hp_m_awaddr;  wire o_hp_m_awvalid;
  wire [63:0] o_hp_m_wdata;   wire o_hp_m_wvalid;
  wire        o_hp_m_bready;
  wire [31:0] o_hp_m_araddr;  wire o_hp_m_arvalid;
  wire        o_hp_m_rready;
  // ---- HP AXI responses (slave -> soc) ----
  reg         hp_m_awready = 0, hp_m_wready = 0, hp_m_bvalid = 0;
  reg  [1:0]  hp_m_bresp = 0;
  reg         hp_m_arready = 0, hp_m_rvalid = 0;
  reg  [63:0] hp_m_rdata_in = 0;
  reg  [1:0]  hp_m_rresp = 0;

  // ---- GP AXI responses: trivial always-ready slave (unused by this prog) ----
  reg         gpm_m_awready = 1, gpm_m_wready = 1, gpm_m_bvalid = 1;
  reg  [1:0]  gpm_m_bresp = 0;
  reg         gpm_m_arready = 1, gpm_m_rvalid = 1;
  reg  [31:0] gpm_m_rdata_in = 0;
  reg  [1:0]  gpm_m_rresp = 0;

  lnp64mini_soc dut (
    .clk(clk), .rst(rst),
    .cmd_valid(cmd_valid), .cmd_idx(cmd_idx), .cmd_data(cmd_data),
    // HP responses in
    .hp_m_awready(hp_m_awready), .hp_m_wready(hp_m_wready),
    .hp_m_bvalid(hp_m_bvalid), .hp_m_bresp(hp_m_bresp),
    .hp_m_arready(hp_m_arready), .hp_m_rvalid(hp_m_rvalid),
    .hp_m_rdata_in(hp_m_rdata_in), .hp_m_rresp(hp_m_rresp),
    // GP responses in
    .gpm_m_awready(gpm_m_awready), .gpm_m_wready(gpm_m_wready),
    .gpm_m_bvalid(gpm_m_bvalid), .gpm_m_bresp(gpm_m_bresp),
    .gpm_m_arready(gpm_m_arready), .gpm_m_rvalid(gpm_m_rvalid),
    .gpm_m_rdata_in(gpm_m_rdata_in), .gpm_m_rresp(gpm_m_rresp),
    // observability
    .o_running(o_running), .o_halted(o_halted), .o_st(o_st),
    .o_pc(o_pc), .o_retire(o_retire),
    .o_trap_active(o_trap_active), .o_trapped_op(o_trapped_op),
    // HP AXI master out
    .o_hp_m_awaddr(o_hp_m_awaddr), .o_hp_m_awvalid(o_hp_m_awvalid),
    .o_hp_m_wdata(o_hp_m_wdata), .o_hp_m_wvalid(o_hp_m_wvalid),
    .o_hp_m_bready(o_hp_m_bready),
    .o_hp_m_araddr(o_hp_m_araddr), .o_hp_m_arvalid(o_hp_m_arvalid),
    .o_hp_m_rready(o_hp_m_rready));

  // ---- behavioral single-beat AXI3 slave behind DDR ----
  // Window-relative: byte addr - DATA_BASE, word index >> 3.
  localparam [31:0] DATA_BASE = 32'h1000_0000;
  reg [63:0] ddr [0:65535];
  integer di;

  // Write channel FSM: accept AW, then W, then emit B.
  localparam WS_IDLE=0, WS_AW=1, WS_W=2, WS_B=3;
  reg [1:0]  wstate = WS_IDLE;
  reg [31:0] waddr = 0;
  // Read channel FSM: accept AR, then emit R.
  localparam RS_IDLE=0, RS_AR=1, RS_R=2;
  reg [1:0]  rstate = RS_IDLE;
  reg [31:0] raddr = 0;

  always @(posedge clk) begin
    // defaults (single-cycle handshakes)
    hp_m_awready <= 0; hp_m_wready <= 0; hp_m_bvalid <= 0;
    hp_m_arready <= 0; hp_m_rvalid <= 0;
    // --- write channel ---
    case (wstate)
      WS_IDLE: if (o_hp_m_awvalid) begin
                 waddr <= o_hp_m_awaddr; hp_m_awready <= 1; wstate <= WS_W;
               end
      WS_W:    if (o_hp_m_wvalid) begin
                 ddr[(waddr - DATA_BASE) >> 3] <= o_hp_m_wdata;
                 hp_m_wready <= 1; wstate <= WS_B;
               end
      WS_B:    begin
                 // hold BVALID until master's BREADY (master keeps it HIGH)
                 hp_m_bvalid <= 1; hp_m_bresp <= 2'b00;
                 if (o_hp_m_bready) wstate <= WS_IDLE;
               end
      default: wstate <= WS_IDLE;
    endcase
    // --- read channel ---
    case (rstate)
      RS_IDLE: if (o_hp_m_arvalid) begin
                 raddr <= o_hp_m_araddr; hp_m_arready <= 1; rstate <= RS_R;
               end
      RS_R:    begin
                 hp_m_rvalid <= 1; hp_m_rresp <= 2'b00;
                 hp_m_rdata_in <= ddr[(raddr - DATA_BASE) >> 3];
                 if (o_hp_m_rready) rstate <= RS_IDLE;
               end
      default: rstate <= RS_IDLE;
    endcase
  end

  task cmd(input [6:0] idx, input [31:0] data);
    begin
      @(negedge clk); cmd_idx = idx; cmd_data = data; cmd_valid = 1;
      @(negedge clk); cmd_valid = 0;
    end
  endtask

  integer i, cyc;
  initial begin
    for (di = 0; di < 65536; di = di + 1) ddr[di] = 64'd0;
    $readmemh(`PROG_HEX, ddr, 512);       // 512 = 0x1000>>3
    repeat (4) @(negedge clk); rst = 0;
    repeat (4) @(negedge clk);
    cmd(7'd13, 32'd1);                    // reset (starts the zeroing sweep)
    repeat (1200) @(negedge clk);         // 1024-cycle rf/dmem zero + margin
    cmd(7'd13, 32'd2);                    // start
    cyc = 0;
    while (!o_halted && !o_trap_active && cyc < 2000000) begin
      @(negedge clk); cyc = cyc + 1;
    end
    if (o_trap_active)
      $display("TRAP op=%02x pc=%0d", o_trapped_op, o_pc);
    $display("HALTED=%0d cycles=%0d pc=%0d retire=%0d",
             o_halted, cyc, o_pc, o_retire);
    for (i = 1; i <= 9; i = i + 1)
      $display("r%0d=%0d", i, dut.rf[i]);  // thread 0 regs (cur=0)
    $display("dmem32=%0d", dut.dmem[32]);  // zp word at 0x100
    $finish;
  end
endmodule
