// tb_lnp64mini.v -- full-system testbench for the Loom-emitted lnp64mini:
// behavioral HP-DDR model (2-cycle latency, mini3 handshake), BSCAN cmd
// driver (reset -> zeroing sweep -> start), runs a flat program image from
// DDR to EXIT, dumps the architectural state for the emulator cross-check.
// Program image: $readmemh PROG_HEX into ddr at word (0x1000>>3) (mini3
// v2 map: fetch/data at DDR[DATA_BASE + addr], pc starts at 0x1000).
`timescale 1ns/1ps
module tb;
  reg clk = 0, rst = 1;
  always #5 clk = ~clk;

  // D15 inputs
  reg         m_done = 0, m_busy = 0, gp_done = 0, gp_busy = 0;
  reg  [63:0] m_rdata = 0;
  reg  [31:0] gp_rdata = 0;
  reg         cmd_valid = 0;
  reg  [6:0]  cmd_idx = 0;
  reg  [31:0] cmd_data = 0;
  // observability
  wire        o_running, o_halted, o_trap_active;
  wire [4:0]  o_st;
  wire [63:0] o_pc;
  wire [31:0] o_retire;
  wire [7:0]  o_trapped_op;
  wire        o_core_rd, o_core_wr;
  wire [31:0] o_core_addr;
  wire [63:0] o_core_wdata;

  lnp64mini dut (
    .clk(clk), .rst(rst),
    .m_done(m_done), .m_rdata(m_rdata), .m_busy(m_busy),
    .gp_done(gp_done), .gp_rdata(gp_rdata), .gp_busy(gp_busy),
    .cmd_valid(cmd_valid), .cmd_idx(cmd_idx), .cmd_data(cmd_data),
    .o_running(o_running), .o_halted(o_halted), .o_st(o_st),
    .o_pc(o_pc), .o_retire(o_retire),
    .o_trap_active(o_trap_active), .o_trapped_op(o_trapped_op),
    .o_core_rd(o_core_rd), .o_core_wr(o_core_wr),
    .o_core_addr(o_core_addr), .o_core_wdata(o_core_wdata));

  // ---- behavioral DDR behind the HP handshake (window-relative) ----
  localparam [31:0] DATA_BASE = 32'h1000_0000;
  reg [63:0] ddr [0:65535];              // 512 KB window
  integer di;
  reg [31:0] lat_addr = 0; reg [63:0] lat_wd = 0;
  reg [2:0] hp_cnt = 0; reg hp_isrd = 0, hp_act = 0;
  always @(posedge clk) begin
    m_done <= 0;
    if (o_core_rd && !hp_act) begin
      hp_act <= 1; hp_isrd <= 1; lat_addr <= o_core_addr; hp_cnt <= 2;
    end else if (o_core_wr && !hp_act) begin
      hp_act <= 1; hp_isrd <= 0; lat_addr <= o_core_addr;
      lat_wd <= o_core_wdata; hp_cnt <= 2;
    end else if (hp_act) begin
      if (hp_cnt == 0) begin
        if (hp_isrd) m_rdata <= ddr[(lat_addr - DATA_BASE) >> 3];
        else ddr[(lat_addr - DATA_BASE) >> 3] <= lat_wd;
        m_done <= 1; hp_act <= 0;
      end else hp_cnt <= hp_cnt - 1;
    end
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
