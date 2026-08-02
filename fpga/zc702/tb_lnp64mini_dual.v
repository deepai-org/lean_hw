// tb_lnp64mini_dual.v -- full-system testbench for the ALL-LEAN two-core
// lnp64mini_dual (core0 || core1 || HpArbiter || HP master || GP master,
// Loom-emitted). One behavioral single-beat AXI3 slave sits behind the one
// HP master, exactly as in tb_lnp64mini_soc.v -- so the *only* path to
// shared memory is through the in-design arbiter, which is the point.
//
// Two independent cmd drivers (core-select is a tb argument, mirroring the
// wrapper's dr[39] region bit) and a CORE1_HOLD input.
//
// Program images:
//   PROG_HEX0 -> ddr word 0x1000>>3 = 512   (core 0 text, pc resets there)
//   PROG_HEX1 -> ddr word TEXT1>>3          (core 1 text; SET_PC via cmd 53)
// Defining ONLY_C0 starts BOTH cores but leaves CORE1_HOLD asserted, so
// core 1 must make zero progress -- the single-core regression on the dual
// fabric AND the `hold` test.
//
// Dumps both cores' architectural state plus the shared DDR words the three
// ladder-step-2 tests use.
`timescale 1ns/1ps
`ifndef TEXT1
  `define TEXT1 32'h4000
`endif
`ifndef MAXCYC
  `define MAXCYC 2000000
`endif
`ifndef NREGS
  `define NREGS 12
`endif
module tb;
  reg clk = 0, rst = 1;
  always #5 clk = ~clk;

  // ---- per-core cmd surfaces (the wrapper's dr[39] core-select, in the tb) ----
  reg         c0_cmd_valid = 0, c1_cmd_valid = 0;
  reg  [6:0]  c0_cmd_idx = 0,   c1_cmd_idx = 0;
  reg  [31:0] c0_cmd_data = 0,  c1_cmd_data = 0;
  reg         c1_hold = 1;                  // CORE1_HOLD: held out of reset

  // ---- observability ----
  wire        o_c0_running, o_c0_halted, o_c0_trap_active;
  wire        o_c1_running, o_c1_halted, o_c1_trap_active;
  wire [4:0]  o_c0_st, o_c1_st;
  wire [63:0] o_c0_pc, o_c1_pc;
  wire [31:0] o_c0_retire, o_c1_retire;
  wire [7:0]  o_c0_trapped_op, o_c1_trapped_op;
  wire        o_c0_wake_out, o_c1_wake_out;

  // ---- HP AXI master ports (dual -> slave) ----
  wire [31:0] o_hp_m_awaddr;  wire o_hp_m_awvalid;
  wire [63:0] o_hp_m_wdata;   wire o_hp_m_wvalid;
  wire        o_hp_m_bready;
  wire [31:0] o_hp_m_araddr;  wire o_hp_m_arvalid;
  wire        o_hp_m_rready;
  // ---- HP AXI responses (slave -> dual) ----
  reg         hp_m_awready = 0, hp_m_wready = 0, hp_m_bvalid = 0;
  reg  [1:0]  hp_m_bresp = 0;
  reg         hp_m_arready = 0, hp_m_rvalid = 0;
  reg  [63:0] hp_m_rdata_in = 0;
  reg  [1:0]  hp_m_rresp = 0;
  // ---- GP AXI responses: trivial always-ready slave (unused) ----
  reg         gpm_m_awready = 1, gpm_m_wready = 1, gpm_m_bvalid = 1;
  reg  [1:0]  gpm_m_bresp = 0;
  reg         gpm_m_arready = 1, gpm_m_rvalid = 1;
  reg  [31:0] gpm_m_rdata_in = 0;
  reg  [1:0]  gpm_m_rresp = 0;

  lnp64mini_dual dut (
    .clk(clk), .rst(rst),
    .c0_cmd_valid(c0_cmd_valid), .c0_cmd_idx(c0_cmd_idx), .c0_cmd_data(c0_cmd_data),
    .c1_cmd_valid(c1_cmd_valid), .c1_cmd_idx(c1_cmd_idx), .c1_cmd_data(c1_cmd_data),
    .c1_hold(c1_hold),
    .hp_m_awready(hp_m_awready), .hp_m_wready(hp_m_wready),
    .hp_m_bvalid(hp_m_bvalid), .hp_m_bresp(hp_m_bresp),
    .hp_m_arready(hp_m_arready), .hp_m_rvalid(hp_m_rvalid),
    .hp_m_rdata_in(hp_m_rdata_in), .hp_m_rresp(hp_m_rresp),
    .gpm_m_awready(gpm_m_awready), .gpm_m_wready(gpm_m_wready),
    .gpm_m_bvalid(gpm_m_bvalid), .gpm_m_bresp(gpm_m_bresp),
    .gpm_m_arready(gpm_m_arready), .gpm_m_rvalid(gpm_m_rvalid),
    .gpm_m_rdata_in(gpm_m_rdata_in), .gpm_m_rresp(gpm_m_rresp),
    .o_c0_running(o_c0_running), .o_c0_halted(o_c0_halted), .o_c0_st(o_c0_st),
    .o_c0_pc(o_c0_pc), .o_c0_retire(o_c0_retire),
    .o_c0_trap_active(o_c0_trap_active), .o_c0_trapped_op(o_c0_trapped_op),
    .o_c0_wake_out(o_c0_wake_out),
    .o_c1_running(o_c1_running), .o_c1_halted(o_c1_halted), .o_c1_st(o_c1_st),
    .o_c1_pc(o_c1_pc), .o_c1_retire(o_c1_retire),
    .o_c1_trap_active(o_c1_trap_active), .o_c1_trapped_op(o_c1_trapped_op),
    .o_c1_wake_out(o_c1_wake_out),
    .o_hp_m_awaddr(o_hp_m_awaddr), .o_hp_m_awvalid(o_hp_m_awvalid),
    .o_hp_m_wdata(o_hp_m_wdata), .o_hp_m_wvalid(o_hp_m_wvalid),
    .o_hp_m_bready(o_hp_m_bready),
    .o_hp_m_araddr(o_hp_m_araddr), .o_hp_m_arvalid(o_hp_m_arvalid),
    .o_hp_m_rready(o_hp_m_rready));

  // ---- behavioral single-beat AXI3 slave behind DDR ----
  localparam [31:0] DATA_BASE = 32'h1000_0000;
  reg [63:0] ddr [0:65535];
  integer di;

  localparam WS_IDLE=0, WS_W=2, WS_B=3;
  reg [1:0]  wstate = WS_IDLE;
  reg [31:0] waddr = 0;
  localparam RS_IDLE=0, RS_R=2;
  reg [1:0]  rstate = RS_IDLE;
  reg [31:0] raddr = 0;

  always @(posedge clk) begin
    hp_m_awready <= 0; hp_m_wready <= 0; hp_m_bvalid <= 0;
    hp_m_arready <= 0; hp_m_rvalid <= 0;
    case (wstate)
      WS_IDLE: if (o_hp_m_awvalid) begin
                 waddr <= o_hp_m_awaddr; hp_m_awready <= 1; wstate <= WS_W;
               end
      WS_W:    if (o_hp_m_wvalid) begin
                 ddr[(waddr - DATA_BASE) >> 3] <= o_hp_m_wdata;
                 hp_m_wready <= 1; wstate <= WS_B;
               end
      WS_B:    begin
                 hp_m_bvalid <= 1; hp_m_bresp <= 2'b00;
                 if (o_hp_m_bready) wstate <= WS_IDLE;
               end
      default: wstate <= WS_IDLE;
    endcase
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

  // ---- SMP-event counters (the ping-pong evidence) ----
  // wake_out pulses = FUTEX_WAKEs executed = doorbells delivered to the peer;
  // S_WAIT (st=10) cycles = time actually parked with every thread blocked,
  // which for a single-threaded core can ONLY be left via the doorbell.
  integer c0_wakes = 0, c1_wakes = 0, c0_waitc = 0, c1_waitc = 0;
  integer c0_kills = 0, c1_kills = 0;
  always @(posedge clk) if (!rst) begin
    if (o_c0_wake_out) c0_wakes = c0_wakes + 1;
    if (o_c1_wake_out) c1_wakes = c1_wakes + 1;
    if (o_c0_running && o_c0_st == 5'd10) c0_waitc = c0_waitc + 1;
    if (o_c1_running && o_c1_st == 5'd10) c1_waitc = c1_waitc + 1;
    if (dut.arb_res_kill0) c0_kills = c0_kills + 1;
    if (dut.arb_res_kill1) c1_kills = c1_kills + 1;
  end

  // ---- two cmd drivers (core = the wrapper's dr[39]) ----
  task cmd(input core, input [6:0] idx, input [31:0] data);
    begin
      @(negedge clk);
      if (core) begin c1_cmd_idx = idx; c1_cmd_data = data; c1_cmd_valid = 1; end
      else      begin c0_cmd_idx = idx; c0_cmd_data = data; c0_cmd_valid = 1; end
      @(negedge clk); c0_cmd_valid = 0; c1_cmd_valid = 0;
    end
  endtask

  integer i, cyc;
  reg c0_done_f, c1_done_f;
  initial begin
    for (di = 0; di < 65536; di = di + 1) ddr[di] = 64'd0;
    $readmemh(`PROG_HEX0, ddr, 512);              // core 0 text @ 0x1000
`ifdef PROG_HEX1
    $readmemh(`PROG_HEX1, ddr, (`TEXT1) >> 3);    // core 1 text @ TEXT1
`endif
    repeat (4) @(negedge clk); rst = 0;
    repeat (4) @(negedge clk);
    cmd(1'b0, 7'd13, 32'd1);                      // core0 reset (zeroing sweep)
    cmd(1'b1, 7'd13, 32'd1);                      // core1 reset
    repeat (1200) @(negedge clk);                 // 1024-cycle rf/dmem zero + margin
`ifdef PROG_HEX1
    cmd(1'b1, 7'd53, `TEXT1);                     // core1 SET_PC = TEXT1
`endif
`ifndef ONLY_C0
    c1_hold = 0;                                  // release CORE1_HOLD
`endif
`ifdef QUANTUM
    cmd(1'b0, 7'd57, `QUANTUM);                   // EXT-1: preemption quantum
    cmd(1'b1, 7'd57, `QUANTUM);                   // (cmd 57; 0 = disabled)
`endif
    cmd(1'b0, 7'd13, 32'd2);                      // core0 start
    cmd(1'b1, 7'd13, 32'd2);                      // core1 start (HELD if ONLY_C0)
    cyc = 0;
    c0_done_f = 0; c1_done_f = 0;
    while (!(c0_done_f && c1_done_f) && cyc < `MAXCYC) begin
      @(negedge clk); cyc = cyc + 1;
      c0_done_f = o_c0_halted || o_c0_trap_active;
`ifdef ONLY_C0
      c1_done_f = 1;
`else
      c1_done_f = o_c1_halted || o_c1_trap_active;
`endif
    end
    if (o_c0_trap_active) $display("C0 TRAP op=%02x pc=%0d", o_c0_trapped_op, o_c0_pc);
    if (o_c1_trap_active) $display("C1 TRAP op=%02x pc=%0d", o_c1_trapped_op, o_c1_pc);
    $display("CYCLES=%0d", cyc);
    $display("C0 HALTED=%0d pc=%0d retire=%0d", o_c0_halted, o_c0_pc, o_c0_retire);
    for (i = 1; i <= `NREGS; i = i + 1) $display("c0.r%0d=%0d", i, dut.c0_rf[i]);
    $display("C1 HALTED=%0d pc=%0d retire=%0d", o_c1_halted, o_c1_pc, o_c1_retire);
    for (i = 1; i <= `NREGS; i = i + 1) $display("c1.r%0d=%0d", i, dut.c1_rf[i]);
    $display("shared[0x10000]=%0d", ddr[32'h10000 >> 3]);
    $display("c0.wake_out=%0d c1.wake_out=%0d (FUTEX_WAKEs = doorbells sent to the peer)",
             c0_wakes, c1_wakes);
    $display("c0.S_WAIT_cycles=%0d c1.S_WAIT_cycles=%0d (parked; only a doorbell can resume)",
             c0_waitc, c1_waitc);
    $display("res_kill0=%0d res_kill1=%0d (remote-access reservation kills)",
             c0_kills, c1_kills);
    $display("c0.dmem32=%0d c1.dmem32=%0d", dut.c0_dmem[32], dut.c1_dmem[32]);
    $finish;
  end
endmodule
