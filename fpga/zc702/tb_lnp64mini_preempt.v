// tb_lnp64mini_preempt.v -- EXT-1 (the preemption tick) at the RTL.
//
// Same behavioral single-beat AXI3 slave as tb_lnp64mini_soc.v, driving the
// Loom-emitted lnp64mini_soc. The program (`preempt.hex`, written by
// `Machines/Lnp64mini/Emit.lean preempthex` from `progSpin`) is the Law-5
// story in nine words: thread 0 CLONEs a child and then **spins on a flag
// it never sets itself**; the child sets the flag and exits. On the
// cooperative machine the spinner owns the core forever and nothing else
// ever runs. With a quantum, the child gets the CPU, sets the flag, and
// thread 0 finishes.
//
// Everything printed is timing-INDEPENDENT (how many spin iterations
// thread 0 completes is not), so the line is diffable byte-for-byte against
// the Lean ISS oracle (`Emit.lean preemptpredict`) even though the AXI
// slave's latency differs from the harness DDR model's.
//
//   QUANTUM (define) -- cmd 56 payload; undefined = never written = 0 = off
//   MAXCYC  (define) -- run cap (the cooperative run never halts)
`timescale 1ns/1ps
`ifndef QUANTUM
  `define QUANTUM 32'd0
`endif
`ifndef MAXCYC
  `define MAXCYC 20000
`endif
module tb;
  reg clk = 0, rst = 1;
  always #5 clk = ~clk;

  reg         cmd_valid = 0;
  reg  [6:0]  cmd_idx = 0;
  reg  [31:0] cmd_data = 0;

  wire        o_running, o_halted, o_trap_active;
  wire [4:0]  o_st;
  wire [63:0] o_pc;
  wire [31:0] o_retire;
  wire [7:0]  o_trapped_op;

  wire [31:0] o_hp_m_awaddr;  wire o_hp_m_awvalid;
  wire [63:0] o_hp_m_wdata;   wire o_hp_m_wvalid;
  wire        o_hp_m_bready;
  wire [31:0] o_hp_m_araddr;  wire o_hp_m_arvalid;
  wire        o_hp_m_rready;
  reg         hp_m_awready = 0, hp_m_wready = 0, hp_m_bvalid = 0;
  reg  [1:0]  hp_m_bresp = 0;
  reg         hp_m_arready = 0, hp_m_rvalid = 0;
  reg  [63:0] hp_m_rdata_in = 0;
  reg  [1:0]  hp_m_rresp = 0;
  reg         gpm_m_awready = 1, gpm_m_wready = 1, gpm_m_bvalid = 1;
  reg  [1:0]  gpm_m_bresp = 0;
  reg         gpm_m_arready = 1, gpm_m_rvalid = 1;
  reg  [31:0] gpm_m_rdata_in = 0;
  reg  [1:0]  gpm_m_rresp = 0;

  lnp64mini_soc dut (
    .clk(clk), .rst(rst),
    .cmd_valid(cmd_valid), .cmd_idx(cmd_idx), .cmd_data(cmd_data),
    .hp_m_awready(hp_m_awready), .hp_m_wready(hp_m_wready),
    .hp_m_bvalid(hp_m_bvalid), .hp_m_bresp(hp_m_bresp),
    .hp_m_arready(hp_m_arready), .hp_m_rvalid(hp_m_rvalid),
    .hp_m_rdata_in(hp_m_rdata_in), .hp_m_rresp(hp_m_rresp),
    .gpm_m_awready(gpm_m_awready), .gpm_m_wready(gpm_m_wready),
    .gpm_m_bvalid(gpm_m_bvalid), .gpm_m_bresp(gpm_m_bresp),
    .gpm_m_arready(gpm_m_arready), .gpm_m_rvalid(gpm_m_rvalid),
    .gpm_m_rdata_in(gpm_m_rdata_in), .gpm_m_rresp(gpm_m_rresp),
    .o_running(o_running), .o_halted(o_halted), .o_st(o_st),
    .o_pc(o_pc), .o_retire(o_retire),
    .o_trap_active(o_trap_active), .o_trapped_op(o_trapped_op),
    .o_hp_m_awaddr(o_hp_m_awaddr), .o_hp_m_awvalid(o_hp_m_awvalid),
    .o_hp_m_wdata(o_hp_m_wdata), .o_hp_m_wvalid(o_hp_m_wvalid),
    .o_hp_m_bready(o_hp_m_bready),
    .o_hp_m_araddr(o_hp_m_araddr), .o_hp_m_arvalid(o_hp_m_arvalid),
    .o_hp_m_rready(o_hp_m_rready));

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

  // The preemption fire predicate, read off the same registers the design
  // reads (S_F0 = 5'd1). Counted, but only its ZERO/NON-ZERO is printed:
  // how many ticks land inside a run is a function of AXI latency.
  integer fires = 0;
  always @(posedge clk) if (!rst) begin
    if (dut.running && !dut.halted && !dut.zeroing && dut.st == 5'd1 &&
        !dut.bus_req && !dut.trap_active && dut.quantum != 32'd0 &&
        dut.qctr == 32'd0 && dut.next_ready != dut.cur)
      fires = fires + 1;
  end

  task cmd(input [6:0] idx, input [31:0] data);
    begin
      @(negedge clk); cmd_idx = idx; cmd_data = data; cmd_valid = 1;
      @(negedge clk); cmd_valid = 0;
    end
  endtask

  integer cyc;
  initial begin
    for (di = 0; di < 65536; di = di + 1) ddr[di] = 64'd0;
    $readmemh(`PROG_HEX, ddr, 512);       // 512 = 0x1000>>3
    repeat (4) @(negedge clk); rst = 0;
    repeat (4) @(negedge clk);
    cmd(7'd13, 32'd1);                    // reset (starts the zeroing sweep)
    repeat (1200) @(negedge clk);         // 1024-cycle rf/dmem zero + margin
    cmd(7'd57, `QUANTUM);                 // EXT-1: the quantum (0 = disabled)
    cmd(7'd13, 32'd2);                    // start
    cyc = 0;
    while (!o_halted && !o_trap_active && cyc < `MAXCYC) begin
      @(negedge clk); cyc = cyc + 1;
    end
    $display("PREEMPT halted=%0d trap=%0d pc=%0d r5=%0d r9=%0d dmem0=%0d t1state=%0d preempted=%0d",
             o_halted, o_trap_active, o_halted ? o_pc : 0,
             dut.rf[5], dut.rf[9], dut.dmem[0], dut.tstate1, fires != 0);
    $finish;
  end
endmodule
