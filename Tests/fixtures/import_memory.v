// Copyright (c) 2026 Kevin Baragona
// SPDX-License-Identifier: Apache-2.0
module import_memory(
  input wire clk,
  input wire [1:0] we0,
  input wire we1,
  input wire [1:0] addr0,
  input wire [1:0] addr1,
  input wire [1:0] raddr,
  input wire [7:0] wdata0,
  input wire [7:0] wdata1,
  output wire [7:0] q
);
  reg [7:0] mem [0:3];

  initial begin
    mem[0] = 8'h12;
    mem[1] = 8'h34;
    mem[2] = 8'h56;
    mem[3] = 8'hx8;
  end

  always @(posedge clk) begin
    if (we0[0]) mem[addr0][3:0] <= wdata0[3:0];
    if (we0[1]) mem[addr0][7:4] <= wdata0[7:4];
    if (we1) mem[addr1] <= wdata1;
  end

  assign q = mem[raddr];
endmodule
