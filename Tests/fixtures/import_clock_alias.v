// Copyright (c) 2026 Kevin Baragona
// SPDX-License-Identifier: Apache-2.0
module import_clock_alias(
  input wire clk_osc,
  input wire d,
  output reg q
);
  wire clk = clk_osc;

  always @(posedge clk)
    q <= d;
endmodule
