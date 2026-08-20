// Copyright (c) 2026 Kevin Baragona
// SPDX-License-Identifier: Apache-2.0
module import_mixed_edge(
  input wire clk,
  input wire rst,
  input wire d,
  output wire q,
  output wire sampled_on_falling
);
  reg falling_sample;
  reg rising_output;

  always @(negedge clk) begin
    if (rst) falling_sample <= 1'b0;
    else falling_sample <= d;
  end

  always @(posedge clk) begin
    if (rst) rising_output <= 1'b0;
    else rising_output <= falling_sample;
  end

  assign q = rising_output;
  assign sampled_on_falling = falling_sample;
endmodule
