-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.SSA

namespace Tests.ReleaseSSA

open Loom.Release.SSA

private def demo : Program where
  name := "demo"
  regs := [{ name := "r", width := 8, init := 0, next := "n1" }]
  mems := []
  wires := .node
    (.leaf [{ width := 8, name := "n0", rhs := .lit 8 1 }])
    (.leaf [{ width := 8, name := "n1", rhs := .bin .add "r" "n0" }])
  outs := [{ name := "o_r", width := 8, value := "r" }]

#guard demo.elaborate |>.isSome

example : demo.render = [
    "module demo(",
    "  input wire clk,",
    "  input wire rst,",
    "  output wire [7:0] o_r",
    ");",
    "  reg [7:0] r;",
    "  wire [7:0] n0 = 8'd1;",
    "  wire [7:0] n1 = r + n0;",
    "  always @(posedge clk) begin",
    "    if (rst) begin",
    "      r <= 8'd0;",
    "    end else begin",
    "      r <= n1;",
    "    end",
    "  end",
    "  assign o_r = r;",
    "endmodule"] := by decide +kernel

end Tests.ReleaseSSA
