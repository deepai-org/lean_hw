-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Emit.MicroVerilog.RoundTrip

/-!
# Parser-boundary counterexamples

These kernel checks pin two important limits on the release theorem:

* successful parsing does not imply byte canonicity, because legal SSA wire
  names need not be the reference printer's `n0`, `n1`, … names;
* parsing a printed memory recovers its addressable initialization image, not
  arbitrary values of the source initialization function beyond that image.

Consequently release certification uses a concrete-syntax certificate that
preserves and renders the exact SSA program; it does not rely on a false
`parse t = some m → t = print m` theorem.
-/

namespace Tests.ParserBoundary

open Loom.Emit.MicroVerilog

private def renamedWireText : String :=
  "module demo(\n  input wire clk,\n  input wire rst\n);\n  reg [0:0] r;\n  wire [0:0] x = 1'd0;\n  always @(posedge clk) begin\n    if (rst) begin\n      r <= 1'd0;\n    end else begin\n      r <= x;\n    end\n  end\nendmodule"

example : (Parse.parse renamedWireText).isSome = true := by decide +kernel

/-- A concrete counterexample to full parser canonicity. -/
example : (Parse.parse renamedWireText).map Print.print ≠
    some renamedWireText := by decide +kernel

private def wideInit : Module where
  name := "mem_demo"
  regs := []
  mems := [({ name := "m", addrWidth := 1, dataWidth := 1,
              init := fun _ => 1, wrPorts := [] } : MemDef)]
  outs := []

-- Address `2` is outside a one-bit memory's address space. The printer does
-- not serialize it and the parser intentionally reconstructs zero there.
#guard (match Parse.parse (Print.print wideInit) with
  | some { mems := parsedMem :: _, .. } => parsedMem.init 2 == 0
  | _ => false)

example : (match wideInit.mems with
    | sourceMem :: _ => (sourceMem.init 2).toNat = 1
    | [] => False) := by simp [wideInit]

end Tests.ParserBoundary
