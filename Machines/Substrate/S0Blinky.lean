-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.FastEval
import Loom.Hw.CompileCorrect
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO

/-!
# S0Blinky — the substrate-0 bring-up blinky, ported to Loom

Port of `remote-fpga fpga/substrate0/rtl/s0_blinky.v`, the design that first
proved the open-source build+program pipeline on the ZC702 (xc7z020): a
free-running 28-bit counter whose top four bits drive the board LEDs at
visibly staggered rates from the 200 MHz system clock.

The Loom design is the counter itself — the synchronous logic. The board
top (`fpga/zc702/s0blinky_top.v`) is an untrusted wrapper in the same role
as a testbench: LVDS clock buffers (`IBUFDS`/`BUFG`, vendor primitives
outside µVerilog by design), reset tie-off, and the LED pin mapping
`leds = o_cnt[27:24]`.

This is Loom's first-light design for real FPGA bring-up (CHARTER Phase 2:
"first light on FPGA").
-/

namespace Machines.Substrate.S0Blinky

open Loom.Hw

def cnt : Expr 28 := .reg 28 "cnt"

/-- One rule: count every cycle (wraps mod 2^28). -/
def tick : Act := .write 28 "cnt" (.add cnt (.lit 1))

def design : Design where
  name  := "s0blinky"
  regs  := [⟨"cnt", 28, 0⟩]
  mems  := []
  rules := [⟨"tick", tick⟩]

theorem design_wf : Compile.DesignWF design :=
  Compile.designWFCheck_sound design (by decide)

/-- The FastEval side condition (`Loom/Hw/FastEval.lean`), discharged in the
kernel: `Loom.Hw.FastEval.fastRun_eq` applies to this design. -/
theorem design_fastWF : design.fastWFB = true := by rfl

/-- Emission entry (root `main` lives in `Machines/Substrate/Emit.lean` so
this module can sit in the `Machines` umbrella next to the tutorial's). -/
def emit : IO Unit := design.emit "rtl/s0blinky.v"

end Machines.Substrate.S0Blinky
