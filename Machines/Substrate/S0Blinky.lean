-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Declarations
import Loom.Hw.Semantics
import Loom.Hw.FastEval
import Loom.Hw.CompileCorrect
import Loom.Hw.CertifiedDesign
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

def cntReg : Reg 28 := ⟨"cnt"⟩
def cnt : Expr 28 := cntReg.rd

/-- One rule: count every cycle (wraps mod 2^28). -/
def tick : Act := cntReg.set (.add cnt (.lit 1))

def declarations : Declarations :=
  Declarations.empty.addReg cntReg (exported := true)

def design : Design :=
  Design.ofDecls "s0blinky" declarations [⟨"tick", tick⟩]

theorem design_wf : Compile.DesignWF design :=
  Compile.designWFCheck_sound design (by decide)

/-- The FastEval side condition (`Loom/Hw/FastEval.lean`), discharged in the
kernel: `Loom.Hw.FastEval.fastRun_eq` applies to this design. -/
theorem design_fastWF : design.fastWFB = true := by rfl

/-- The small publication-independent genericity witness: the same Design
supplies both the certified shared-DAG simulator and proved compilation. -/
def simulator : FastEval.VerifiedSimulator design := ⟨design_fastWF⟩

theorem dag_ready : (DagEval.prepareSimulator? simulator).isSome = true := by
  exact DagEval.prepareSimulator?_complete simulator

def dagSimulator : DagEval.VerifiedSimulator design :=
  DagEval.verifiedSimulatorOfPreparation simulator dag_ready

def certified : CertifiedDesign design :=
  CertifiedDesign.of design_wf dagSimulator

/-- Emission entry (root `main` lives in `Machines/Substrate/Emit.lean` so
this module can sit in the `Machines` umbrella next to the tutorial's). -/
def emit : IO Unit := design.emit "rtl/s0blinky.v"

end Machines.Substrate.S0Blinky
