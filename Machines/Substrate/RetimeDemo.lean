-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Retime
import Loom.Hw.EmitIO
import Loom.Hw.Declarations

/-!
# Retime demo: registered-output split on a write-only observability latch

A minimal design in the proved `retimeReg_stutter` class (no rule reads the
retimed register): a free-running counter `cnt` and a *write-only*
observability latch `obs := cnt + 7` (nothing reads `obs`). Retiming `obs`
via `retimeReg` cuts the `+7` cone at a new register `obs__pre` and copies
back one cycle later, so the retimed `obs` stream is the baseline `obs`
stream delayed by exactly one cycle.

`emit` writes the baseline, the retimed design, and a combined testbench that
instantiates both and asserts the 1-cycle-delay relation over 40 cycles
(`scripts/retime_demo.sh` runs iverilog). `check` cross-checks the same
relation on the in-repo EDSL semantics (kernel-evaluated).
-/

namespace Machines.Substrate.RetimeDemo

open Loom.Hw

def cntReg : Reg 8 := ⟨"cnt"⟩
def obsReg : Reg 8 := ⟨"obs"⟩

/-- Baseline: `cnt` counts; `obs` latches `cnt + 7`. Nothing reads `obs`, so
`obs ∈` the proved `retimeReg_stutter` observability class. -/
def declarations : Declarations :=
  Declarations.empty
    |>.addReg cntReg (exported := true)
    |>.addReg obsReg (init := 7) (exported := true)

def baseline : Design :=
  Design.ofDecls "retime_base" declarations
    [ ⟨"tick", cntReg.set (.add cntReg.rd (.lit 1))⟩
    , ⟨"latch", obsReg.set (.add cntReg.rd (.lit 7))⟩ ]

def cuts : List RetimeCut := [RetimeCut.ofReg obsReg]

/-- The retimed design: `obs` split through `obs__pre`. The one-cut plan uses
the same batch API as larger selected-cut transforms. Renamed so it can be
instantiated alongside the baseline in one testbench. -/
def retimed : Design :=
  { retimePlan baseline cuts with name := "retime_base_retimed" }

/-- The retime is legal (decidable guard passes): `obs` declared at width 8,
`obs__pre` fresh, no rule reads `obs`. -/
example : retimeRegOkB baseline "obs" 8 = true := by decide

example : retimePlanOkB baseline cuts = true := by decide

/-! ## EDSL-level self-check of the 1-cycle delay -/

/-- `obs` after `n` baseline cycles. -/
def baseObs (n : Nat) : Nat :=
  ((baseline.run n baseline.reset).regs "obs" 8).toNat

/-- `obs` after `n` retimed cycles. -/
def retObs (n : Nat) : Nat :=
  ((retimed.run n retimed.reset).regs "obs" 8).toNat

/-- The retimed `obs` at cycle `n+1` equals the baseline `obs` at cycle `n`
(a one-cycle lag), checked on the EDSL semantics for the first cycles. -/
def check : IO Unit := do
  let mut ok := true
  for n in List.range 12 do
    -- retimed obs lags baseline obs by one cycle
    if retObs (n + 1) ≠ baseObs n then
      IO.println s!"MISMATCH n={n}: retimed obs@{n+1}={retObs (n+1)} baseline obs@{n}={baseObs n}"
      ok := false
  if ok then
    IO.println "RETIME_DEMO EDSL OK (retimed obs = baseline obs delayed one cycle)"
  else
    IO.println "RETIME_DEMO EDSL FAILED"

/-! ## Emission (baseline + retimed + combined delay-checking testbench) -/

def tb : String := "`timescale 1ns/1ps
module tb;
  reg clk = 0, rst = 1;
  retime_base base(.clk(clk), .rst(rst));
  retime_base_retimed rt(.clk(clk), .rst(rst));
  always #5 clk = ~clk;
  integer i;
  reg [7:0] prev_obs;
  reg fail;
  initial begin
    fail = 0;
    @(negedge clk); rst = 0;      // deassert reset
    @(negedge clk);               // first live edge: base.obs / rt.obs updated
    prev_obs = base.obs;
    for (i = 0; i < 40; i = i + 1) begin
      @(negedge clk);
      // retimed obs should equal the PREVIOUS baseline obs (1-cycle delay)
      if (rt.obs !== prev_obs) begin
        $display(\"FAIL i=%0d rt.obs=%0d expected(prev base.obs)=%0d\", i, rt.obs, prev_obs);
        fail = 1;
      end
      prev_obs = base.obs;
    end
    if (fail) $display(\"retime_demo: DIVERGENCE\");
    else $display(\"retime_demo: OK (rt.obs == base.obs delayed 1 cycle, 40 cycles)\");
    $finish;
  end
endmodule
"

/-- Emit baseline, retimed, and the combined testbench. -/
def emit : IO Unit := do
  baseline.emit "rtl/retime_base.v"
  retimed.emit "rtl/retime_retimed.v"
  IO.FS.writeFile "rtl/tb_retime.v" tb
  IO.println "rtl/retime_base.v + rtl/retime_retimed.v + rtl/tb_retime.v written"

end Machines.Substrate.RetimeDemo
