-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Fanout
import Evidence.Targets.Memory
import Loom.Hw.Declarations
import Loom.Hw.EmitIO
import Loom.Hw.Cost

/-!
# Fan-out duplication demo

Eight independent consumer cones read one 16-bit source. The verified pass
moves four consumers to `source__dup` and mirrors the producer write, reducing
the EDSL's maximum syntactic fan-out from eight to four while adding one
16-bit register. The accompanying script emits and synthesizes both forms so
the external tool's result is reported separately from the refinement proof.
-/

namespace Machines.Substrate.FanoutDemo

open Loom.Hw
open Loom.Evidence.Targets

def driverReg : Reg 16 := ⟨"driver"⟩
def sourceReg : Reg 16 := ⟨"source"⟩
def sinkRegs : RegArray 16 8 := ⟨"sink"⟩

def declarations : Declarations :=
  Declarations.empty
    |>.addReg driverReg (exported := true)
    |>.addReg sourceReg (exported := true)
    |>.addRegArray sinkRegs (exported := true)

def consumerRule (index : Fin 8) : Rule :=
  ⟨s!"consumer{index.val}",
    sinkRegs.set index (.add sourceReg.rd (.lit (BitVec.ofNat 16 index.val)))⟩

def baseline : Design :=
  Design.ofDecls "fanout_base" declarations <|
    [ ⟨"tick", driverReg.set (.add driverReg.rd (.lit 1))⟩
    , ⟨"produce", sourceReg.set
        (.xor driverReg.rd (.shl driverReg.rd (.lit 1)))⟩ ] ++
    (List.finRange 8).map consumerRule

def selectedConsumers : List String :=
  (List.range 4).map fun index => s!"consumer{index}"

def split : Design :=
  { duplicateFanoutReg baseline sourceReg "source__dup" selectedConsumers with
    name := "fanout_split" }

theorem checked : duplicateFanoutRegOkB baseline sourceReg "source__dup" = true := by
  decide

theorem legal : FanoutLegal baseline sourceReg.name 16 "source__dup" :=
  duplicateFanoutRegOkB_sound baseline sourceReg "source__dup" checked

/-- The machine-facing refinement object for this concrete transform. -/
def refinement : Loom.Simulation baseline.toTSys split.toTSys.reachablePart :=
  duplicateFanout_simulation baseline sourceReg.name 16 "source__dup"
    selectedConsumers legal

example : (baseline.cost Memory.xc7).maxFanout = 8 := by native_decide
/- The source cone itself splits 8→4; the whole-design maximum is 5 because
mirroring the two-read producer expression gives `driver` five read sites. -/
example : (split.cost Memory.xc7).maxFanout = 5 := by native_decide
example : (split.cost Memory.xc7).stateBits =
    (baseline.cost Memory.xc7).stateBits + 16 := by native_decide

def visible (design : Design) (state : St) : List (String × Nat) :=
  design.regs.filterMap fun decl =>
    if design.outputs.contains decl.name then
      some (decl.name, (state.regs decl.name decl.width).toNat)
    else none

/-- Executable corroboration of the proved abstraction over a short run. -/
def check : IO Unit := do
  let mut baseState := baseline.reset
  let mut splitState := split.reset
  let mut ok := true
  for cycle in List.range 32 do
    if visible baseline baseState ≠ visible baseline (fanoutAbs "source__dup" splitState) then
      IO.eprintln s!"fanout_demo: mismatch before cycle {cycle}"
      ok := false
    baseState := baseline.cycle baseState
    splitState := split.cycle splitState
  if ok then
    IO.println "FANOUT_DEMO EDSL OK (visible states agree for 32 cycles)"
  else
    throw <| IO.userError "fanout_demo: EDSL divergence"

def reportCost : IO Unit := do
  let base := baseline.cost Memory.xc7
  let transformed := split.cost Memory.xc7
  IO.println s!"fanout abstract base:  stateBits={base.stateBits} bitOps={base.bitOps} maxFanout={base.maxFanout}"
  IO.println s!"fanout abstract split: stateBits={transformed.stateBits} bitOps={transformed.bitOps} maxFanout={transformed.maxFanout}"

def tb : String := "`timescale 1ns/1ps
module tb;
  reg clk = 0, rst = 1;
  fanout_base base(.clk(clk), .rst(rst));
  fanout_split split(.clk(clk), .rst(rst));
  always #5 clk = ~clk;
  integer cycle;
  reg fail;
  initial begin
    fail = 0;
    @(negedge clk); rst = 0;
    for (cycle = 0; cycle < 40; cycle = cycle + 1) begin
      @(negedge clk);
      if ({base.driver, base.source,
           base.sink0, base.sink1, base.sink2, base.sink3,
           base.sink4, base.sink5, base.sink6, base.sink7} !==
          {split.driver, split.source,
           split.sink0, split.sink1, split.sink2, split.sink3,
           split.sink4, split.sink5, split.sink6, split.sink7}) begin
        $display(\"FAIL visible state mismatch at cycle %0d\", cycle);
        fail = 1;
      end
      if (split.source !== split.source__dup) begin
        $display(\"FAIL replica incoherent at cycle %0d\", cycle);
        fail = 1;
      end
    end
    if (fail) $display(\"fanout_demo: DIVERGENCE\");
    else $display(\"fanout_demo: OK (visible equivalence + replica coherence, 40 cycles)\");
    $finish;
  end
endmodule
"

def emit : IO Unit := do
  baseline.emit "rtl/fanout_base.v"
  split.emit "rtl/fanout_split.v"
  IO.FS.writeFile "rtl/tb_fanout.v" tb
  IO.println "rtl/fanout_base.v + rtl/fanout_split.v + rtl/tb_fanout.v written"

end Machines.Substrate.FanoutDemo
