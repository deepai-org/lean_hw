-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.FastEval
import Loom.Hw.Notation
import Loom.Hw.CompileCorrect
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO

/-!
# S1Counters — the ergonomics demo (typed handles + `act!` + balanced trees)

A small but non-trivial substrate design written *entirely* in the Part-B
EDSL surface:

* every register is a `Reg`/`RegArray` handle — the name string appears
  exactly once, in the handle;
* every rule body is `act! { … }` with `⇐` assignment and `when … do`
  guards, so the rules read like the Verilog they compile to;
* every wide reduction is a **balanced** `Loom.Hw.Trees` builder
  (`orTree`, `addTree`, `priTree`, `dynRead`, `dynWrite`) rather than a
  linear fold, with the proved evaluation lemmas behind it.

Behaviour: an LFSR sprays increments across eight 12-bit counters; a
running total (balanced adder tree), a saturation flag (balanced OR tree),
a first-above-threshold index (balanced priority tree), a dynamically
indexed read (`dynRd`) and a dynamically indexed clear (`dynSet`) exercise
every builder.

Corroboration: `check` runs the verified fast evaluator against the
reference `Design.cycle` in lockstep, and `scripts/s1counters_demo.sh`
simulates the emitted RTL under iverilog and compares against the fast
evaluator's prediction.
-/

namespace Machines.Substrate.S1Counters

open Loom.Hw
open Loom.Hw.Notation

/-! ## State — one handle per coordinate, one name string each -/

def cyc    : Reg 16 := ⟨"cyc"⟩
def lfsr   : Reg 16 := ⟨"lfsr"⟩
def total  : Reg 16 := ⟨"total"⟩
def anyMax : Reg 1  := ⟨"any_max"⟩
def sel    : Reg 3  := ⟨"sel"⟩
def sink   : Reg 12 := ⟨"sink"⟩
def hits   : Reg 16 := ⟨"hits"⟩

/-- Eight 12-bit counters: `bank0` … `bank7`, declared once. -/
def bank : RegArray 12 8 := ⟨"bank"⟩

def LFSR_INIT : Nat := 0xBEEF
def THRESH : Nat := 64

/-! ## Combinational helpers -/

/-- Galois-ish LFSR feedback, taps 15/13/12/10. -/
def fb : Expr 1 :=
  (Expr.slice lfsr.rd 15 1 ^^^ Expr.slice lfsr.rd 13 1) ^^^
  (Expr.slice lfsr.rd 12 1 ^^^ Expr.slice lfsr.rd 10 1)

/-- Per-counter increment enable: bit `i` of the LFSR. -/
def bump (i : Fin 8) : Expr 1 := Expr.slice lfsr.rd i.val 1

/-- Balanced 8-way adder tree of the (zero-extended) counters. -/
def totalE : Expr 16 := bank.sum (fun r => Expr.zext r.rd 16)

/-- Balanced 8-way OR tree: is any counter saturated? -/
def anyMaxE : Expr 1 := bank.any (fun r => r.rd === 0xFFF)

/-- Balanced priority tree: lowest-indexed counter at or above `THRESH`
(defaults to 7 when none is). -/
def selE : Expr 3 :=
  priTree ((List.finRange 8).map
    (fun i => (~~~(bank.rd i <ᵤ Expr.lit (BitVec.ofNat 12 THRESH)),
               Expr.lit (BitVec.ofNat 3 i.val)))) 7

/-! ## Rules -/

def tickRule : Rule := ⟨"tick", act! { cyc ⇐ cyc.rd + 1 }⟩

def lfsrRule : Rule :=
  ⟨"lfsr", act! { lfsr ⇐ (lfsr.rd <<< 1) ||| Expr.zext fb 16 }⟩

/-- One rule per counter — `RegArray` derives the name. -/
def bumpRule (i : Fin 8) : Rule :=
  ⟨s!"bump{i.val}",
   act! { when bump i then bank.set i (bank.rd i + 1) }⟩

/-- Dynamically indexed clear: when the LFSR's low nibble is `0xF`, clear
the counter selected by `lfsr[6:4]` (a `dynWrite` over the family). -/
def clearRule : Rule :=
  ⟨"clear",
   act! { when (Expr.slice lfsr.rd 0 4 === 0xF) then
            bank.dynSet (Expr.slice lfsr.rd 4 3) 0 }⟩

def obsRule : Rule :=
  ⟨"obs",
   act! { total ⇐ totalE,
          anyMax ⇐ anyMaxE,
          sel ⇐ selE,
          sink ⇐ bank.dynRd sel.rd 0,
          when anyMaxE then hits ⇐ hits.rd + 1 }⟩

def design : Design where
  name := "s1counters"
  regs :=
    [cyc.decl, lfsr.decl (BitVec.ofNat 16 LFSR_INIT), total.decl,
     anyMax.decl, sel.decl, sink.decl, hits.decl] ++ bank.decls
  mems := []
  rules :=
    [tickRule, lfsrRule] ++ (List.finRange 8).map bumpRule ++
    [clearRule, obsRule]

/-- The compiler's side condition.  `by rfl` rather than `by decide`: the
`Decidable` instance for `Bool` equality does not reduce through the
`RegArray` name derivation, but definitional unfolding does. -/
theorem design_wf : Compile.DesignWF design :=
  Compile.designWFCheck_sound design (by rfl)

/-- The FastEval side condition, discharged in the kernel — so
`Loom.Hw.FastEval.fastRun_eq` applies to this design as a theorem, not just
as a runtime check. -/
theorem design_fastWF : design.fastWFB = true := by rfl

/-! ## Cross-checks and emission -/

def fast : FastDesign := design.elaborate

/-- The observable state after `n` cycles, straight from the EDSL via the
verified fast evaluator. -/
def predictAt (n : Nat) : List (String × Nat) :=
  design.fastRegs (fastRun fast n design.fastReset)

/-- `fastCycle` ≡ the reference `Design.cycle` for `depth` cycles. -/
def check (depth : Nat := 200) : IO Unit := do
  if ← design.lockstep depth then
    IO.println s!"S1COUNTERS LOCKSTEP OK ({depth} cycles, fastCycle ≡ Design.cycle)"
  else
    IO.println "S1COUNTERS LOCKSTEP FAILED"

/-- The iverilog oracle: the full register state after `n` cycles. -/
def predict (n : Nat := 512) : IO Unit := do
  for (nm, v) in predictAt n do
    IO.println s!"{nm}={v}"

/-- The smoke testbench (kept in Lean because `rtl/` is generated). -/
def tb : String := "// Copyright (c) 2026 Kevin Baragona
// SPDX-License-Identifier: Apache-2.0
// Smoke testbench for the S1Counters ergonomics demo: run 512 cycles from
// reset and print the full register state as `name=value` lines, for
// comparison against the Loom fast evaluator's prediction.
`timescale 1ns/1ps
module tb_s1counters;
  reg clk = 0, rst = 1;
  wire [15:0] o_cyc, o_lfsr, o_total, o_hits;
  wire [0:0]  o_any_max;
  wire [2:0]  o_sel;
  wire [11:0] o_sink, o_bank0, o_bank1, o_bank2, o_bank3,
              o_bank4, o_bank5, o_bank6, o_bank7;
  integer i;

  s1counters dut(.clk(clk), .rst(rst),
    .o_cyc(o_cyc), .o_lfsr(o_lfsr), .o_total(o_total), .o_any_max(o_any_max),
    .o_sel(o_sel), .o_sink(o_sink), .o_hits(o_hits),
    .o_bank0(o_bank0), .o_bank1(o_bank1), .o_bank2(o_bank2), .o_bank3(o_bank3),
    .o_bank4(o_bank4), .o_bank5(o_bank5), .o_bank6(o_bank6), .o_bank7(o_bank7));

  initial begin
    // one reset edge, then 512 free-running cycles
    #1 clk = 1; #1 clk = 0; rst = 0;
    for (i = 0; i < 512; i = i + 1) begin
      #1 clk = 1; #1 clk = 0;
    end
    $display(\"cyc=%0d\", o_cyc);
    $display(\"lfsr=%0d\", o_lfsr);
    $display(\"total=%0d\", o_total);
    $display(\"any_max=%0d\", o_any_max);
    $display(\"sel=%0d\", o_sel);
    $display(\"sink=%0d\", o_sink);
    $display(\"hits=%0d\", o_hits);
    $display(\"bank0=%0d\", o_bank0);
    $display(\"bank1=%0d\", o_bank1);
    $display(\"bank2=%0d\", o_bank2);
    $display(\"bank3=%0d\", o_bank3);
    $display(\"bank4=%0d\", o_bank4);
    $display(\"bank5=%0d\", o_bank5);
    $display(\"bank6=%0d\", o_bank6);
    $display(\"bank7=%0d\", o_bank7);
    $finish;
  end
endmodule
"

def emit : IO Unit := do
  design.emit "rtl/s1counters.v"
  IO.FS.writeFile "rtl/tb_s1counters.v" tb
  IO.println "rtl/tb_s1counters.v written"

end Machines.Substrate.S1Counters
