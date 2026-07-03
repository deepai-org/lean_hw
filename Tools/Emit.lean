import Loom.Hw.Compile
import Loom.Emit.MicroVerilog.Print
import Machines.Acc8.Core
import Machines.Acc8.Iss
import Machines.Lnp64u.Hw.Core
import Machines.Lnp64u.Hw.Demo

/-!
# `lake exe emit` — emit µVerilog (tasks 2.5 / 1.11)

Targets:

* `acc8` (default) — the pathfinder design to `rtl/acc8.v`, plus its
  ISS-golden testbench `rtl/tb_acc8.v` (`scripts/lockstep_acc8.sh`).
* `lnp64u` — the LNP64-µ multicycle core, configured with the system-op
  demo manifest (the lockstep test's manifest), to `rtl/lnp64u.v`, plus a
  *generated* testbench `rtl/tb_lnp64u.v` whose expected values are
  computed here from the ISS (`stepN` of the same manifest): after 2000
  simulated cycles it compares the cycle counter, every domain's pc, run
  state, cause register and budget, and the golden memory cells, printing
  `LNP64U: PASS` iff all match (`scripts/lockstep_lnp64u.sh`).
-/

open Loom.Hw Loom.Emit.MicroVerilog

/-- The Acc8 testbench (golden values from `Acc8.goldenResult`). -/
def tbAcc8 : String := "`timescale 1ns/1ps
module tb;
  reg clk = 0, rst = 1;
  wire [7:0] o_acc, o_pc; wire o_halted;
  acc8 dut(.clk(clk), .rst(rst), .o_acc(o_acc), .o_pc(o_pc), .o_halted(o_halted));
  always #5 clk = ~clk;
  integer i;
  initial begin
    @(negedge clk); rst = 0;   // deassert reset after one cycle
    for (i = 0; i < 12; i = i + 1) @(negedge clk);
    $display(\"acc=%0d pc=%0d halted=%0d mem3=%0d\", o_acc, o_pc, o_halted, dut.mem[3]);
    $finish;
  end
endmodule
"

def emitAcc8 : IO Unit := do
  let img := Machines.Acc8.loadProg Machines.Acc8.golden
  let m := Loom.Hw.Compile.compile (Machines.Acc8.Core.design img)
  IO.FS.writeFile "rtl/acc8.v" (Print.print m)
  IO.FS.writeFile "rtl/tb_acc8.v" tbAcc8
  IO.println "rtl/acc8.v + rtl/tb_acc8.v written"

namespace Lnp64uEmit

open Machines.Lnp64u Machines.Lnp64u.Hw Machines.Lnp64u.Demo

/-- Simulated cycle count (matches the lockstep test's horizon). -/
def simCycles : Nat := 2000

/-- Re-materialize the spec state each cycle so `Fun.update` chains stay
shallow (pointwise identity; the emit-time golden run only). -/
private def canonDom (ds : DomainState) : DomainState :=
  let regs := Array.ofFn (fun r : Fin numRegs => ds.regs r)
  let caps := Array.ofFn (fun s : Fin numSlots => ds.caps s)
  let gens := Array.ofFn (fun s : Fin numSlots => ds.slotGen s)
  let lin := Array.ofFn (fun l : Fin numLineage => ds.lineage l)
  let rgn := Array.ofFn (fun r : Fin numRegions => ds.regions r)
  { ds with
    regs := fun r => regs[r.val]!
    caps := fun s => caps[s.val]!
    slotGen := fun s => gens[s.val]!
    lineage := fun l => lin[l.val]!
    regions := fun r => rgn[r.val]! }

private def canonSp (σ : MachineState) : MachineState :=
  let mem := Array.ofFn (fun i : Fin memWords => σ.mem (BitVec.ofNat 12 i.val))
  let d0 := canonDom (σ.doms 0)
  let d1 := canonDom (σ.doms 1)
  let d2 := canonDom (σ.doms 2)
  let d3 := canonDom (σ.doms 3)
  { σ with
    mem := fun a => mem[a.toNat]!
    doms := fun d =>
      if d.val = 0 then d0 else if d.val = 1 then d1
      else if d.val = 2 then d2 else d3 }

/-- The golden memory cells the demo programs populate. -/
def goldenAddrs : List Nat :=
  [0x410, 0x424, 0x425, 0x426, 0x427, 0x428, 0x429, 0x42A, 0x42B, 0x42C,
   0x42D, 0x42E, 0x440, 0x480, 0x481, 0x482, 0x483, 0x500, 0x501, 0x502,
   0x520, 0x700, 0x7C7]

/-- The generated testbench: run `simCycles`, compare against the ISS. -/
def tbLnp64u : String := Id.run do
  let final := (List.range simCycles).foldl
    (fun σ _ => canonSp (step sysManifest σ)) sysManifest.initState
  let mut checks : List (String × Nat × Nat) := []  -- (lhs, width, expected)
  checks := checks ++ [("dut.cycle", 32, final.cycle)]
  for d in List.finRange numDomains do
    let ds := final.doms d
    checks := checks ++
      [ (s!"dut.d{d.val}_pc", 12, ds.pc.toNat),
        (s!"dut.d{d.val}_run", 2, (encRun ds.run).toNat),
        (s!"dut.d{d.val}_cause", 32, ds.cause.toNat),
        (s!"dut.d{d.val}_budget", 32, ds.budget) ]
  for a in goldenAddrs do
    checks := checks ++
      [(s!"dut.mem[{a}]", 32, (final.mem (BitVec.ofNat 12 a)).toNat)]
  let body := String.join <| checks.map fun (lhs, w, v) =>
    s!"    if ({lhs} !== {w}'d{v}) begin errs = errs + 1; " ++
    s!"$display(\"LNP64U MISMATCH {lhs} exp={v} got=%0d\", {lhs}); end\n"
  return "`timescale 1ns/1ps\nmodule tb;\n  reg clk = 0, rst = 1;\n" ++
    "  lnp64u dut(.clk(clk), .rst(rst));\n" ++
    "  always #5 clk = ~clk;\n  integer i; integer errs = 0;\n" ++
    "  initial begin\n    @(negedge clk); rst = 0;\n" ++
    s!"    for (i = 0; i < {simCycles}; i = i + 1) @(negedge clk);\n" ++
    body ++
    "    if (errs == 0) $display(\"LNP64U: PASS\");\n" ++
    "    else $display(\"LNP64U: FAIL (%0d mismatches)\", errs);\n" ++
    "    $finish;\n  end\nendmodule\n"

def emit : IO Unit := do
  IO.println "compiling lnp64u (system-op demo manifest) ..."
  let m := Loom.Hw.Compile.compile (core sysManifest)
  IO.println "printing rtl/lnp64u.v ..."
  IO.FS.writeFile "rtl/lnp64u.v" (Print.print m)
  IO.println s!"generating rtl/tb_lnp64u.v (ISS goldens, {simCycles} cycles) ..."
  IO.FS.writeFile "rtl/tb_lnp64u.v" tbLnp64u
  let sz ← (System.FilePath.mk "rtl/lnp64u.v").metadata
  IO.println s!"rtl/lnp64u.v ({sz.byteSize} bytes) + rtl/tb_lnp64u.v written"

end Lnp64uEmit

def main (args : List String) : IO Unit := do
  IO.FS.createDirAll "rtl"
  match args with
  | [] | ["acc8"] => emitAcc8
  | ["lnp64u"] => Lnp64uEmit.emit
  | _ => throw (IO.userError "usage: emit [acc8|lnp64u]")
