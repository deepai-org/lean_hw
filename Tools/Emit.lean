import Loom.Hw.Compile
import Loom.Emit.MicroVerilog.Print
import Machines.Acc8.Core
import Machines.Acc8.Iss

/-!
# `lake exe emit` — emit µVerilog (task 2.5)

Compiles the Acc8 core (the pathfinder design) through the EDSL→µVerilog
compiler and prints it to `rtl/acc8.v`. LNP64-µ's multicycle core joins
once it is written (task 1.11, Lnp64u half).
-/

open Loom.Hw Loom.Emit.MicroVerilog Machines.Acc8

def main : IO Unit := do
  IO.FS.createDirAll "rtl"
  let img := loadProg golden
  let m := Compile.compile (Core.design img)
  IO.FS.writeFile "rtl/acc8.v" (Print.print m)
  IO.println "rtl/acc8.v written"
