-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.CapWalk.Engine
import Machines.CapWalk.CapSoc
import Evidence.Targets.Memory

/-!
# CapWalk runner (Layer 2)

```console
lake env lean --run Machines/CapWalk/Emit.lean selftest  # FastEval acceptance ladder (D18)
lake env lean --run Machines/CapWalk/Emit.lean d19       # sync-read (BRAM) shape report
lake env lean --run Machines/CapWalk/Emit.lean predict   # the iverilog testbench's oracle
lake env lean --run Machines/CapWalk/Emit.lean ddr       # fpga/zc702/capwalk_ddr.hex
lake env lean --run Machines/CapWalk/Emit.lean engine    # rtl/capwalk.v
lake env lean --run Machines/CapWalk/Emit.lean soc       # rtl/lnp64mini_cap.v
```

Every emit path first discharges the D19 obligation and D38's
realizability check against the declared memory target: `cell_flags` and
`c_tag` each have two writers (the drop/mint unit and the walker), so a
rule reorder that broke the strictly-increasing port order would silently
invalidate the emission theorem, and a bank pushed out of block RAM by a
second write port loses its reset image (CE10; `Loom/Hw/MemTarget.lean`).
Emission refuses rather than regressing.
-/

open Machines.CapWalk
open Loom.Evidence.Targets

private def checkShape : IO Unit := do
  if ! Engine.syncReadOkB Engine.design then
    IO.println (Engine.syncReadReport Engine.design)
    throw <| IO.userError "D19: the capwalk banks are not sync-read shaped"
  -- D38: the write-port discipline is Loom's now (`Design.memPortTraceOkB`
  -- and the `MemTarget` image rule, enforced by the explicit target check);
  -- checking it here as well keeps the failure at the top of the ladder,
  -- where it names the engine.
  if ! Engine.design.realizableOnB Memory.xc7 then
    IO.println (Memory.report Engine.design)
    throw <| IO.userError
      "D38: capwalk is not realizable on memory target 'xc7'"

/-- Write the behavioural DDR image the iverilog testbench loads. One
64-bit word per line; the Lean selftest and the RTL testbench therefore
read the *same* bytes. -/
private def hexImage (img : List (BitVec 64)) : String :=
  String.intercalate "\n"
    (img.map (fun w =>
      let s := String.ofList (Nat.toDigits 16 w.toNat)
      String.ofList (List.replicate (16 - s.length) '0') ++ s)) ++ "\n"

private def emitDdr : IO Unit := do
  IO.FS.writeFile "fpga/zc702/capwalk_ddr.hex" (hexImage Engine.ddrImage)
  IO.println "fpga/zc702/capwalk_ddr.hex written"
  IO.FS.writeFile "fpga/zc702/capwalk_ddr_remint.hex" (hexImage Engine.ddrImageRemint)
  IO.println "fpga/zc702/capwalk_ddr_remint.hex written"

def main (args : List String) : IO Unit := do
  match args with
  | ["selftest"] => do
      Engine.selftest
      Engine.latency
      Engine.refCheck
  | ["d19"] => do
      IO.println (Engine.syncReadReport Engine.design)
      IO.println CapSoc.syncReadReport
      IO.println (Memory.report Engine.design)
      IO.println s!"composed syncReadOk = {CapSoc.syncReadOk}"
      IO.println s!"composed parOk      = {CapSoc.parOk}"
  | ["predict"] => Engine.predict
  | ["ddr"] => emitDdr
  | ["engine"] => do
      checkShape
      Engine.design.emitFor Memory.xc7 "rtl/capwalk.v"
  | ["soc"] => do
      checkShape
      if ! CapSoc.parOk then
        throw <| IO.userError "cap soc: parOkB failed — instance names not disjoint"
      if ! CapSoc.syncReadOk then
        IO.println CapSoc.syncReadReport
        throw <| IO.userError "cap soc: D19 syncReadOkB failed"
      CapSoc.capSoc.emitFor Memory.xc7 "rtl/lnp64mini_cap.v"
  | _ => do
      checkShape
      Engine.design.emitFor Memory.xc7 "rtl/capwalk.v"
      emitDdr
      if ! CapSoc.parOk then
        throw <| IO.userError "cap soc: parOkB failed — instance names not disjoint"
      CapSoc.capSoc.emitFor Memory.xc7 "rtl/lnp64mini_cap.v"
