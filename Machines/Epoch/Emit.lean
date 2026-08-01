-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Epoch.Engine
import Machines.Epoch.EpochSoc

/-!
# Epoch-engine runner (Layer 2)

```console
lake env lean --run Machines/Epoch/Emit.lean selftest  # FastEval acceptance ladder (D18)
lake env lean --run Machines/Epoch/Emit.lean d19       # sync-read (BRAM) shape report
lake env lean --run Machines/Epoch/Emit.lean predict   # the iverilog testbench's oracle
lake env lean --run Machines/Epoch/Emit.lean engine    # rtl/epochengine{,_tiny}.v
lake env lean --run Machines/Epoch/Emit.lean soc       # rtl/lnp64mini_epoch.v
```

Every emit path first discharges the D19 obligation: if a bank stops being
read through a register latch it becomes LUTRAM and the composed design
stops fitting, so emission refuses rather than silently regressing.
-/

open Machines.Epoch in
private def checkD19 : IO Unit := do
  if ! Engine.syncReadOkB Engine.design then
    IO.println (Engine.syncReadReport Engine.design)
    throw <| IO.userError "D19: the engine's banks are not sync-read shaped"

/-- `epochengine_tiny` as *emitted*: `Engine.tiny` plus the D37
acknowledgement that its reset image is one the FPGA flow does not deliver.

**The finding.** `Engine.mems`' docstring says the three epoch banks are
"exactly the banks the target flow maps to block RAM". That holds for
`cfg32` (512×32 → `RAMB18E1`, `INIT_xx` delivered — re-confirmed against
yosys 0.33) and **fails for `cfgTiny`**: 4×3 banks map to `RAM32M`, whose
image the configuration path drops exactly as it dropped D30's
`cell_flags`. `Loom/Hw/MemInitOk.lean` predicted it from the declared shape
and `scripts/check_mem_init.py` confirms it on the netlist. Nothing had ever
looked: `epochengine_tiny` is not in `eqcheck.sh`'s design list.

**Acknowledged, not fixed, and why.** The reset image *is* `Protocol.Init`
(deviation E4 — there is no install op), so taking it out of memory the way
`tpc` and `cell_flags` did would break `abs(reset) = Protocol.Init` and every
theorem stated over `runOpen`-from-reset. And it costs nothing to leave: the
board artifacts are `epochengine` and `lnp64mini_epoch`, both `cfg32`;
`cfgTiny` exists so the iverilog ladder can reach §3's saturation case at a
width where saturation is reachable. Anyone putting `epochengine_tiny` on a
fabric must add a reset sweep first.

**Why here and not on `Engine.tiny`.** `ackMemInit` is read by no semantic
function — it is a fact about emitting the artifact, not about the machine —
and the Layer-3 theorems in `Refines.lean` are stated over
`Engine.mkDesign cfgTiny`, which a differing field would no longer unify
with. Attaching it at the emission site keeps the proved object literally
unchanged. The emitted text is identical either way. -/
private def tinyEmit : Loom.Hw.Design :=
  { Machines.Epoch.Engine.tiny with
    ackMemInit := ["cell_epoch", "repl0", "repl1"] }

open Machines.Epoch in
def main (args : List String) : IO Unit := do
  match args with
  | ["selftest"] => do
      Engine.selftest
      Engine.latency
      Engine.refCheck
  | ["d19"] => do
      IO.println (Engine.syncReadReport Engine.design)
      IO.println EpochSoc.syncReadReport
      IO.println s!"composed syncReadOk = {EpochSoc.syncReadOk}"
      IO.println s!"composed parOk      = {EpochSoc.parOk}"
  | ["predict"] => do
      Engine.predict "epochengine" Engine.design Engine.tbTrace
      Engine.predict "epochengine_tiny" Engine.tiny Engine.tbTraceTiny
  | ["engine"] => do
      checkD19
      Engine.design.emit "rtl/epochengine.v"
      tinyEmit.emit "rtl/epochengine_tiny.v"
  | ["soc"] => do
      checkD19
      if ! EpochSoc.parOk then
        throw <| IO.userError "epoch soc: parOkB failed — instance names not disjoint"
      if ! EpochSoc.syncReadOk then
        IO.println EpochSoc.syncReadReport
        throw <| IO.userError "epoch soc: D19 syncReadOkB failed"
      EpochSoc.epochSoc.emit "rtl/lnp64mini_epoch.v"
  | _ => do
      checkD19
      Engine.design.emit "rtl/epochengine.v"
      tinyEmit.emit "rtl/epochengine_tiny.v"
      if ! EpochSoc.parOk then
        throw <| IO.userError "epoch soc: parOkB failed — instance names not disjoint"
      EpochSoc.epochSoc.emit "rtl/lnp64mini_epoch.v"
