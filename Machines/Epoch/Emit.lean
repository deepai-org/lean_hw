-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Epoch.Engine
import Machines.Epoch.EpochSoc
import Evidence.Targets.Memory

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

/-- The tiny simulation configuration uses non-zero images in banks that the
XC7 profile classifies as soft memory. Its target-specific emitter records
that known loss. Deploying this configuration requires an explicit reset
sweep instead of relying on its image. -/
private def tinyEmit : Loom.Hw.Design :=
  { Machines.Epoch.Engine.tiny with
    ackMemInit := ["cell_epoch", "repl0", "repl1"] }

open Machines.Epoch in
def main (args : List String) : IO Unit := do
  let target := Loom.Evidence.Targets.Memory.xc7
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
      Engine.design.emitFor target "rtl/epochengine.v"
      tinyEmit.emitFor target "rtl/epochengine_tiny.v"
  | ["soc"] => do
      checkD19
      if ! EpochSoc.parOk then
        throw <| IO.userError "epoch soc: parOkB failed — instance names not disjoint"
      if ! EpochSoc.syncReadOk then
        IO.println EpochSoc.syncReadReport
        throw <| IO.userError "epoch soc: D19 syncReadOkB failed"
      EpochSoc.epochSoc.emitFor target "rtl/lnp64mini_epoch.v"
  | _ => do
      checkD19
      Engine.design.emitFor target "rtl/epochengine.v"
      tinyEmit.emitFor target "rtl/epochengine_tiny.v"
      if ! EpochSoc.parOk then
        throw <| IO.userError "epoch soc: parOkB failed — instance names not disjoint"
      EpochSoc.epochSoc.emitFor target "rtl/lnp64mini_epoch.v"
