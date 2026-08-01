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
      Engine.predict "check-hit" Engine.design (Engine.chkSeq 0 5 1)
      Engine.predict "check-stale" Engine.design (Engine.chkSeq 0 5 9)
      Engine.predict "bump-then-check" Engine.design
        (Engine.bmpSeq 0 5 ++ Engine.chkSeq 0 5 1 ++ Engine.chkSeq 1 5 1
          ++ Engine.chkSeq 0 5 2)
      Engine.predict "poison" Engine.design
        (Engine.bmpSeq 0 7 true ++ Engine.chkSeq 0 7 2)
      Engine.predict "inflight" Engine.design
        ([{ r0 := (Engine.bmp 0 3).r0, r1 := (Engine.chk 1 3 1).r1 }]
          ++ Engine.gap 12 ++ Engine.chkSeq 1 3 1)
      Engine.predict "saturate(tiny)" Engine.tiny
        ((List.replicate 6 (Engine.bmpSeq 0 1)).flatten ++ Engine.chkSeq 0 1 7)
  | ["engine"] => do
      checkD19
      Engine.design.emit "rtl/epochengine.v"
      Engine.tiny.emit "rtl/epochengine_tiny.v"
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
      Engine.tiny.emit "rtl/epochengine_tiny.v"
      if ! EpochSoc.parOk then
        throw <| IO.userError "epoch soc: parOkB failed — instance names not disjoint"
      EpochSoc.epochSoc.emit "rtl/lnp64mini_epoch.v"
