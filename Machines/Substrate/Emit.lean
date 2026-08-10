-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Substrate.S0Blinky
import Machines.Substrate.S13Soak
import Machines.Substrate.S0BscanRegs
import Machines.Substrate.RetimeDemo
import Machines.Substrate.FanoutDemo
import Machines.Substrate.S1Counters

/-!
# Substrate runner

The runnable shim for the substrate ports (kept out of the `Machines`
umbrella so its root `main` cannot clash with the tutorial's):

```console
lake env lean --run Machines/Substrate/Emit.lean            # emit both .v files
lake env lean --run Machines/Substrate/Emit.lean selftest   # Design ≡ ISS, small K
lake env lean --run Machines/Substrate/Emit.lean predict    # ISS state at K (silicon oracle)
lake env lean --run Machines/Substrate/Emit.lean retime     # emit + EDSL-check retime demo
lake env lean --run Machines/Substrate/Emit.lean fanout    # emit + check fan-out demo
```
-/

open Machines.Substrate in
def main (args : List String) : IO Unit := do
  match args with
  | ["selftest"] => do
      S13Soak.selftest
      S0BscanRegs.selftest
      S1Counters.check
  | ["predict"]         => S13Soak.predict
  | ["predict-s0bscan"] => S0BscanRegs.predict
  | ["s1check"]   => S1Counters.check
  | ["s1predict"] => S1Counters.predict
  | ["retime"] => do
      RetimeDemo.check
      RetimeDemo.emit
  | ["fanout"] => do
      FanoutDemo.check
      FanoutDemo.reportCost
      FanoutDemo.emit
  | _ => do
      S0Blinky.emit
      S13Soak.emit
      S0BscanRegs.emit
      S1Counters.emit
