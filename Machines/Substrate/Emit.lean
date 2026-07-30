-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Substrate.S0Blinky
import Machines.Substrate.S13Soak

/-!
# Substrate runner

The runnable shim for the substrate ports (kept out of the `Machines`
umbrella so its root `main` cannot clash with the tutorial's):

```console
lake env lean --run Machines/Substrate/Emit.lean            # emit both .v files
lake env lean --run Machines/Substrate/Emit.lean selftest   # Design ≡ ISS, small K
lake env lean --run Machines/Substrate/Emit.lean predict    # ISS state at K (silicon oracle)
```
-/

open Machines.Substrate in
def main (args : List String) : IO Unit := do
  match args with
  | ["selftest"] => S13Soak.selftest
  | ["predict"]  => S13Soak.predict
  | _ => do
      S0Blinky.emit
      S13Soak.emit
