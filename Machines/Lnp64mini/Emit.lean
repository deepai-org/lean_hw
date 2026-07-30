-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64mini.Core
import Machines.Lnp64mini.Iss
import Machines.Lnp64mini.Harness

/-!
# Lnp64mini runner (root `main`, kept out of the `Machines` umbrella)

```console
lake env lean --run Machines/Lnp64mini/Emit.lean            # emit rtl/lnp64mini.v
lake env lean --run Machines/Lnp64mini/Emit.lean selftest   # EDSL ≡ ISS lockstep
lake env lean --run Machines/Lnp64mini/Emit.lean progtest   # ISS runs a program to EXIT
```
-/

open Machines.Lnp64mini in
def main (args : List String) : IO Unit := do
  match args with
  | ["selftest"] => selftest
  | ["progtest"] => progtest
  | _ => design.emit "rtl/lnp64mini.v"
