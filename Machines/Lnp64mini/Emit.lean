-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64mini.Core
import Machines.Lnp64mini.Iss
import Machines.Lnp64mini.Harness
import Machines.Lnp64mini.HpMaster
import Machines.Lnp64mini.GpMaster
import Machines.Lnp64mini.HpArbiter
import Machines.Lnp64mini.Soc
import Machines.Lnp64mini.DualSoc

/-!
# Lnp64mini runner (root `main`, kept out of the `Machines` umbrella)

```console
lake env lean --run Machines/Lnp64mini/Emit.lean            # emit rtl/lnp64mini.v
lake env lean --run Machines/Lnp64mini/Emit.lean soc        # emit rtl/lnp64mini_soc.v
lake env lean --run Machines/Lnp64mini/Emit.lean dual       # emit rtl/lnp64mini_dual.v
lake env lean --run Machines/Lnp64mini/Emit.lean selftest   # EDSL ≡ ISS lockstep
lake env lean --run Machines/Lnp64mini/Emit.lean hpselftest # HP master EDSL ≡ ISS
lake env lean --run Machines/Lnp64mini/Emit.lean gpselftest # GP master EDSL ≡ ISS
lake env lean --run Machines/Lnp64mini/Emit.lean arbselftest # HP arbiter EDSL ≡ ISS
lake env lean --run Machines/Lnp64mini/Emit.lean smpselftest # res_kill/doorbell/hold/wake_out
lake env lean --run Machines/Lnp64mini/Emit.lean progtest   # ISS runs a program to EXIT
```
-/

open Machines.Lnp64mini in
def main (args : List String) : IO Unit := do
  match args with
  | ["selftest"]   => selftest
  | ["hpselftest"] => Machines.Lnp64mini.HpMaster.selftest
  | ["gpselftest"] => Machines.Lnp64mini.GpMaster.selftest
  | ["arbselftest"] => Machines.Lnp64mini.HpArbiter.selftest
  | ["smpselftest"] => smpSelftest
  | ["progtest"]   => progtest
  | ["soc"]        =>
      if ! Machines.Lnp64mini.Soc.parOk then
        throw <| IO.userError "soc: parOkB failed — instance names not disjoint"
      Machines.Lnp64mini.Soc.soc.emit "rtl/lnp64mini_soc.v"
  | ["dual"]       =>
      if ! Machines.Lnp64mini.DualSoc.parOk then
        throw <| IO.userError "dual: parOkB failed — instance names not disjoint"
      Machines.Lnp64mini.DualSoc.dual.emit "rtl/lnp64mini_dual.v"
  | _ => design.emit "rtl/lnp64mini.v"
