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
lake env lean --run Machines/Lnp64mini/Emit.lean preemptselftest # EXT-1 quantum / preemption tick
lake env lean --run Machines/Lnp64mini/Emit.lean domselftest     # EXT-2 protection domains
lake env lean --run Machines/Lnp64mini/Emit.lean preempthex   # write fpga/zc702/preempt.hex
lake env lean --run Machines/Lnp64mini/Emit.lean preemptpredict 64  # the EXT-1 iverilog oracle
lake env lean --run Machines/Lnp64mini/Emit.lean progtest   # ISS runs a program to EXIT
lake env lean --run Machines/Lnp64mini/Emit.lean d19        # D19 sync-read (BRAM) report
```

Every emit path first discharges the D19 obligation (`syncReadOk`): `rf`,
`dmem` and `uart_mem` must be read only through register-latch sites, or
the emitted RTL silently becomes LUTRAM and the dual core stops fitting
(`Loom/Hw/D19_SPEC.md`).
-/

open Machines.Lnp64mini in
/-- Refuse to emit unless the D19 sync-read shape still holds. -/
private def checkD19 : IO Unit := do
  if ! Machines.Lnp64mini.syncReadOk then
    IO.println Machines.Lnp64mini.syncReadReport
    throw <| IO.userError
      "D19: syncReadOkB failed \u2014 a memory in syncReadMems is read outside a register-latch site (it would emit as LUTRAM); see Loom/Hw/D19_SPEC.md"

open Machines.Lnp64mini in
def main (args : List String) : IO Unit := do
  match args with
  | ["d19"]        => IO.println Machines.Lnp64mini.syncReadReport
  | ["selftest"]   => selftest
  | ["hpselftest"] => Machines.Lnp64mini.HpMaster.selftest
  | ["gpselftest"] => Machines.Lnp64mini.GpMaster.selftest
  | ["arbselftest"] => Machines.Lnp64mini.HpArbiter.selftest
  | ["smpselftest"] => smpSelftest
  | ["preemptselftest"] => preemptSelftest
  | ["domselftest"] => domSelftest
  | ["failstopselftest"] => failstopSelftest
  | ["preempthex"]  => writePreemptHex "fpga/zc702/preempt.hex"
  | ["preemptpredict", q] => preemptPredict ((q.toNat?).getD 0)
  | ["progtest"]   => progtest
  | ["soc"]        =>
      checkD19
      if ! Machines.Lnp64mini.Soc.parOk then
        throw <| IO.userError "soc: parOkB failed — instance names not disjoint"
      Machines.Lnp64mini.Soc.soc.emit "rtl/lnp64mini_soc.v"
  | ["dual"]       =>
      checkD19
      if ! Machines.Lnp64mini.DualSoc.parOk then
        throw <| IO.userError "dual: parOkB failed — instance names not disjoint"
      Machines.Lnp64mini.DualSoc.dual.emit "rtl/lnp64mini_dual.v"
  | _ => checkD19; design.emit "rtl/lnp64mini.v"
