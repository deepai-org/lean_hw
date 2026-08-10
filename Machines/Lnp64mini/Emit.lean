-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64mini.Core
import Machines.Lnp64mini.Harness
import Machines.Lnp64mini.HpMaster
import Machines.Lnp64mini.GpMaster
import Machines.Lnp64mini.HpArbiter
import Machines.Lnp64mini.Soc
import Machines.Lnp64mini.DualSoc
import Machines.Lnp64mini.DebugMap

/-!
# Lnp64mini runner (root `main`, kept out of the `Machines` umbrella)

```console
lake exe minitest            # emit rtl/lnp64mini.v
lake exe minitest soc        # emit rtl/lnp64mini_soc.v
lake exe minitest dual       # emit rtl/lnp64mini_dual.v
lake exe minitest debugmap   # emit the dual-board BSCAN debug include
lake exe minitest selftest   # core Design-derived architectural checks
lake exe minitest hpselftest # HP master Design outcome checks
lake exe minitest gpselftest # GP master Design outcome checks
lake exe minitest arbselftest # HP arbiter Design outcome checks
lake exe minitest smpselftest # res_kill/doorbell/hold/wake_out
lake exe minitest preemptselftest # EXT-1 quantum / preemption tick
lake exe minitest domselftest     # EXT-2 protection domains
lake exe minitest preempthex   # write fpga/zc702/preempt.hex
lake exe minitest preemptpredict 64  # Design-derived RTL expectation
lake exe minitest progtest   # run a program to EXIT on the proved simulator
lake exe minitest d19        # D19 sync-read (BRAM) report
```

D19 and instance-name disjointness are no longer discharged here. The
design declares `syncReadMems := ["rf","dmem","uart_mem"]` and `Design.emit`
enforces it, along with duplicate register/memory names (which is how a
`par`/`prefixed` with non-disjoint prefixes shows up). That is the point:
these were per-machine helpers each emit site had to remember to call, and
an obligation a caller can skip is not an obligation.
Run substantial selftests through the compiled `lake exe minitest <target>`
entry point.
-/

open Machines.Lnp64mini in
def main (args : List String) : IO Unit := do
  match args with
  | ["d19"]        => IO.println Machines.Lnp64mini.syncReadReport
  | ["selftest"]   => selftest
  | ["dcacheselftest"] => dcacheSelftest
  | ["hpselftest"] => Machines.Lnp64mini.HpMaster.selftest
  | ["gpselftest"] => Machines.Lnp64mini.GpMaster.selftest
  | ["arbselftest"] => Machines.Lnp64mini.HpArbiter.selftest
  | ["smpselftest"] => smpSelftest
  | ["preemptselftest"] => preemptSelftest
  | ["domselftest"] => domSelftest
  | ["failstopselftest"] => failstopSelftest
  | ["gateselftest"] => gateSelftest
  | ["gatehammerselftest"] => gateHammerSelftest
  | ["gatedwellselftest"] => gateDwellSelftest
  | ["faultconformanceselftest"] => faultConformanceSelftest
  | ["sentinelselftest"] => sentinelSelftest
  | ["refusalconformanceselftest"] => refusalConformanceSelftest
  | ["capxferselftest"] => capXferSelftest
  | ["slotfillselftest"] => slotFillSelftest
  | ["mmuselftest"] => mmuSelftest
  | ["subwordselftest"] => subwordSelftest
  | ["alugapselftest"] => aluGapSelftest
  | ["traceselftest"] => traceSelftest
  | ["opdiffhex", d] => writeOpDiffHex d
  | ["designexpect", f] => designExpectHexFile f
  | ["mmuidentityselftest"] => mmuIdentitySelftest
  | ["mmurelocselftest"] => mmuRelocSelftest
  | ["preempthex"]  => writePreemptHex "fpga/zc702/preempt.hex"
  | ["preemptpredict", q] => preemptPredict ((q.toNat?).getD 0)
  | ["progtest"]   => progtest
  | ["soc"]        =>
      Machines.Lnp64mini.Soc.soc.emit "rtl/lnp64mini_soc.v"
  | ["dual"]       =>
      Machines.Lnp64mini.DualSoc.dual.emit "rtl/lnp64mini_dual.v"
      Machines.Lnp64mini.DebugMap.emit
  | ["debugmap"]   => Machines.Lnp64mini.DebugMap.emit
  | _ => design.emit "rtl/lnp64mini.v"
