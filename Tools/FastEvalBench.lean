-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.FastEval
import Machines.Substrate.S13Soak
import Machines.Substrate.S0BscanRegs
import Machines.Substrate.S0Blinky
import Machines.Substrate.S1Counters

/-!
# FastEval benchmark / oracle runner (compiled)

```console
lake exe fastbench            # S13Soak full-K fast run, timed
lake exe fastbench lockstep   # fastCycle vs Design.cycle, all substrate designs
```
-/

open Loom.Hw Machines.Substrate

def benchScale : IO Unit := do
  let d := S13Soak.design
  let fd := d.elaborate
  for n in [10000, 100000, 1000000] do
    let t0 ← IO.monoMsNow
    let fs := fastRun fd n d.fastReset
    let v := fs.regs.getD 1 0
    let t1 ← IO.monoMsNow
    IO.println s!"{n} fastCycles -> lfsr={v} in {t1 - t0} ms"

def benchSoak : IO Unit := do
  let d := S13Soak.design
  let fd := d.elaborate
  let n := S13Soak.K + 8
  let fs := fastRun fd n d.fastReset
  IO.println s!"s13soak: {n} fastCycles (see `fastbench scale` for timing)"
  for (nm, v) in d.fastRegs fs do IO.println s!"{nm}={v}"

def benchLockstep : IO Unit := do
  let mut ok := true
  ok := (← S0Blinky.design.lockstep 300) && ok
  ok := (← S13Soak.design.lockstep 300) && ok
  ok := (← S0BscanRegs.design.lockstep 60 (randomInEnv 7)) && ok
  ok := (← S1Counters.design.lockstep 300) && ok
  IO.println (if ok then "FASTEVAL LOCKSTEP OK (blinky 300, soak 300, bscan 60 random, s1counters 300)"
              else "FASTEVAL LOCKSTEP FAILED")

def main (args : List String) : IO Unit := do
  match args with
  | ["lockstep"] => benchLockstep
  | ["scale"] => benchScale
  | _ => benchSoak
