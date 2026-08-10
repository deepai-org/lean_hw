-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Evidence.Targets.Memory
import Machines.Acc8.Core
import Machines.Acc8.Iss
import Machines.Lnp64u.Hw.Core
import Machines.Lnp64u.Hw.Demo
import Machines.Lnp64mini.Core
import Machines.Lnp64mini.Soc
import Machines.Lnp64mini.DualSoc
import Machines.Epoch.Engine
import Machines.Epoch.EpochSoc
import Machines.CapWalk.Engine
import Machines.CapWalk.CapSoc
import Machines.Substrate.S0Blinky
import Machines.Substrate.S0BscanRegs
import Machines.Substrate.S13Soak
import Machines.Substrate.S1Counters
import Machines.Substrate.RetimeDemo

/-!
# `lake exe memtargets` — the portability table (D38)

For every shipped design, which declared memory technologies
(`Evidence/Targets/Memory.lean`) can realize its memories. This is the point of
D38: a design realizable only on `xc7` is *visibly* target-specific rather
than silently so (`Loom/Hw/MEMTARGET_SPEC.md`).

```console
lake exe memtargets          # the table
lake exe memtargets -v       # plus a line per memory per target
```

`realizableOnB` reads the *design*, so an `ackMemInit` recorded at an
emission site rather than on the design (as `epochengine_tiny`'s is, in
`Machines/Epoch/Emit.lean`) does not show here: the table reports the
property; `Design.checkTarget` and `Design.emitFor` enforce the policy.

`pingpong` and `satcounter` are omitted: both declare `mems := []`, so they
are realizable on every target, and their modules each define a root `main`
and therefore cannot be imported together with anything else.
-/

open Loom.Hw
open Loom.Evidence.Targets

/-- The shipped designs, by the name of the `rtl/*.v` they emit. -/
def shipped : List (String × Design) :=
  [ ("acc8", Machines.Acc8.Core.design
      (Machines.Acc8.loadProg Machines.Acc8.golden)),
    ("lnp64u", Machines.Lnp64u.Hw.core Machines.Lnp64u.Demo.sysManifest),
    ("s0blinky", Machines.Substrate.S0Blinky.design),
    ("s0bscan", Machines.Substrate.S0BscanRegs.design),
    ("s13soak", Machines.Substrate.S13Soak.design),
    ("s1counters", Machines.Substrate.S1Counters.design),
    ("retime_base", Machines.Substrate.RetimeDemo.baseline),
    ("retime_retimed", Machines.Substrate.RetimeDemo.retimed),
    ("lnp64mini", Machines.Lnp64mini.design),
    ("lnp64mini_soc", Machines.Lnp64mini.Soc.soc),
    ("lnp64mini_dual", Machines.Lnp64mini.DualSoc.dual),
    ("epochengine", Machines.Epoch.Engine.design),
    ("epochengine_tiny", Machines.Epoch.Engine.tiny),
    ("lnp64mini_epoch", Machines.Epoch.EpochSoc.epochSoc),
    ("capwalk", Machines.CapWalk.Engine.design),
    ("lnp64mini_cap", Machines.CapWalk.CapSoc.capSoc) ]

def pad (s : String) (n : Nat) : String :=
  s ++ String.ofList (List.replicate (n - s.length) ' ')

def main (args : List String) : IO Unit := do
  let verbose := args.contains "-v"
  IO.println "design            mems  xc7   ecp5  asic   offenders"
  for (n, d) in shipped do
    let verdict := Memory.all.map fun t =>
      (t, d.realizableOnB t, (d.unrealizableOn t).map (·.name))
    let cells := String.join <| verdict.map fun (_, ok, _) =>
      pad (if ok then "yes" else "NO") 6
    let bad := (verdict.filter (fun (_, ok, _) => !ok)).map fun (t, _, ms) =>
      s!"{t.name}:{ms}" ++ (if d.realizableAckOkB t then " (ACK)" else "")
    IO.println <| pad n 18 ++ pad (toString d.mems.length) 6 ++ cells ++
      " " ++ String.intercalate " " bad
    if verbose then
      for t in Memory.all do
        for md in d.mems do
          IO.println (d.realizableReport t md)
  IO.println "\n(pingpong and satcounter declare no memories: realizable on \
every target.)"
