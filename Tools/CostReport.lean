-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom
import Evidence.Targets.Memory
import Evidence.Targets.Cost
import Machines.Lnp64mini.Core
import Machines.Lnp64mini.DualSoc
import Machines.Epoch.EpochSoc
import Machines.CapWalk.CapSoc
open Loom.Hw
open Loom.Evidence.Targets
def main : IO Unit := do
  for (nm, d) in [("lnp64mini (core)", Machines.Lnp64mini.design),
                  ("lnp64mini_dual", Machines.Lnp64mini.DualSoc.dual),
                  ("lnp64mini_epoch", Machines.Epoch.EpochSoc.epochSoc),
                  ("lnp64mini_cap", Machines.CapWalk.CapSoc.capSoc)] do
    let c := d.cost Memory.xc7
    let ds := DagEval.stats d.elaborate
    IO.println s!"== {nm}"
    IO.println s!"  cost: state={c.stateBits} bitOps={c.bitOps} macroBits={c.macroBits} softBits={c.softBits} maxFanout={c.maxFanout}"
    IO.println s!"  evaluator DAG: {ds.render}"
    IO.println (CostTarget.report Cost.xc7z020 c)
