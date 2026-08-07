import Loom
import Machines.Lnp64mini.Core
import Machines.Lnp64mini.DualSoc
import Machines.Epoch.EpochSoc
import Machines.CapWalk.CapSoc
open Loom.Hw
def main : IO Unit := do
  for (nm, d) in [("lnp64mini (core)", Machines.Lnp64mini.design),
                  ("lnp64mini_dual", Machines.Lnp64mini.DualSoc.dual),
                  ("lnp64mini_epoch", Machines.Epoch.EpochSoc.epochSoc),
                  ("lnp64mini_cap", Machines.CapWalk.CapSoc.capSoc)] do
    let c := d.cost MemTarget.xc7
    IO.println s!"== {nm}"
    IO.println s!"  cost: state={c.stateBits} bitOps={c.bitOps} macroBits={c.macroBits} softBits={c.softBits} maxFanout={c.maxFanout}"
    IO.println (CostTarget.report xc7z020 c)
