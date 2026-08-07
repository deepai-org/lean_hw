import Loom
import Machines.Lnp64mini.Core
open Loom.Hw
def main : IO Unit := do
  let d := Machines.Lnp64mini.design
  for m in ["ic_data", "ic_tag"] do
    IO.println s!"{m}: syncReadOk={d.syncReadOkB m} writePorts={d.writePortCount m}"
  IO.println s!"realizable xc7      = {d.realizableOnB MemTarget.xc7}"
  IO.println s!"realizable asicSram = {d.realizableOnB MemTarget.asicSram}"
  let c := d.cost MemTarget.xc7
  IO.println s!"cost: bitOps={c.bitOps} macroBits={c.macroBits} softBits={c.softBits}"
  IO.println (CostTarget.report xc7z020 c)
