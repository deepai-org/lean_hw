-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom
import Evidence.Targets.Memory
import Evidence.Targets.Cost
import Machines.Lnp64mini.Core
open Loom.Hw
open Loom.Evidence.Targets
def main : IO Unit := do
  let d := Machines.Lnp64mini.design
  for m in ["ic_data", "ic_tag"] do
    IO.println s!"{m}: syncReadOk={d.syncReadOkB m} writePorts={d.writePortCount m}"
  IO.println s!"realizable xc7      = {d.realizableOnB Memory.xc7}"
  IO.println s!"realizable asicSram = {d.realizableOnB Memory.asicSram}"
  let c := d.cost Memory.xc7
  IO.println s!"cost: bitOps={c.bitOps} macroBits={c.macroBits} softBits={c.softBits}"
  IO.println (CostTarget.report Cost.xc7z020 c)
