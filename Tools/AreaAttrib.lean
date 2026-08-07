-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom
import Machines.Lnp64mini.Core
open Loom.Hw

/-!
# Where the area goes

`lake exe areaattrib`

The epoch top routed at 55% SLICE_LUTX with only 16% SLICE_FFX -- a 3.3:1
combinational-to-sequential ratio, which says the area is in logic cones, not
in state. The question "which cones" is not answerable from a placed netlist
(`-flatten` throws the hierarchy away and the emitted design is one module
anyway), but it *is* answerable from the source: `Act.cost` is the
hash-consed node weight of a rule body, so summing per rule attributes the
design's `bitOps` back to the rule that built it.

Two caveats, both from `Cost.lean`'s own honesty boundary. Sharing across
rules is not modelled, so these are upper bounds that sum to the design's
`bitOps` by construction. And node weight is not LUTs -- yosys's mux-cone
optimisation is exactly the thing the model does not claim to predict. Use
this to rank, not to size.
-/

def main : IO Unit := do
  let d := Machines.Lnp64mini.design
  let total := d.rules.foldl (fun acc r => acc + r.body.cost) 0
  let rows := d.rules.map (fun r => (r.name, r.body.cost))
  let sorted := rows.toArray.qsort (fun a b => a.2 > b.2) |>.toList
  IO.println s!"lnp64mini: {d.rules.length} rules, total bitOps {total}"
  IO.println "  (hash-consed node weight per rule; upper bounds, for ranking)"
  IO.println ""
  let mut run := 0
  for (nm, c) in sorted do
    run := run + c
    let pct := if total == 0 then 0 else c * 1000 / total
    let cum := if total == 0 then 0 else run * 1000 / total
    IO.println s!"  {c}\t{pct / 10}.{pct % 10}%\tcum {cum / 10}.{cum % 10}%\t{nm}"
  IO.println ""
  -- Break the biggest rules down their `.seq` spine. A rule body is a chain
  -- of guarded writes, and the chain element is the unit a person can act on
  -- ("this command", "this funnel entry") where the rule total is not.
  for target in ["cmd", "fsm", "rf_funnel", "smp"] do
    match d.rules.find? (fun r => r.name == target) with
    | none => pure ()
    | some r =>
      let rec spine (a : Act) : List Act :=
        match a with
        | .seq x y => spine x ++ spine y
        | other => [other]
      let parts := (spine r.body).map (fun a => a.cost)
      let sorted := parts.toArray.qsort (fun a b => a > b) |>.toList
      let tot := parts.foldl (·+·) 0
      IO.println s!"  {target}: {parts.length} chain elements, total {tot}"
      IO.println s!"    top 12: {(sorted.take 12)}"
  IO.println ""
  IO.println s!"state: {d.regs.length} registers, {d.mems.length} memories"
  let regBits := d.regs.foldl (fun acc r => acc + r.width) 0
  IO.println s!"  register bits: {regBits}"
  for m in d.mems do
    IO.println s!"  mem {m.name}: {2 ^ m.addrWidth} x {m.dataWidth} = {m.dataWidth * 2 ^ m.addrWidth} bits"
