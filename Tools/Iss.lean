import Machines.Lnp64u.Iss
import Machines.Acc8.Iss

/-!
# `lake exe iss` — boot the machines, print lockstep traces

First light (task 0.15): boots the Acc8 golden program and the LNP64-µ
demo manifest, prints each trace in the frozen `Loom.Trace` text format
plus a final-state summary. Image-from-file loading joins with the
conformance suite (task 1.9).
-/

open Machines Loom

def acc8Report : IO Unit := do
  IO.println "=== Acc8: golden program ==="
  let final := Acc8.goldenResult
  IO.println s!"halted={final.halted} acc={final.acc.toNat} mem[3]={(final.mem 3).toNat}"

def lnp64uReport : IO Unit := do
  IO.println "=== LNP64-µ: demo manifest ==="
  let (final, trace) := Lnp64u.demoResult
  for l in trace do
    IO.println l.print
  for d in List.finRange Lnp64u.numDomains do
    let ds := final.doms d
    IO.println s!"domain {d.val}: run={reprStr ds.run} cause={ds.cause.toNat} \
      r3={(ds.reg 3).toNat} r4={(ds.reg 4).toNat} pc={ds.pc.toNat}"
  IO.println s!"mem[data0]={(final.read (BitVec.ofNat 12 (Lnp64u.dataBase 0))).toNat}"

def main : IO Unit := do
  acc8Report
  lnp64uReport
