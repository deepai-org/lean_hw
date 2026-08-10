-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64mini.Harness
import Loom.Hw.DagEval

/-!
# LNP64mini simulator benchmark

Measures the generated, proved `FastEval` simulator against the hand-written
cycle ISS on the same precomputed input trace.  Elaboration and DDR/GP model
work are outside the timed regions, so this is an apples-to-apples core-cycle
comparison rather than a comparison of two different harnesses.

```console
lake exe lnpsimbench          # 10,000 cycles
lake exe lnpsimbench 1000     # shorter profiling run
```
-/

namespace Tools.Lnp64miniSimBench

open Loom.Hw
open Machines.Lnp64mini

/-- Produce a realistic canonical input trace by running the existing system
model over the broad `progLS` directed program.  The start command is asserted
on cycle zero; after the program exits, the trace remains a valid idle-system
workload. -/
def inputTrace (n : Nat) : Array MiniIn := Id.run do
  let image := imageFrom TEXT_BASE progLS
  let mut s : MiniSt := {}
  let mut d : DdrModel := { mem := Std.HashMap.ofList image, latency := 1 }
  let mut g : GpModel := {}
  let mut trace := Array.mkEmpty n
  for k in List.range n do
    let cmd : MiniIn :=
      if k = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}
    let (s', d', g', inp) := sysStep s d g cmd 0
    trace := trace.push inp
    s := s'; d := d'; g := g'
  return trace

def runGenerated (trace : Array MiniIn) : FastSt :=
  -- Hoist elaboration out of the cycle loop.  Calling `simulator.cycleOpen`
  -- directly would unfold `simulator.fast` at every iteration because Lean
  -- definitions are functions, not memoized global values.
  let fd := simulator.fast
  trace.foldl (fun fs inp => fastCycleOpen fd inp.toEnv fs) simulator.reset

def runHand (trace : Array MiniIn) : MiniSt :=
  trace.foldl (fun s inp => MiniIss.step s inp) ({} : MiniSt)

def runDag {fd : FastDesign} (d : DagEval.Verified fd)
    (trace : Array MiniIn) : FastSt :=
  trace.foldl (fun fs inp => d.cycleOpen inp.toEnv fs)
    simulator.reset

def generatedChecksum (fs : FastSt) : Nat :=
  let fd := simulator.fast
  (fd.peek fs "pc").getD 0 + (fd.peek fs "retire").getD 0 +
    (fd.peek fs "running").getD 0 + (fd.peek fs "halted").getD 0

def handChecksum (s : MiniSt) : Nat :=
  s.pc.toNat + s.retire.toNat + (if s.running then 1 else 0) +
    (if s.halted then 1 else 0)

def parseCycles : List String → Nat
  | [s] => s.toNat?.getD 10000
  | _ => 10000

def benchmark (args : List String) : IO Unit := do
  let n := parseCycles args
  IO.eprintln s!"precomputing {n}-cycle canonical LNP64mini input trace"
  let trace := inputTrace n
  IO.eprintln "input trace ready; elaborating generated design"
  -- Force the elaborated design before starting either timer.
  let fd := simulator.fast
  IO.eprintln s!"elaborated: {fd.acts.size} rules, {fd.nregs} register/input slots, {fd.memTotal} memory cells"
  let tp0 ← IO.monoMsNow
  let dag ← match DagEval.prepare? fd with
    | some dag => pure dag
    | none => throw <| IO.userError "generated DAG failed its semantic certificate"
  let nodeCount := dag.design.nodes.size
  let tp1 ← IO.monoMsNow
  IO.eprintln s!"certified DAG: {nodeCount} unique expression nodes"
  IO.eprintln s!"DAG structure: {(DagEval.statsOf fd dag.design).render}"
  IO.eprintln s!"DAG lowering + independent certificate: {tp1 - tp0} ms"

  let t0 ← IO.monoMsNow
  let hs := runHand trace
  let hc := handChecksum hs
  -- `IO.println` forces the checksum before the timestamp; otherwise Lean's
  -- pure values may remain suspended until the final report.
  IO.eprintln s!"hand ISS checksum {hc}"
  let t1 ← IO.monoMsNow
  IO.eprintln s!"hand ISS timing complete ({t1 - t0} ms); running generated simulator"
  let fs := runGenerated trace
  let gc := generatedChecksum fs
  IO.eprintln s!"generated simulator checksum {gc}"
  let t2 ← IO.monoMsNow
  IO.eprintln "running certified eager DAG evaluator"
  let dfs := runDag dag trace
  let dc := generatedChecksum dfs
  IO.eprintln s!"certified DAG checksum {dc}"
  let t3 ← IO.monoMsNow
  IO.println s!"hand ISS:             {n} cycles in {t1 - t0} ms (checksum {hc})"
  IO.println s!"generated proved sim: {n} cycles in {t2 - t1} ms (checksum {gc})"
  IO.println s!"certified DAG sim:    {n} cycles in {t3 - t2} ms (checksum {dc})"
  if hc != gc || hc != dc then
    throw <| IO.userError s!"final architectural checksum mismatch: hand={hc}, generated={gc}, dag={dc}"

end Tools.Lnp64miniSimBench

def main (args : List String) : IO Unit :=
  Tools.Lnp64miniSimBench.benchmark args
