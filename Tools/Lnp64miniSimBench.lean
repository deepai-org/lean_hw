-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64mini.Harness
import Loom.Hw.DagEval

/-!
# LNP64mini simulator benchmark

Measures the generated, proved `FastEval` simulator against the certified DAG
evaluator on the same precomputed input trace. Elaboration and DDR/GP model
work are outside the timed regions.

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
def inputTrace (view : DerivedView) (dag : DagEval.VerifiedSimulator design)
    (n : Nat) : Array MiniIn := Id.run do
  let image := imageFrom TEXT_BASE progLS
  let mut system := DerivedSystem.reset dag image 1
  let mut trace := Array.mkEmpty n
  for k in List.range n do
    let cmd : MiniIn :=
      if k = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}
    let (next, inp) := system.step view dag cmd 0
    trace := trace.push inp
    system := next
  return trace

def runGenerated (trace : Array MiniIn) : FastSt :=
  -- Hoist elaboration out of the cycle loop.  Calling `simulator.cycleOpen`
  -- directly would unfold `simulator.fast` at every iteration because Lean
  -- definitions are functions, not memoized global values.
  let fd := simulator.fast
  trace.foldl (fun fs inp => fastCycleOpen fd inp.toEnv fs) simulator.reset

def runDag {fd : FastDesign} (d : DagEval.Verified fd)
    (trace : Array MiniIn) : FastSt :=
  trace.foldl (fun fs inp => d.cycleOpen inp.toEnv fs)
    simulator.reset

def generatedChecksum (fs : FastSt) : Nat :=
  let fd := simulator.fast
  (fd.peek fs "pc").getD 0 + (fd.peek fs "retire").getD 0 +
    (fd.peek fs "running").getD 0 + (fd.peek fs "halted").getD 0

def parseCycles : List String → Nat
  | [s] => s.toNat?.getD 10000
  | _ => 10000

def benchmark (args : List String) : IO Unit := do
  let n := parseCycles args
  IO.eprintln "elaborating generated design"
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
  let view ← prepareDerivedView
  IO.eprintln s!"precomputing {n}-cycle canonical LNP64mini input trace"
  let trace := inputTrace view ⟨simulator, dag⟩ n
  IO.eprintln "input trace ready"

  let t0 ← IO.monoMsNow
  let fs := runGenerated trace
  let gc := generatedChecksum fs
  IO.eprintln s!"generated simulator checksum {gc}"
  let t1 ← IO.monoMsNow
  IO.eprintln "running certified eager DAG evaluator"
  let dfs := runDag dag trace
  let dc := generatedChecksum dfs
  IO.eprintln s!"certified DAG checksum {dc}"
  let t2 ← IO.monoMsNow
  IO.println s!"generated proved sim: {n} cycles in {t1 - t0} ms (checksum {gc})"
  IO.println s!"certified DAG sim:    {n} cycles in {t2 - t1} ms (checksum {dc})"
  if gc != dc then
    throw <| IO.userError s!"final architectural checksum mismatch: generated={gc}, dag={dc}"

end Tools.Lnp64miniSimBench

def main (args : List String) : IO Unit :=
  Tools.Lnp64miniSimBench.benchmark args
