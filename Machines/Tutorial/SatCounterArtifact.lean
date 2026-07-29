-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ToProgramDenotes
import Machines.Tutorial.SatCounter

/-!
# The tutorial design's symbolic denotation — no pipeline required

`toProgram_denotes` (proved 2026-07-29) makes the full `ModuleBehavior`
statement — every wire, register, and output of the emitted SSA witness
denotes the verified compilation — a corollary of four kernel-reducible
Booleans. For a tutorial-scale design each discharges by `decide` in
seconds; the per-node certificate pipeline the processor releases use is
not involved at all. This is the intended artifact path for new small
designs.

The heartbeat bump covers the `designReadsOkB` conjunct, which reduces
`design.toProgram` (flatten + CSE hash table) inside the kernel; the
whole file checks in ~18 s.
-/

namespace Machines.Tutorial.SatCounter

open Loom.Release.SSA

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- The end-to-end symbolic denotation of the saturating counter:
its constructed release witness denotes the verified compiler's output
at every node. Four `decide`s, no generated certificates. -/
theorem satcounter_denotes :
    Loom.Release.Symbolic.ModuleBehavior design design.toProgram
      design.indexedsOf design.tableOf design.registersOf design.memoriesOf
      design.outputsOf :=
  toProgram_denotes design (by decide) (by decide) (by decide) (by decide)

end Machines.Tutorial.SatCounter
