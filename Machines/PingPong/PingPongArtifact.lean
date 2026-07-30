import Loom.Release.ToProgramDenotes
import Machines.PingPong.PingPong

/-!
# PingPong's symbolic denotation

Per TUTORIAL.md §6 (optional step): the emitted SSA witness denotes the
verified compilation at every wire, register, and output — one application
of `toProgram_denotes` plus four `by decide` facts.
-/

namespace Machines.PingPong

open Loom.Release.SSA

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

theorem pingpong_denotes :
    Loom.Release.Symbolic.ModuleBehavior design design.toProgram
      design.indexedsOf design.tableOf design.registersOf design.memoriesOf
      design.outputsOf :=
  toProgram_denotes design (by decide) (by decide) (by decide) (by decide)

end Machines.PingPong
