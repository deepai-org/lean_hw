import Machines.Acc8.Core
import Loom.Hw.Compile
import Loom.Emit.MicroVerilog.Axiom

/-!
# A-EV — the emitted µVerilog denotes the Acc8 core (task 2.4, pathfinder)

The emission theorem instantiated for Acc8: the compiled µVerilog module's
transition system equals the EDSL core's, under the state conversion. With
the round-trip theorem (task 2.3) and the µVerilog-semantics axiom, this
chains Acc8's spec → core (A-R) → µVerilog text. LNP64-µ's E-V is the same
statement at scale.
-/

namespace Machines.Acc8.Theorems.AEV

open Loom Loom.Hw Loom.Emit.MicroVerilog Machines.Acc8

/-- State conversion: EDSL design state ↔ µVerilog module state (both are
name-indexed register/memory valuations, so this is the identity on the
underlying maps). -/
def conv (σ : Loom.Hw.St) : Loom.Emit.MicroVerilog.St :=
  { regs := σ.regs, mems := σ.mems }

/-- **A-EV (cycle).** One µVerilog cycle equals one compiled-design cycle
under `conv`: the register mux-tree fold and the memory write-port fold the
compiler builds evaluate to the design's rule fold. -/
theorem cycle_agree (prog : BitVec 8 → BitVec 16) (σ : Loom.Hw.St) :
    (Compile.compile (Core.design prog)).cycle (conv σ)
      = conv ((Core.design prog).cycle σ) := by
  sorry

/-- **A-EV.** The emitted module's transition system equals the core's. -/
theorem emission_correct (prog : BitVec 8 → BitVec 16) :
    Nonempty (Simulation (Core.design prog).toTSys
                (Compile.compile (Core.design prog)).toTSys) := by
  sorry

end Machines.Acc8.Theorems.AEV
