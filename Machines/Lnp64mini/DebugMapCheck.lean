-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64mini.DebugMap
import Machines.Lnp64mini.Core

/-! Build-time integrity certificate for the external LNP64mini debug map.
Kept out of the runtime emitter so `native_decide` does not make regeneration
construct the full composed dual design during process initialization. -/

namespace Machines.Lnp64mini.DebugMap

/-- Lightweight source-level output surface. `DualSoc` prefixes these two
lists; the runtime `debugmap --check` independently requires every generated
port to occur in the current emitted dual RTL. -/
private def dualCoreOutputSurface : Loom.Hw.Design :=
  { name := "lnp64mini_dual_core_outputs"
    regs :=
      Machines.Lnp64mini.declarations.regs.map (fun reg =>
        { reg with name := "c0_" ++ reg.name }) ++
      Machines.Lnp64mini.declarations.regs.map (fun reg =>
        { reg with name := "c1_" ++ reg.name })
    mems := [], rules := [], «inputs» := []
    outputs :=
      Machines.Lnp64mini.declarations.outputs.map ("c0_" ++ ·) ++
      Machines.Lnp64mini.declarations.outputs.map ("c1_" ++ ·) }

set_option maxRecDepth 100000 in
theorem board_source_checked : board.okB dualCoreOutputSurface = true := by decide

end Machines.Lnp64mini.DebugMap
