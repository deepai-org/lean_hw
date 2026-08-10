-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Substrate.S13Soak

/-!
# Generated-family declaration migration regression

S13Soak is the first existing `Fin`-generated register design migrated to
`RegArray`. This pins the derived register and output lists to the previous
shape; its full-depth ISS lockstep and checked RTL artifact cover behavior.
-/

namespace Tests.S13Declarations

open Loom.Hw
open Machines.Substrate.S13Soak

private def legacyRegs : List RegDecl :=
  [⟨"cyc", 32, 0⟩, ⟨"lfsr", 16, BitVec.ofNat 16 LFSR_INIT⟩, ⟨"ptr", 3, 0⟩,
   ⟨"tmr", 16, 0⟩, ⟨"dma_busy", 1, 0⟩, ⟨"dma_cd", 4, 0⟩,
   ⟨"injected", 32, 0⟩, ⟨"serviced", 32, 0⟩, ⟨"err", 32, 0⟩,
   ⟨"maxout", 32, 0⟩, ⟨"dma_sub", 32, 0⟩, ⟨"dma_comp", 32, 0⟩,
   ⟨"tmr_exp", 32, 0⟩]
  ++ (List.finRange 8).map (fun i => ⟨s!"pend{i.val}", 1, 0⟩)
  ++ (List.finRange 8).map (fun i => ⟨s!"age{i.val}", 11, 0⟩)

theorem regs_eq_legacy : s13Regs = legacyRegs := rfl

theorem outputs_eq_legacy : design.outputs = legacyRegs.map (·.name) := by
  rw [← regs_eq_legacy]
  rfl

end Tests.S13Declarations
