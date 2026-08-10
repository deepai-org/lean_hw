-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Substrate.S0Blinky
import Machines.Substrate.S0BscanRegs

/-!
# Substrate-0 typed-declaration migration regressions

These checks pin both first-light designs to their pre-migration interface
shape. Existing executable selftests cover S0Bscan behavior; the equalities
below make names, widths, reset values, memory images, input order, and output
selection kernel obligations.
-/

namespace Tests.S0Declarations

open Loom.Hw

namespace Blinky

open Machines.Substrate.S0Blinky

private def legacyDesign : Design where
  name := "s0blinky"
  regs := [⟨"cnt", 28, 0⟩]
  outputs := ["cnt"]
  mems := []
  rules := [⟨"tick", .write 28 "cnt" (.add (.reg 28 "cnt") (.lit 1))⟩]

theorem design_eq_legacy : design = legacyDesign := rfl

end Blinky

namespace Bscan

open Machines.Substrate.S0BscanRegs

private def legacyRegs : List RegDecl :=
  [⟨"scratch", 32, 0⟩, ⟨"led", 4, 0⟩, ⟨"con_idx", 5, 0⟩,
   ⟨"rd_reg", 32, 0⟩, ⟨"hb", 32, 0⟩]

private def legacyMems : List MemDecl :=
  [⟨"banner", 5, 8, bannerInit⟩, ⟨"bram", 3, 32, fun _ => 0⟩]

private def legacyInputs : List InputDecl :=
  [⟨"cmd_valid", 1⟩, ⟨"cmd_wr", 1⟩, ⟨"cmd_bram", 1⟩,
   ⟨"cmd_idx", 7⟩, ⟨"cmd_wdata", 32⟩]

theorem regs_eq_legacy : design.regs = legacyRegs := rfl
theorem mems_eq_legacy : design.mems = legacyMems := rfl
theorem inputs_eq_legacy : design.inputs = legacyInputs := rfl
theorem outputs_eq_legacy : design.outputs = legacyRegs.map (fun r => r.name) := rfl

end Bscan

end Tests.S0Declarations
