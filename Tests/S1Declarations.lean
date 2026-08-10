-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Substrate.S1Counters
import Machines.Substrate.RetimeDemo

/-!
# Substrate typed-declaration regressions

Pins the typed lowering for the larger S1 generated-family example and the
baseline consumed by the verified retiming demo.
-/

namespace Tests.S1Declarations

open Loom.Hw

namespace Counters

open Machines.Substrate.S1Counters

private def legacyRegs : List RegDecl :=
  [⟨"cyc", 16, 0⟩, ⟨"lfsr", 16, BitVec.ofNat 16 LFSR_INIT⟩,
   ⟨"total", 16, 0⟩, ⟨"any_max", 1, 0⟩, ⟨"sel", 3, 0⟩,
   ⟨"sink", 12, 0⟩, ⟨"hits", 16, 0⟩] ++
  (List.finRange 8).map (fun i => ⟨s!"bank{i.val}", 12, 0⟩)

theorem regs_eq_legacy : design.regs = legacyRegs := rfl
theorem outputs_eq_legacy : design.outputs = legacyRegs.map (fun r => r.name) := rfl

end Counters

namespace Retime

open Machines.Substrate.RetimeDemo

private def legacyBaseline : Design where
  name := "retime_base"
  regs := [⟨"cnt", 8, 0⟩, ⟨"obs", 8, 7⟩]
  outputs := ["cnt", "obs"]
  mems := []
  rules :=
    [ ⟨"tick", .write 8 "cnt" (.add (.reg 8 "cnt") (.lit 1))⟩
    , ⟨"latch", .write 8 "obs" (.add (.reg 8 "cnt") (.lit 7))⟩ ]

theorem baseline_eq_legacy : baseline = legacyBaseline := rfl

end Retime

end Tests.S1Declarations
