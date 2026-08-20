-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.HierarchyEmit

/-! # Hierarchy-preserving emission regressions -/

namespace Tests.HierarchyEmit

open Loom.Hw
open Loom.Hw.Backend

private def basePlan : Plan Unit Unit where
  topName := "hierarchy_fixture"
  instances :=
    [{ path := "u_first", moduleName := "stage", parameters := [], external := false,
       ports :=
         [⟨"d", "a", .input, 8⟩,
          ⟨"q", "mid", .output, 8⟩] },
     { path := "u_second", moduleName := "stage", parameters := [], external := false,
       ports :=
         [⟨"d", "mid", .input, 8⟩,
          ⟨"q", "y", .output, 8⟩] }]
  modules := [⟨"stage", "module stage(input clk, input rst); endmodule\n"⟩]
  externalArtifacts := []
  assumptions := []

private def plan : HierarchyEmissionPlan Unit Unit where
  design := basePlan
  topPorts :=
    [⟨"clk_i", "clk_i", .input, 1⟩,
     ⟨"rst_i", "rst_i", .input, 1⟩,
     ⟨"input_byte", "a", .input, 8⟩,
     ⟨"output_byte", "y", .output, 8⟩]
  clockReset :=
    [⟨"u_first", "clk_i", "rst_i"⟩,
     ⟨"u_second", "clk_i", "rst_i"⟩]

#guard plan.validB
#guard plan.renderTop?.toOption.any fun text =>
  text.contains "stage u_first" && text.contains "stage u_second" &&
  text.contains ".q(mid)" && text.contains "assign a = input_byte;" &&
  text.contains "assign output_byte = y;"

private def multiplyDriven : HierarchyEmissionPlan Unit Unit :=
  { plan with topPorts := plan.topPorts ++ [⟨"bad_driver", "mid", .input, 8⟩] }

#guard !multiplyDriven.validB
#guard match multiplyDriven.renderTop? with
  | .error _ => true
  | .ok _ => false

private def mismatchedInstances :=
  basePlan.instances.map fun inst =>
    if inst.path == "u_second" then
      { inst with ports := [⟨"d", "mid", .input, 16⟩, ⟨"q", "y", .output, 8⟩] }
    else inst

private def widthMismatch : HierarchyEmissionPlan Unit Unit :=
  { plan with
    design := { basePlan with instances := mismatchedInstances } }

#guard !widthMismatch.validB

end Tests.HierarchyEmit
