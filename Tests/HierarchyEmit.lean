-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.HierarchyEmit
import Loom.Hw.Stateless

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

private inductive FixtureDomain : Type where
  | marker

private instance : ClockDomain FixtureDomain where
  name := "fixture_domain"

private def statelessDesign : Design where
  name := "comb_stage"
  regs := []
  mems := []
  rules := []
  inputs := [⟨"d", 8⟩]
  outputs := []
  combOutputs := [⟨"q", 8, .not (.reg 8 "d")⟩]

private def statelessComponent :
    Except String (DomainComponent FixtureDomain) := do
  let implementation ← StatelessDesign.check? statelessDesign
  ({ name := "comb_stage"
     ports :=
       [⟨"d", .input, 8, "byte"⟩,
        ⟨"q", .output, 8, "byte"⟩]
     implementation } : StatelessComponent).bind? (δ := FixtureDomain)

private def statelessGraph : Except String (BoundComponentGraph FixtureDomain) :=
  match statelessComponent with
  | .error message => .error message
  | .ok component =>
      (BoundComponentGraph.empty (δ := FixtureDomain) "comb_top").addInternal
        ⟨"u_comb", component⟩

private def statelessHierarchyPlan :
    Except String (HierarchyEmissionPlan Loom.Artifact.Identity NamedAssumption) :=
  match statelessGraph with
  | .error message => .error message
  | .ok graph => .ok <|
      BoundComponentGraph.hierarchyEmissionPlan graph "unused_clk" "unused_rst"

#guard statelessHierarchyPlan.toOption.any fun plan =>
  plan.clockReset.isEmpty &&
    plan.topPorts.all (fun port => port.port != "unused_clk" && port.port != "unused_rst") &&
    plan.design.modules.all (fun artifact =>
      !artifact.text.contains "always" && !artifact.text.contains "input wire clk") &&
    plan.renderTop?.toOption.any (fun text =>
      !text.contains "unused_clk" && !text.contains "unused_rst")

end Tests.HierarchyEmit
