-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.ClockGauntlet
import Tools.ClockGauntletCampaign

/-! Executable Clock Gauntlet campaigns and fail-closed assembly fixtures. -/

namespace Tests.ClockGauntlet

open Loom.Hw
open Machines.Multiclock.ClockGauntlet

/-- The short exhaustive enumeration and every long seeded/adversarial
campaign pass through the runner proved equivalent to `System.runEventsFrom`. -/
example : Tools.ClockGauntletCampaign.evidenceResultJson.1 = true := by
  native_decide

example : certifiedArtifact.emissionCheck.isOk := by native_decide
example : certifiedArtifact.bindings.length = system.connections.length := by
  native_decide

private def missingSinkBuilder : SystemBuilder :=
  System.empty
    |>.island "source" source (clock := "source_clk")
    |>.connect sourceToTransform (source := "source") (sink := "absent")

/-- An unpaired endpoint never crosses the opaque checked-System boundary. -/
example : !(missingSinkBuilder.assemble.isOk) := by native_decide

private def rogueCrossDomainInput : Design :=
  { sourceBody with
    name := "rogue_cross_domain_input"
    inputs := [⟨"__loom_chan_undeclared_dst_valid", 1⟩] }

private def rogueCrossDomainBuilder : SystemBuilder :=
  System.empty
    |>.island "rogue" rogueCrossDomainInput (clock := "rogue_clk")

/-- A raw generated-looking cross-domain input outside a declared `Chan` is
rejected at checked-System assembly. -/
example : !(rogueCrossDomainBuilder.assemble.isOk) := by native_decide

/-- Physical release fails if any semantic crossing is absent or duplicated. -/
example : !(System.realize system []).isOk := by native_decide
example : !(System.realize system [firstBinding.toPhysical]).isOk := by native_decide
example : !(System.realize system
    [firstBinding.toPhysical, firstBinding.toPhysical]).isOk := by native_decide

private def unconstrainedFirst : System.BoundImplementation :=
  System.BoundImplementation.custom firstConnection "negative.no_constraints" .any
    firstBinding.refinement (fun _ => "negative_no_constraints")
    (fun _ => "module negative_no_constraints; endmodule") (fun _ => [])

/-- A distinct-clock binding without timing intent is rejected even when its
semantic refinement and ordered inventory key are otherwise valid. -/
example : !(System.realize system
    [unconstrainedFirst, secondBinding.toPhysical]).isOk := by native_decide

/-- The certified path's exact RTL value is the selected emitted RTL value. -/
example : certifiedArtifact.rtlArtifact.text.toUTF8 =
    certifiedArtifact.renderedUTF8 := certifiedArtifact.rtlArtifact_exact

private def variedOrderFairBlock : List NamedClockEvent :=
  [3, 4, 1, 6, 1, 6].map Execution.event

/-- The public bounded-completion premise accepts changing clock order and
coincident ticks, rather than only the fixed campaign schedule. -/
example : Execution.BoundedTickBlock variedOrderFairBlock := by
  simp [Execution.BoundedTickBlock, variedOrderFairBlock,
    Execution.eventMasks, Execution.protocolEventMask, Execution.event,
    Execution.FollowsRankGap, NamedClockEvent.fires, Execution.boolNat]

private theorem variedOrderFairBlock_bounded :
    Execution.BoundedTickBlock variedOrderFairBlock := by
  simp [Execution.BoundedTickBlock, variedOrderFairBlock,
    Execution.eventMasks, Execution.protocolEventMask, Execution.event,
    Execution.FollowsRankGap, NamedClockEvent.fires, Execution.boolNat]

/-- Regression instantiation of the universal 21,510-event completion theorem. -/
example (blocks : List (List NamedClockEvent))
    (count : blocks.length = 3585)
    (bounded : Execution.BoundedTickBlocks blocks) : Execution.protocolComplete
    (Execution.runProtocolBlocks Execution.protocolReset
      blocks) = true :=
  Execution.bounded_completion_blocks blocks count bounded

end Tests.ClockGauntlet
