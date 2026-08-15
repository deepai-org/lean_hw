-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ExternalComponent

/-! # Contract-bearing external component regressions -/

namespace Tests.ExternalComponent

open Loom.Hw

private inductive CoreClock
private instance : ClockDomain CoreClock where name := "core"

private def inputPort : Port .input CoreClock (BitVec 8) :=
  Port.bits .input 8 "input"

private def outputPort : Port .output CoreClock (BitVec 8) :=
  Port.bits .output 8 "output"

private def interface : ComponentInterface :=
  ⟨[inputPort.decl, outputPort.decl]⟩

/-- A small total contract used to exercise the seam.  Real IP contracts may
be relational and nondeterministic; extensionality still prevents reads of
undeclared inputs from becoming hidden premises. -/
private def behavior : ComponentContract interface where
  State := Unit
  init := fun _ => True
  step := fun _ _ _ _ => True
  observe := fun _ _ _ _ => 0
  step_input_congr := by simp
  observe_input_congr := by
    intro _ _ _ _ port _
    rfl

private def specification : ExternalComponent where
  name := "neutral_leaf"
  version := "1"
  interface := interface
  behavior := behavior
  domains := [⟨"core", .rising, .synchronous true⟩]
  combinational := [⟨"output", "input"⟩]
  latency := [⟨"output", some "input", 0, some 0⟩]

private def binding : ExternalBinding specification where
  format := .verilog
  moduleName := "neutral_leaf_impl"
  parameters := [("WIDTH", "8")]
  artifact := Loom.Artifact.Identity.ofText "module neutral_leaf_impl; endmodule\n"
  evidence := .assumptionOnly
  assumptions :=
    [⟨"leaf_contract", "the bound module implements neutral_leaf contract v1"⟩]

#guard specification.validB
#guard binding.validB

private def reflexiveModel : RefinedExternalModel specification where
  implementation := behavior
  refinement := ComponentContract.Refinement.refl behavior

example : reflexiveModel.refinement.abstract () = () := rfl

private def badDependency : ExternalComponent :=
  { specification with combinational := [⟨"missing", "input"⟩] }

#guard !badDependency.validB

private def duplicateParameterBinding : ExternalBinding specification :=
  { binding with parameters := [("WIDTH", "8"), ("WIDTH", "16")] }

#guard !duplicateParameterBinding.validB

end Tests.ExternalComponent
