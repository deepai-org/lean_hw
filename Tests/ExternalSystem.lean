-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ExternalSystem

namespace Tests.ExternalSystem

open Loom.Hw

private inductive CoreClock
private instance : ClockDomain CoreClock where name := "core_clk"

private def referenceDesign : Design where
  name := "reference_leaf"
  regs := []
  mems := []
  inputs := []
  outputs := []
  rules := []

private def domainDesign : DomainDesign CoreClock :=
  DomainDesign.authored referenceDesign

private def owner : DomainIslandHandle CoreClock :=
  .named "leaf" domainDesign

private def builder : SystemBuilder :=
  System.empty.addDomainIsland owner

private def system : System := builder.certify (by decide)

private def referenceComponentValue : Component where
  name := "reference"
  interface := ⟨[]⟩
  design := referenceDesign

private def referenceComponent : DomainComponent CoreClock where
  implementation := domainDesign
  sealed :=
    { component := referenceComponentValue
      interfaceOk := by native_decide
      readsOk := by native_decide
      certified := CertifiedDesign.ofChecks (by native_decide) (by native_decide) }
  implementationEq := rfl
  domainOk := by native_decide

private def behavior : ComponentContract referenceComponent.sealed.component.interface where
  State := Unit
  init := fun _ => True
  step := fun _ _ _ _ => True
  observe := fun _ _ _ _ => 0
  step_input_congr := by intros; trivial
  observe_input_congr := by intros; trivial

private def specification : ExternalComponent where
  name := "reference_contract"
  version := "1"
  interface := referenceComponent.sealed.component.interface
  behavior := behavior
  domains := [⟨"core_clk", .rising, .synchronous true⟩]
  combinational := []
  latency := []

private def moduleText : String :=
  "module reference_leaf(input wire clk, input wire rst); endmodule\n"

private def binding : ExternalBinding specification where
  format := .verilog
  moduleName := "reference_leaf"
  parameters := []
  artifact := Loom.Artifact.Identity.ofText moduleText
  evidence := .assumptionOnly
  assumptions :=
    [⟨"rtl_contract", "the exact external bytes implement reference_contract v1"⟩]

private def external : DomainExternal CoreClock where
  sealed :=
    { specification := specification
      specificationValid := by native_decide
      binding := binding
      bindingValid := by native_decide }
  domainOk := by native_decide

private def witness : BoundComponentGraph.DesignContractWitness
    referenceComponent specification where
  interfaceEq := rfl
  abstract := fun _ => ()
  init := trivial
  tick := by intros; trivial
  reset := by intros; trivial
  hold := by intros; trivial
  observe := by
    intro input state port member
    simp [specification, referenceComponent, referenceComponentValue,
      ComponentInterface.outputs] at member

private theorem ownerFound : system.findIsland? owner.name = some owner.toSystemIsland := by
  rfl

private theorem ownerDesignEq :
    owner.design.design = referenceComponent.implementation.design := by
  rfl

private def substitution : ExternalIslandSubstitution system :=
  (ExternalIslandSubstitution.check? owner referenceComponent external witness
    ownerFound ownerDesignEq).toOption.get (by native_decide)

private def base : System.Application system :=
  system.realizePortable (by native_decide)

private def application : ExternalApplication system :=
  (ExternalApplication.check? base [substitution]).toOption.get (by native_decide)

example : application.emissionCheck.isOk := by native_decide

private def emittedReferenceSubstitution : ExternalIslandSubstitution system :=
  (ExternalIslandSubstitution.checkEmittedReference? owner.name
    referenceComponent external witness).toOption.get (by native_decide)

example : emittedReferenceSubstitution.artifact.bytes = binding.artifact.bytes := by
  native_decide

example : application.externalArtifacts.map (·.bytes) == [binding.artifact.bytes] := by
  native_decide

example : application.renderedVerilog.contains "module reference_leaf" := by native_decide

example : application.report.contains "rtl_contract" := by native_decide

example : application.emissionArtifacts.map (·.relativePath.toString) =
    ["system.v", "clock_constraints.md", "crossings.md", "external_islands.md"] := by
  native_decide

private def duplicateRejected : Bool :=
  match ExternalApplication.check? base [substitution, substitution] with
  | .error _ => true
  | .ok _ => false

example : duplicateRejected := by native_decide

private def wrongNameBinding : ExternalBinding specification :=
  { binding with moduleName := "wrong_name" }

private def wrongNameExternal : DomainExternal CoreClock where
  sealed :=
    { specification := specification
      specificationValid := by native_decide
      binding := wrongNameBinding
      bindingValid := by native_decide }
  domainOk := by native_decide

private def wrongNameRejected : Bool :=
  match ExternalIslandSubstitution.check? owner referenceComponent wrongNameExternal
      witness ownerFound ownerDesignEq with
  | .error _ => true
  | .ok _ => false

example : wrongNameRejected := by native_decide

private def changedReferenceDesign : Design :=
  { referenceDesign with
    regs := [⟨"changed", 1, 0⟩]
    outputs := ["changed"] }

private def changedOwner : DomainIslandHandle CoreClock :=
  .named "leaf" (DomainDesign.authored changedReferenceDesign)

private def changedSystem : System :=
  System.empty.addDomainIsland changedOwner |>.certify (by decide)

private def changedReferenceRejected : Bool :=
  match ExternalIslandSubstitution.checkEmittedReference?
      (system := changedSystem) owner.name referenceComponent external witness with
  | .error _ => true
  | .ok _ => false

example : changedReferenceRejected := by native_decide

end Tests.ExternalSystem
