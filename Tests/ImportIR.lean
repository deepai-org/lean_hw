-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ImportIR
import Loom.Hw.Compile
import Loom.Emit.MicroVerilog.Print

/-! # Neutral import IR and explicit-edge regressions -/

namespace Tests.ImportIR

open Loom.Hw
open Loom.Hw.ImportIR

private def location : SourceLocation :=
  ⟨"fixture/simple.sv", 1, 1, 12, 10⟩

private def domain (edge : Loom.ClockEdge) (resetKind : ResetKind) :
    ImportIR.ClockDomain :=
  { name := "core", clockPort := "clock_i", edge := edge,
    reset := { kind := resetKind, port := some "reset_ni",
               activeHigh := false, source := some location },
    source := location }

private def simple (edge : Loom.ClockEdge := .rising) : ImportIR.Module where
  name := "imported_simple"
  source := location
  ports :=
    [⟨"clock_i", .input, 1, "clock", location⟩,
     ⟨"reset_ni", .input, 1, "reset", location⟩,
     ⟨"d", .input, 8, "byte", location⟩,
     ⟨"q", .output, 8, "byte", location⟩]
  domains := [domain edge .synchronous]
  registers :=
    [⟨"state", 8, 0, .signal 8 "d" location, location⟩]
  memories := []
  outputs :=
    [⟨"q", 8, .signal 8 "state" location, location⟩]

#guard match simple.lowerLocalDesign? with
  | .ok lowered => lowered.design.inputs.map (·.name) == ["d"]
  | .error _ => false

#guard match simple.lowerComponent? with
  | .ok lowered => lowered.component.interface.ports.map (·.name) == ["d", "q"]
  | .error _ => false

private def fallingText : Except String String := do
  let lowered ← (simple .falling).lowerLocalDesign?
  pure <| Loom.Emit.MicroVerilog.Print.print
    (Compile.compileForClockReset lowered.design lowered.edge
      lowered.clockPort "reset_ni" false)

#guard fallingText.toOption.any fun text =>
  text.contains "always @(negedge clock_i)" && text.contains "if (!reset_ni)"

private def risingText : Except String String := do
  let lowered ← simple.lowerLocalDesign?
  pure <| Loom.Emit.MicroVerilog.Print.print
    (Compile.compileForClockReset lowered.design lowered.edge
      lowered.clockPort "reset_ni" false)

#guard risingText.toOption.any (·.contains "always @(posedge clock_i)")

private def asyncModule : ImportIR.Module :=
  { simple with
    domains := [domain .rising .asynchronousAssertSynchronousRelease] }

#guard match asyncModule.lowerLocalDesign? with
  | .error _ => true
  | .ok _ => false

private def fullyAsyncModule : ImportIR.Module :=
  { simple with domains := [domain .rising .asynchronous] }

#guard match fullyAsyncModule.lowerLocalDesign? with
  | .error _ => true
  | .ok _ => false

private def statelessModule : ImportIR.Module where
  name := "imported_stateless"
  source := location
  ports :=
    [⟨"a", .input, 8, "byte", location⟩,
     ⟨"b", .input, 8, "byte", location⟩,
     ⟨"q", .output, 8, "byte", location⟩]
  domains := []
  registers := []
  memories := []
  outputs :=
    [⟨"q", 8,
      .binary 8 .bitXor (.signal 8 "a" location)
        (.signal 8 "b" location) location,
      location⟩]

private def statelessText : Except String String := do
  let lowered ← statelessModule.lowerStatelessDesign?
  unless lowered.implementation.parseCheck do
    throw "stateless round trip failed"
  return lowered.implementation.renderedVerilog

#guard statelessText.toOption.any fun text =>
  !text.contains "clk" && !text.contains "rst" &&
    !text.contains "always" && text.contains "assign q"

private inductive ImportDomain : Type where
  | marker

private instance : Loom.Hw.ClockDomain ImportDomain where
  name := "chosen_domain"

#guard match statelessModule.lowerStatelessComponent? >>= (·.bind? (δ := ImportDomain)) with
  | .ok component =>
      component.sealed.component.kind == .stateless &&
        component.sealed.component.interface.ports.all
          (·.domain == "chosen_domain")
  | .error _ => false

private def unsupportedModule : ImportIR.Module :=
  { simple with unsupported :=
      [⟨"tranif1", "bidirectional switch primitive", location⟩] }

#guard match unsupportedModule.lowerLocalDesign? with
  | .error _ => true
  | .ok _ => false

private def explicitPartial : PartialValue :=
  { site := "fixture_partial"
    classification := .synthesisDontCare
    knownMask := 0xf0
    knownValue := 0xa0
    implementationValue := 0xa5
    rationale := "low nibble is deliberately ignored by the fixture consumer" }

#guard explicitPartial.validB 8
#guard explicitPartial.allowedB 8 0xaf
#guard !explicitPartial.allowedB 8 0x5f

private def partialModule : ImportIR.Module :=
  { statelessModule with
    outputs := [⟨"q", 8, .partialLiteral 8 explicitPartial location, location⟩] }

#guard match partialModule.lowerStatelessDesign? with
  | .ok lowered => lowered.implementation.design.combOutputs.length == 1
  | .error _ => false

#guard match ({ partialModule with outputs :=
    [⟨"q", 8, .partialLiteral 8
      { explicitPartial with implementationValue := 0x55 } location, location⟩] }).lowerAny? with
  | .error _ => true
  | .ok _ => false

private def hierarchyChild : ImportIR.Module where
  name := "hierarchy_child"
  source := location
  ports :=
    [⟨"a", .input, 8, "byte", location⟩,
     ⟨"q", .output, 8, "byte", location⟩]
  domains := []
  registers := []
  memories := []
  outputs := [⟨"q", 8, .signal 8 "a" location, location⟩]

private def hierarchyParent : ImportIR.Module where
  name := "hierarchy_parent"
  source := location
  ports :=
    [⟨"a", .input, 8, "byte", location⟩,
     ⟨"q", .output, 8, "byte", location⟩]
  domains := []
  registers := []
  memories := []
  outputs :=
    [⟨"q", 8, .signal 8 "__loom_child_u_child__q" location, location⟩]
  instances :=
    [{ name := "u_child", moduleName := "hierarchy_child"
       connections :=
         [{ port := "a", direction := .input,
            signal := "__loom_child_u_child__a", width := 8,
            value := some (.signal 8 "a" location), source := location },
          { port := "q", direction := .output,
            signal := "__loom_child_u_child__q", width := 8,
            source := location }]
       source := location }]

private def hierarchyPackage : ImportIR.Package where
  top := "hierarchy_parent"
  modules := [hierarchyChild, hierarchyParent]
  source := location

#guard hierarchyPackage.validB

#guard match hierarchyParent.lowerAny? with
  | .error _ => true
  | .ok _ => false

private def childLoopExpr : ImportIR.Expr :=
  .signal 8 "__loom_child_u_child__q" location

private def cyclicHierarchyParent : ImportIR.Module :=
  { hierarchyParent with
    instances := hierarchyParent.instances.map fun inst =>
      { inst with connections := inst.connections.map fun connection =>
          if connection.port == "a" then
            { connection with value := some childLoopExpr }
          else connection } }

#guard !({ hierarchyPackage with
  modules := [hierarchyChild, cyclicHierarchyParent] }).validB

private def mistypedHierarchyParent : ImportIR.Module :=
  { hierarchyParent with
    instances := hierarchyParent.instances.map fun inst =>
      { inst with connections := inst.connections.map fun connection =>
          if connection.port == "a" then { connection with width := 7 }
          else connection } }

#guard !({ hierarchyPackage with
  modules := [hierarchyChild, mistypedHierarchyParent] }).validB

private def digest := String.ofList (List.replicate 64 'a')

private def sourceBinding : ArtifactBinding where
  role := "source"
  path := "fixture/simple.sv"
  sha256 := digest
  identity := Loom.Artifact.Identity.ofText "module imported_simple; endmodule\n"

private def neutralBinding : ArtifactBinding where
  role := "neutral_import_ir"
  path := "build/simple.import.json"
  sha256 := digest
  identity := Loom.Artifact.Identity.ofText "{\"schema\":1}\n"

private def manifest : ImportManifest where
  frontend := "fixture"
  version := "1"
  invocation := ["fixture", "simple.sv"]
  sources := [sourceBinding]
  neutralArtifact := neutralBinding
  assumptions := ["the fixture frontend interpreted SystemVerilog correctly"]

#guard manifest.validB
#guard !({ manifest with assumptions := [] }).validB
#guard !({ manifest with sources := [sourceBinding, sourceBinding] }).validB

end Tests.ImportIR
