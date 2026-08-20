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

private def unsupportedModule : ImportIR.Module :=
  { simple with unsupported :=
      [⟨"tranif1", "bidirectional switch primitive", location⟩] }

#guard match unsupportedModule.lowerLocalDesign? with
  | .error _ => true
  | .ok _ => false

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
