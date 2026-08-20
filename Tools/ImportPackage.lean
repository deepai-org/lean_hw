-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ImportJson
import Loom.Hw.ImportHierarchy
import Loom.Artifact

/-! # Checked neutral hierarchy package to structural Loom RTL -/

namespace Tools.ImportPackage

private def usage : String :=
  "usage: lake exe importPackage INPUT.package.import.json OUTPUT.v"

def main (arguments : List String) : IO Unit := do
  let [input, output] := arguments
    | throw <| IO.userError usage
  let text ← IO.FS.readFile input
  let package ← match Loom.Hw.ImportJson.parsePackageDocument text with
    | .ok package => pure package
    | .error message => throw <| IO.userError s!"neutral package parse failed: {message}"
  let artifacts ← match package.artifacts? with
    | .ok artifacts => pure artifacts
    | .error message => throw <| IO.userError s!"neutral package lowering failed: {message}"
  let rendered := String.intercalate "\n" (artifacts.map (·.text))
  let changed ← Loom.Artifact.writeText output rendered
  IO.println s!"{output} {if changed then "written" else "unchanged"}"
  IO.println s!"LOOM_IMPORT_PACKAGE_PASS top={package.top} modules={package.modules.length} artifacts={artifacts.length}"

end Tools.ImportPackage

def main (arguments : List String) : IO Unit :=
  Tools.ImportPackage.main arguments
