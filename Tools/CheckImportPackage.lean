-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ImportJson

/-! # Checked neutral hierarchy package command -/

namespace Tools.CheckImportPackage

private def usage : String :=
  "usage: lake exe checkImportPackage INPUT.package.import.json"

def main (arguments : List String) : IO Unit := do
  let [input] := arguments
    | throw <| IO.userError usage
  let text ← IO.FS.readFile input
  let package ← match Loom.Hw.ImportJson.parsePackageDocument text with
    | .ok package => pure package
    | .error message => throw <| IO.userError s!"neutral package parse failed: {message}"
  let checked ← match package.check? with
    | .ok checked => pure checked
    | .error message => throw <| IO.userError s!"neutral package check failed: {message}"
  IO.println s!"LOOM_IMPORT_PACKAGE_CHECK_PASS top={checked.top} modules={checked.modules.length}"

end Tools.CheckImportPackage

def main (arguments : List String) : IO Unit :=
  Tools.CheckImportPackage.main arguments
