-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ImportJson
import Loom.Hw.EmitIO

/-! # Checked neutral-import JSON to Loom RTL command -/

namespace Tools.ImportModule

private def usage : String :=
  "usage: lake exe importModule INPUT.import.json OUTPUT.v"

def main (arguments : List String) : IO Unit := do
  let [input, output] := arguments
    | throw <| IO.userError usage
  let text ← IO.FS.readFile input
  let module ← match Loom.Hw.ImportJson.parseDocument text with
    | .ok module => pure module
    | .error message => throw <| IO.userError s!"neutral import parse failed: {message}"
  let lowered ← match module.lowerLocalDesign? with
    | .ok lowered => pure lowered
    | .error message => throw <| IO.userError s!"neutral import lowering failed: {message}"
  let some resetName := lowered.reset.port
    | throw <| IO.userError "checked synchronous-reset import lost its reset port"
  lowered.design.emitWithClockReset lowered.edge lowered.clockPort resetName
    lowered.reset.activeHigh output
  IO.println s!"LOOM_IMPORT_MODULE_PASS module={module.name} edge={repr lowered.edge}"

end Tools.ImportModule

def main (arguments : List String) : IO Unit :=
  Tools.ImportModule.main arguments
