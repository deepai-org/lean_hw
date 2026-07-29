-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Compile
import Loom.Emit.MicroVerilog.Print

/-!
# One-call Verilog emission

Tutorial-path defect #1 (`Machines/Tutorial/DEFECTS.md`, run 1): a new
design could not be emitted without reading `Tools/Emit.lean` and writing
IO by hand. `Design.emit` is the generic entry point: compile with the
verified compiler, print with the verified printer, write the file.
-/

/-- Compile `d` with the verified compiler, print it with the verified
printer, and write the result to `path` (creating parent directories).
Usage from a design file:

```
def main : IO Unit := design.emit "rtl/mydesign.v"
```

run with `lake env lean --run MyDesign.lean` (the `main` must be at root
level — tutorial defect #2). -/
def Loom.Hw.Design.emit (d : Loom.Hw.Design) (path : System.FilePath) :
    IO Unit := do
  if let some dir := path.parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile path
    (Loom.Emit.MicroVerilog.Print.print (Loom.Hw.Compile.compile d))
  IO.println s!"{path} written"
