-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Compile
import Loom.Hw.MemInitOk
import Loom.Hw.MemTarget
import Loom.Hw.Outputs
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
  -- D15 sanity: input names must be fresh (they print as `input wire`
  -- identifiers next to the register declarations).
  let taken := d.regs.map (·.name) ++ d.mems.map (·.name)
  for i in d.inputs do
    if taken.contains i.name then
      throw <| IO.userError
        s!"Design.emit: input '{i.name}' collides with a register/memory name"
  let inNames := d.inputs.map (·.name)
  if inNames.length ≠ inNames.eraseDups.length then
    throw <| IO.userError "Design.emit: duplicate input names"
  -- D38 (subsuming D37): refuse a design some memory of which the target
  -- memory technology cannot realize — a reset image the flow does not
  -- deliver (D30 — the epoch engine's `cell_flags`, found on silicon), or
  -- a write-port assignment the compiler's memory theorem does not admit
  -- (CAPWALK CE10, where the same shape cost 14× the LUTs). The target is
  -- the one this repo builds for; a design can be checked against another
  -- with `Design.realizableOnB` (`Loom/Hw/MemTarget.lean`). Image
  -- offenders the design has written down in `ackMemInit` pass; everything
  -- else is an error here rather than a `-BADREF` on a board.
  for md in d.unrealizableUnackedOn Loom.Hw.MemTarget.default do
    throw <| IO.userError (d.realizableError Loom.Hw.MemTarget.default md)
  -- D39: an observability selection (`Design.outputs`) may only name
  -- declared registers. An unrecognized name would otherwise silently
  -- export nothing at all, which is the failure mode a *selection* is most
  -- prone to (`Loom/Hw/Outputs.lean`, `Loom/Hw/OUTPUTS_SPEC.md` §2).
  for n in d.outputsUndeclared do
    throw <| IO.userError (d.outputsError n)
  if let some dir := path.parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile path
    (Loom.Emit.MicroVerilog.Print.print (Loom.Hw.Compile.compile d))
  IO.println s!"{path} written"
