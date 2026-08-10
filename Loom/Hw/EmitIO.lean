-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Compile
import Loom.Hw.MemTarget
import Loom.Hw.Outputs
import Loom.Hw.SyncRead
import Loom.Hw.ReadsOk
import Loom.Hw.CompileCorrect
import Loom.Emit.MicroVerilog.Print
import Loom.Artifact

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
  -- D39: an observability selection (`Design.outputs`) may only name
  -- declared registers. An unrecognized name would otherwise silently
  -- export nothing at all, which is the failure mode a *selection* is most
  -- prone to (`Loom/Hw/Outputs.lean`, `Loom/Hw/OUTPUTS_SPEC.md` §2).
  for n in d.outputsUndeclared do
    throw <| IO.userError (d.outputsError n)
  -- **Well-formedness that no composition may violate.** Duplicate
  -- register or memory names are always a bug however they arose, and the
  -- way they arise in practice is a `par`/`prefixed` whose instance
  -- prefixes are not disjoint (D16). That used to be checked by each
  -- machine calling `parOk` before emitting its composed SoC; checking the
  -- *result* here instead catches it whoever built the design and however.
  let rns := d.regs.map (·.name)
  if rns.length ≠ rns.eraseDups.length then
    throw <| IO.userError
      s!"Design.emit: duplicate register names in '{d.name}' — if this design came from `par`/`prefixed`, the instance prefixes are not disjoint (D16)"
  let mns := d.mems.map (·.name)
  if mns.length ≠ mns.eraseDups.length then
    throw <| IO.userError
      s!"Design.emit: duplicate memory names in '{d.name}' — if this design came from `par`/`prefixed`, the instance prefixes are not disjoint (D16)"
  -- D19: memories the design declares as block-RAM-shaped must be read only
  -- through a register-latch site, or they emit as distributed LUTRAM and
  -- the design stops fitting (`Loom/Hw/D19_SPEC.md`). Declared on the
  -- design (`syncReadMems`) so this cannot be skipped by an emit path that
  -- forgets to ask.
  for m in d.syncReadMems do
    if ! d.mems.any (fun md => md.name = m) then
      throw <| IO.userError
        s!"Design.emit: syncReadMems names '{m}', which is not a declared memory of '{d.name}'"
    if ! d.syncReadOkB m then
      throw <| IO.userError
        s!"Design.emit: D19 — memory '{m}' of '{d.name}' is read outside a register-latch site, so it would emit as LUTRAM:\n{d.syncReadReport m}"
  -- Declaration checking in both directions: `designWFCheck` constrains
  -- writes, while `readsOkB` constrains reads. Both are mandatory emission
  -- checks because an undeclared or wrong-width read otherwise evaluates to
  -- zero silently.
  for (n, w) in d.badRegReads do
    throw <| IO.userError (d.badRegReadError n w)
  for (m, dw) in d.badMemReads do
    throw <| IO.userError (d.badMemReadError m dw)
  if ! Loom.Hw.Compile.designWFCheck d then
    throw <| IO.userError
      s!"Design.emit: design '{d.name}' fails `Compile.designWFCheck` — a rule \
writes a signal the design does not declare, two register or memory names \
collide, or a memory's write-port indices do not strictly increase along the \
design's write order."
  let changed ← Loom.Artifact.writeText path
    (Loom.Emit.MicroVerilog.Print.print (Loom.Hw.Compile.compile d))
  IO.println s!"{path} {if changed then "written" else "unchanged"}"

/-- Check the target-dependent memory obligations for `d` against an explicit
implementation profile. This is intentionally separate from `Design.emit`:
generic RTL emission has no FPGA-vendor, ASIC-library, or synthesis-tool
default. -/
def Loom.Hw.Design.checkTarget (d : Loom.Hw.Design)
    (target : Loom.Hw.MemTarget) : IO Unit := do
  for md in d.unrealizableUnackedOn target do
    throw <| IO.userError (d.realizableError target md)

/-- Check `d` against the explicitly selected memory target, then emit it.
Use this entry point for a concrete implementation flow; use `Design.emit`
when producing target-neutral RTL. -/
def Loom.Hw.Design.emitFor (d : Loom.Hw.Design)
    (target : Loom.Hw.MemTarget) (path : System.FilePath) : IO Unit := do
  d.checkTarget target
  d.emit path
