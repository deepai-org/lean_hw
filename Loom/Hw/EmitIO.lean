-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Compile
import Loom.Hw.MemInitOk
import Loom.Hw.MemTarget
import Loom.Hw.Outputs
import Loom.Hw.SyncRead
import Loom.Hw.ReadsOk
import Loom.Hw.CompileCorrect
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
  -- **W1.1 — declaration checking, both directions.** `designWFCheck`
  -- constrains WRITES (a rule may not write an undeclared signal) and was
  -- previously only exercised on the proof path, so a corroborate-only design
  -- never ran it. `readsOkB` constrains READS, whose failure mode is worse
  -- because it is silent: an undeclared or wrong-width read evaluates to 0
  -- forever, so the design simulates, emits, and is simply wrong. Both are
  -- emit-time refusals here for the D19/D38/D39 reason — an obligation a
  -- caller can skip is not an obligation.
  for (n, w) in d.badRegReads do
    throw <| IO.userError (d.badRegReadError n w)
  for (m, dw) in d.badMemReads do
    throw <| IO.userError (d.badMemReadError m dw)
  if ! Loom.Hw.Compile.designWFCheck d then
    throw <| IO.userError
      s!"Design.emit: design '{d.name}' fails `Compile.designWFCheck` — a rule \
writes a signal the design does not declare, two register or memory names \
collide, or a memory's write-port indices do not strictly increase along the \
design's write order. This was previously checked only on the proof path, so \
a corroborate-only design could emit without it (W1.1)."
  if let some dir := path.parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile path
    (Loom.Emit.MicroVerilog.Print.print (Loom.Hw.Compile.compile d))
  IO.println s!"{path} written"
