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

/-- Pure, reusable gate for every path that emits an ordinary `Design`.
Keeping this separate from file IO prevents structural/system emitters from
accidentally bypassing the checks enforced by `Design.emit`. -/
def Loom.Hw.Design.emitCheck (d : Loom.Hw.Design) : Except String Unit := do
  let taken := d.regs.map (·.name) ++ d.mems.map (·.name)
  for i in d.inputs do
    if taken.contains i.name then
      throw s!"Design.emit: input '{i.name}' collides with a register/memory name"
  let inNames := d.inputs.map (·.name)
  if inNames.length ≠ inNames.eraseDups.length then
    throw "Design.emit: duplicate input names"
  let outNames := d.exportedRegs.map ("o_" ++ ·.name) ++
    d.combOutputs.map (·.name)
  if outNames.length ≠ outNames.eraseDups.length then
    throw "Design.emit: duplicate register/combinational output port names"
  if outNames.any inNames.contains then
    throw "Design.emit: an output port collides with an input port"
  for n in d.outputsUndeclared do
    throw (d.outputsError n)
  let rns := d.regs.map (·.name)
  if rns.length ≠ rns.eraseDups.length then
    throw s!"Design.emit: duplicate register names in '{d.name}' — if this design came from `par`/`prefixed`, the instance prefixes are not disjoint (D16)"
  let mns := d.mems.map (·.name)
  if mns.length ≠ mns.eraseDups.length then
    throw s!"Design.emit: duplicate memory names in '{d.name}' — if this design came from `par`/`prefixed`, the instance prefixes are not disjoint (D16)"
  for m in d.syncReadMems do
    if !d.mems.any (fun md => md.name = m) then
      throw s!"Design.emit: syncReadMems names '{m}', which is not a declared memory of '{d.name}'"
    if !d.syncReadOkB m then
      throw s!"Design.emit: D19 — memory '{m}' of '{d.name}' is read outside a register-latch site, so it would emit as LUTRAM:\n{d.syncReadReport m}"
  for (n, w) in d.badRegReads do
    throw (d.badRegReadError n w)
  for (m, dw) in d.badMemReads do
    throw (d.badMemReadError m dw)
  if !Loom.Hw.Compile.designWFCheck d then
    throw s!"Design.emit: design '{d.name}' fails `Compile.designWFCheck` — a rule \
writes a signal the design does not declare, two register or memory names \
collide, or a memory's write-port indices do not strictly increase along the \
design's write order."

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
  match d.emitCheck with
  | .ok _ => pure ()
  | .error message => throw <| IO.userError message
  let changed ← Loom.Artifact.writeText path
    (Loom.Emit.MicroVerilog.Print.print (Loom.Hw.Compile.compile d))
  IO.println s!"{path} {if changed then "written" else "unchanged"}"

/-- Emit the same certified `Design` transition on an explicitly selected
Verilog edge.  Falling-edge import domains therefore do not require a second
hardware semantics or an unchecked textual rewrite. -/
def Loom.Hw.Design.emitOn (d : Loom.Hw.Design) (edge : Loom.ClockEdge)
    (path : System.FilePath) : IO Unit := do
  match d.emitCheck with
  | .ok _ => pure ()
  | .error message => throw <| IO.userError message
  let changed ← Loom.Artifact.writeText path
    (Loom.Emit.MicroVerilog.Print.print
      (Loom.Hw.Compile.compileForEdge d edge))
  IO.println s!"{path} {if changed then "written" else "unchanged"}"

/-- Emit with explicit physical clock/reset names and synchronous reset
polarity. The compiler theorems show this metadata leaves the abstract
transition and reset state unchanged. -/
def Loom.Hw.Design.emitWithClockReset (d : Loom.Hw.Design)
    (edge : Loom.ClockEdge) (clockName resetName : String)
    (resetActiveHigh : Bool) (path : System.FilePath) : IO Unit := do
  match d.emitCheck with
  | .ok _ => pure ()
  | .error message => throw <| IO.userError message
  let changed ← Loom.Artifact.writeText path
    (Loom.Emit.MicroVerilog.Print.print
      (Loom.Hw.Compile.compileForClockReset d edge clockName resetName
        resetActiveHigh))
  IO.println s!"{path} {if changed then "written" else "unchanged"}"

/-- Emit clocked state without a reset port or reset branch. Any source-level
synchronous reset must already be explicit in the compiled next-state graph. -/
def Loom.Hw.Design.emitResetless (d : Loom.Hw.Design)
    (edge : Loom.ClockEdge) (clockName : String)
    (path : System.FilePath) : IO Unit := do
  match d.emitCheck with
  | .ok _ => pure ()
  | .error message => throw <| IO.userError message
  let compiled := Loom.Hw.Compile.compileResetless d edge clockName
  unless compiled.parseCheck do
    throw <| IO.userError s!"resetless design '{d.name}' failed µVerilog round-trip checking"
  let changed ← Loom.Artifact.writeText path
    (Loom.Emit.MicroVerilog.Print.print compiled)
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
