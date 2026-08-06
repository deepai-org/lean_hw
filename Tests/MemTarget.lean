-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.EmitIO
import Machines.Lnp64mini.Core

/-!
# D38 regression: shape checks are stated against a declared target

`Loom/Hw/MemTarget.lean` turns D37's "is this bank block-RAM friendly" into
"is this design realizable on target T", so a design that only works on one
memory technology is *visibly* target-specific
(`Loom/Hw/MEMTARGET_SPEC.md`).

Checked here:

* the **profiles disagree, and that is the point**: the same 512×32 bank
  with a non-zero reset image is realizable on `xc7` (block RAM `INIT_xx`
  are in the bitstream) and **not** on `asicSram` (an SRAM macro has no
  initial contents);
* the **write-port budget bites**, which is D38's addition over D37: the
  same bank with a *second* write port no longer fits a 7-series block RAM
  (two ports total), so on `xc7` it is predicted distributed and its image
  is refused — the CapWalk CE9/CE10 shape, the one that measured 14× the
  LUTs, now caught at emit;
* the **port-trace condition is Loom's**, not one machine's
  (`Design.memPortTraceOkB`, promoted from `Machines/CapWalk/Engine.lean`),
  and it is *not* acknowledgeable — it is a compiler precondition, not a
  mapping prediction;
* the `xc7` profile **is** D37's rule (`xc7_familyOf`, `xc7_imageDelivered`
  in `Loom/Hw/MemTarget.lean`), so the design-time and netlist-time rules
  still cannot disagree;
* the shipped `lnp64mini` is realizable on **all three** profiles.
-/

namespace Tests.MemTarget

open Loom.Hw

/-- A 512×32 bank — the epoch data banks' shape, which yosys does map to
block RAM — read the registered D19 way, with a non-zero reset image.
`twoPorts` adds a second writer on port 1, which is the CE10 shape. -/
private def big (twoPorts : Bool) : Design where
  name := "memtarget"
  outputs := ["a", "b", "v"]  -- D39: export all regs (pre-D39 ports)
  regs := [⟨"a", 9, 0⟩, ⟨"b", 9, 0⟩, ⟨"v", 32, 0⟩]
  mems := [{ name := "t", addrWidth := 9, dataWidth := 32, init := fun _ => 7 }]
  rules :=
    [ ⟨"w0", .memWrite 9 32 "t" 0 (.reg 9 "a") (.reg 32 "v")⟩ ] ++
    (if twoPorts then
      [⟨"w1", .memWrite 9 32 "t" 1 (.reg 9 "b") (.reg 32 "v")⟩] else []) ++
    [ ⟨"r", .write 32 "v" (.memRead 32 "t" (.reg 9 "a"))⟩ ]

/-- The same design with its two write sites on ONE port: two writes to one
port in one cycle is not what the emitted module does, and it is what
`Compile.MemWriteWF`'s port condition forbids. -/
private def clash : Design :=
  { big true with
    rules :=
      [ ⟨"w0", .memWrite 9 32 "t" 0 (.reg 9 "a") (.reg 32 "v")⟩
      , ⟨"w1", .memWrite 9 32 "t" 0 (.reg 9 "b") (.reg 32 "v")⟩
      , ⟨"r", .write 32 "v" (.memRead 32 "t" (.reg 9 "a"))⟩ ] }

-- Write-port counting: a ROM uses none, a written bank uses what it asks for.
#guard (big false).writePortCount "t" == 1
#guard (big true).writePortCount "t" == 2

-- The profiles disagree about the one-port bank, and that is the finding.
#guard (big false).realizableOnB MemTarget.xc7
#guard (big false).realizableOnB MemTarget.ecp5
#guard !((big false).realizableOnB MemTarget.asicSram)
#guard ((big false).unrealizableOn MemTarget.asicSram).map (·.name) == ["t"]

-- D38's addition over D37: the second write port pushes the bank out of the
-- macro on every profile, and the image goes with it.
#guard ((big false).mems.map (MemTarget.xc7.familyOf (big false)))
         == [MemFamily.bram]
#guard ((big true).mems.map (MemTarget.xc7.familyOf (big true)))
         == [MemFamily.lutram]
#guard !((big true).realizableOnB MemTarget.xc7)
-- …which D37's port-blind prediction could not see:
#guard (big true).memInitOkB

-- The port-trace condition, promoted from `Machines/CapWalk/Engine.lean`.
#guard (big true).memPortTraceOkB "t"
#guard !(clash.memPortTraceOkB "t")
#guard !(clash.realizableOnB MemTarget.xc7)
-- and it is not acknowledgeable, while an image loss is
#guard !(({ clash with ackMemInit := ["t"] } : Design).realizableAckOkB MemTarget.xc7)
#guard ({ big true with ackMemInit := ["t"] } : Design).realizableAckOkB MemTarget.xc7

/-! The shipped mini core is realizable on all three profiles — it depends
on no reset image at all (D37 fixed `tpc`), so nothing about it is
FPGA-specific in this respect. -/
#guard Machines.Lnp64mini.design.realizableOnB MemTarget.xc7
#guard Machines.Lnp64mini.design.realizableOnB MemTarget.ecp5
#guard Machines.Lnp64mini.design.realizableOnB MemTarget.asicSram

/-! The refusal is an emit-time *error*, and it names the memory, the
target and the realization. -/
#eval show IO Unit from do
  let path : System.FilePath := "scratch/memtarget_d38_test.v"
  if ← path.pathExists then IO.FS.removeFile path
  let refused ←
    try
      (big true).emit path
      pure ""
    catch e => pure (toString e)
  for needle in ["memory 't'", "target 'xc7'", "distributed LUT RAM",
                 "2 write port"] do
    unless (refused.splitOn needle).length == 2 do
      throw <| IO.userError s!"D38: the refusal does not say '{needle}' \
        (got: {refused})"
  if ← path.pathExists then
    throw <| IO.userError "D38: emit refused but still wrote the file"
  -- the acknowledged variant emits; the port clash never does
  ({ big true with ackMemInit := ["t"] } : Design).emit path
  unless (← path.pathExists) do
    throw <| IO.userError "D38: the acknowledged design did not emit"
  IO.FS.removeFile path
  let refused2 ←
    try
      ({ clash with ackMemInit := ["t"] } : Design).emit path
      pure ""
    catch e => pure (toString e)
  unless (refused2.splitOn "strictly increase").length == 2 do
    throw <| IO.userError s!"D38: an acknowledged port clash was not \
      refused (got: {refused2})"
  if ← path.pathExists then IO.FS.removeFile path

end Tests.MemTarget
