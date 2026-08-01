-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.EmitIO
import Machines.Lnp64mini.Core

/-!
# D37 regression: an undeliverable reset image is refused at emit

`Loom/Hw/MemInitOk.lean` predicts the mapping class of every declared
memory and refuses a design that depends on a non-zero reset image the
configuration path cannot deliver (D30 — found on silicon, as `-BADREF`).

Checked here:

* the **classification**, on the shapes the D30 evidence names: a small
  written bank with a non-zero image is an offender; the same bank with an
  all-zero image, the same image on a bank big enough for block RAM, and a
  never-written ROM (`s0bscan`'s `banner`, `acc8`'s `prog`) are not;
* the **refusal is an emit-time error**, i.e. `Design.emit` throws rather
  than writing the file, and the message names the memory;
* the **escape hatch works and is not silently required**: naming the
  memory in `Design.ackMemInit` makes the same design emit — and
  `lnp64mini`, the one design that used to need it, now passes with an
  empty `ackMemInit`, because D37 fixed `tpc`'s image instead of
  acknowledging it.
-/

namespace Tests.MemInitOk

open Loom.Hw

/-- A written 32×64 bank — the `tpc` shape — with a reset image. `nz` picks
the non-zero (`TEXT_BASE`) image; `ack` names the memory in `ackMemInit`. -/
private def d (nz ack : Bool) : Design where
  name := "meminit"
  regs := [⟨"a", 5, 0⟩, ⟨"v", 64, 0⟩]
  mems := [{ name := "t", addrWidth := 5, dataWidth := 64,
             init := fun _ => if nz then 4096 else 0 }]
  rules :=
    [ ⟨"w", .memWrite 5 64 "t" 0 (.reg 5 "a") (.reg 64 "v")⟩
    , ⟨"r", .write 64 "v" (.memRead 64 "t" (.reg 5 "a"))⟩ ]
  ackMemInit := if ack then ["t"] else []

/-- The same image on a bank that fills a `RAMB18E1` (512×32 — the epoch
data banks' shape, which yosys did map to block RAM and whose init the
bitstream did carry), read the registered D19 way. -/
private def big : Design where
  name := "meminit_big"
  regs := [⟨"a", 9, 0⟩, ⟨"v", 32, 0⟩]
  mems := [{ name := "t", addrWidth := 9, dataWidth := 32, init := fun _ => 7 }]
  rules :=
    [ ⟨"w", .memWrite 9 32 "t" 0 (.reg 9 "a") (.reg 32 "v")⟩
    , ⟨"r", .write 32 "v" (.memRead 32 "t" (.reg 9 "a"))⟩ ]

/-- A never-written ROM with a non-zero image (`banner`/`prog`): a LUT truth
table is carried by the bitstream, so this is not a D30 hazard. -/
private def rom : Design where
  name := "meminit_rom"
  regs := [⟨"a", 5, 0⟩, ⟨"v", 8, 0⟩]
  mems := [{ name := "t", addrWidth := 5, dataWidth := 8, init := fun _ => 65 }]
  rules := [⟨"r", .write 8 "v" (.memRead 8 "t" (.reg 5 "a"))⟩]

-- The classification.
#guard (d true false).memInitOkB == false
#guard (d false false).memInitOkB == true
#guard big.memInitOkB == true
#guard rom.memInitOkB == true
#guard ((d true false).memInitOffenders.map (·.name)) == ["t"]
#guard ((d true false).mems.map (d true false).memFamilyOf) == [MemFamily.lutram]
#guard (big.mems.map big.memFamilyOf) == [MemFamily.bram]

-- The rule the netlist-side check shares (`Loom.Netlist.checkImage`).
#guard imageDelivered .lutram true == false
#guard imageDelivered .lutram false == true
#guard imageDelivered .bram true == true

-- `ackMemInit` is what `Design.emit` consults, and only that.
#guard (d true true).memInitOkB == false          -- still a violation …
#guard (d true true).memInitAckOkB == true        -- … but a recorded one
#guard (d true false).memInitAckOkB == false

/-! **D37's standing claim**: the shipped designs need no exception.
`lnp64mini` declared `tpc`'s image as `TEXT_BASE` until 2026-08-01 and was
the one acknowledged violation repo-wide; the sweep that already
establishes TEXT_BASE made the image redundant, so it is now all-zero and
`ackMemInit` is empty. -/
#guard Machines.Lnp64mini.design.memInitOkB
#guard Machines.Lnp64mini.design.ackMemInit.isEmpty

/-! The refusal is an emit-time *error*: `Design.emit` throws, names the
memory, and writes nothing. The acknowledged variant emits normally. -/
#eval show IO Unit from do
  let path : System.FilePath := "scratch/meminit_d37_test.v"
  if ← path.pathExists then IO.FS.removeFile path
  let refused ←
    try
      (d true false).emit path
      pure ""
    catch e => pure (toString e)
  unless (refused.splitOn "memory 't'").length == 2 do
    throw <| IO.userError s!"D37: emit did not refuse the undeliverable \
      image (got: {refused})"
  unless (refused.splitOn "distributed LUT RAM").length == 2 do
    throw <| IO.userError s!"D37: refusal does not say why (got: {refused})"
  if ← path.pathExists then
    throw <| IO.userError "D37: emit refused but still wrote the file"
  -- the acknowledged one emits
  (d true true).emit path
  unless (← path.pathExists) do
    throw <| IO.userError "D37: the acknowledged design did not emit"
  IO.FS.removeFile path

end Tests.MemInitOk
