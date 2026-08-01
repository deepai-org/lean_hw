-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.SyncRead
import Loom.Hw.Footprint

/-!
# D37 — a reset image the flow cannot deliver is refused, not discovered

D30 is the defect this file exists to make impossible. Loom emits a
`MemDecl`'s reset image as a Verilog `initial` block; on the openXC7 path
that image survives **only** for banks yosys maps to block RAM. The epoch
engine's 512×3 `cell_flags` became distributed LUT RAM (`RAM64M`), whose
non-zero init the configuration path does not carry — the bank powered up
all-zero on the fabric while the proofs, the emulator and the simulation
all agreed it was initialized. No stage of the flow said a word; the ZC702
said `-BADREF`.

D31 and `scripts/check_mem_init.py` made that *detectable*: after
synthesis, `Loom/Netlist/Mem.lean` reassembles the mapped primitives into a
bank and `checkImage` fails a non-zero image sitting on a distributed-RAM
bank (`Loom/Netlist/EQCHECK_SPEC.md` §Memories). That is a guard on the
artifact. It is not a property of the design, and it fires only once
someone has run synthesis.

This module is the *prevention* half: a decidable Boolean over a `Design`,
in the shape of D19's `Design.syncReadOkB` and `Compile.designWFCheck`,
that is `false` exactly when the design declares a non-zero reset image on
a bank whose shape the flow will map to distributed RAM.
`Design.emit` refuses such a design (`Loom/Hw/EmitIO.lean`), so the defect
is a compile-time error rather than a silicon symptom.

## Tying the two checks together

The two checks *must not* be able to disagree about what "undeliverable"
means, so there is exactly one rule and both call it:

`imageDelivered : MemFamily → Bool → Bool` — the configuration path
delivers a memory's reset image iff the image is all-zero or the bank sits
in block RAM. `Loom.Netlist.checkImage` calls it with the family it
*observed* in the netlist; `Design.memInitOkFor` below calls it with the
family this module *predicts* from the declared shape. `MemFamily` itself
moved here from `Loom/Netlist/Mem.lean` for the same reason (that module
re-exports it, so the netlist names are unchanged).

What the two checks legitimately differ on is the *family*, and that
difference is the point:

* downstream reads the family off the netlist — ground truth for the
  mapping the tool actually chose;
* here it is **predicted** from `(addrWidth, dataWidth)` and the read
  shape, because at design time the netlist does not exist.

The prediction is deliberately conservative — it errs toward `.lutram`,
i.e. toward refusing — and a design that believes the prediction wrong can
say so by name in `Design.ackMemInit` rather than by deleting the check.
A synthesis tool is still free to choose differently from the prediction in
either direction, which is why eqcheck's downstream check stays: prevention
and detection are complementary here, not redundant.

## The prediction

For a memory of `2 ^ addrWidth` words of `dataWidth` bits:

1. **ROMs are not hazards.** A memory no rule ever writes is realized as a
   LUT ROM (or a block-RAM ROM, or constant-folded away); a LUT truth table
   and a flip-flop `INIT` are both carried by the bitstream. `s0bscan`'s
   `banner` and `acc8`'s `prog` are exactly this case, and
   `EQCHECK_SPEC.md` §Memories classifies them the same way downstream.
   So only *written* memories are examined.
2. **Asynchronous reads cannot be block RAM.** A block-RAM read port is
   registered (D19); a bank the design reads combinationally can only be
   distributed RAM. `Design.syncReadOkB` is the existing decision of that
   question, and it is reused verbatim.
3. **Small banks are not worth a block RAM.** yosys spends a `RAMB*` on a
   bank that would otherwise cost many LUT slices. The observed boundary is
   the D30 evidence itself: `cell_flags` (512×3 = 1536 bits) and the
   lnp64mini trap-PC tables (32×64 = 2048 bits) went distributed, while the
   epoch data banks (512×32 = 16384 bits) and lnp64mini's `dmem`
   (512×64 = 32768 bits) went to block RAM. The line is drawn at one
   `RAMB18E1`'s usable data capacity: a bank that does not fill one is
   predicted distributed.

None of this is read by any semantic function — not `Expr.eval`, not
`Design.cycle`, not `Compile.compile`, not the printer. Like `syncReadOkB`
it is a predicate *about* a design, so every existing theorem and every
byte of every emitted module is unchanged by its introduction.
-/

namespace Loom.Hw

/-! ## The mapping class, and the one deliverability rule -/

/-- Which primitive family holds a bank, and hence whether the
configuration path delivers its reset image.

The distinction is the whole of D30: a `RAMB*` image is part of the
bitstream and arrives; a distributed-RAM (`RAM*`) image is *not* delivered
by the openXC7 path — the bank powers up all-zero, with no diagnostic at
any stage (`LOOM_GAPS.md` D30, `Machines/Epoch/EPOCH_SPEC.md` E13).

Lives here rather than in `Loom/Netlist/Mem.lean` (where it was introduced)
so that the design-level check and the netlist-level check share one type
and one rule; `Loom.Netlist` re-exports it. -/
inductive MemFamily where
  | bram
  | lutram
deriving BEq, DecidableEq, Repr, Inhabited

def MemFamily.name : MemFamily → String
  | .bram => "block RAM"
  | .lutram => "distributed LUT RAM"

/-- **The deliverability rule (D30), stated once.** The configuration path
delivers a bank's reset image iff the image is all-zero — which every
realization delivers, including a distributed one — or the bank sits in
block RAM, whose `INIT_xx` parameters are part of the bitstream.

`Loom.Netlist.checkImage` calls this with the family it *observed* in the
netlist; `Design.memInitOkFor` calls it with the family predicted from the
declared shape. The two checks therefore cannot disagree about what
"undeliverable" means — only about which family a bank ends up in, which is
exactly the difference between a prediction and a measurement. -/
def imageDelivered (fam : MemFamily) (nonZero : Bool) : Bool :=
  !nonZero || fam == .bram

/-- Usable data bits of one `RAMB18E1` (16 Kib; the parity bits are not
counted). The prediction's size threshold — see the module docstring for
the measurements that place it here. -/
def bramDataBits : Nat := 16384

/-- The mapping class predicted for a *written* bank of `2 ^ aw` words of
`dw` bits whose reads are (`syncRead = true`) or are not the registered D19
shape. Conservative: anything not clearly block-RAM-shaped is `.lutram`. -/
def predictedFamily (aw dw : Nat) (syncRead : Bool) : MemFamily :=
  if syncRead && bramDataBits ≤ 2 ^ aw * dw then .bram else .lutram

/-! ## The design-level check -/

/-- Does the declared reset image have a set bit anywhere in the declared
address space? Evaluates `init` at all `2 ^ addrWidth` addresses, the same
sweep `Loom.Netlist.checkImage` does on the netlist side. -/
def MemDecl.imageNonZeroB (md : MemDecl) : Bool :=
  (List.range (2 ^ md.addrWidth)).any fun a => md.init a != 0#md.dataWidth

/-- Does any rule write memory `m`? An unwritten memory is a ROM, and a ROM
image is delivered by every realization (docstring, point 1). -/
def Design.memWrittenB (d : Design) (m : String) : Bool :=
  d.rules.any fun rl => rl.body.memWrites.contains m

/-- The mapping class predicted for `md` in `d`. -/
def Design.memFamilyOf (d : Design) (md : MemDecl) : MemFamily :=
  predictedFamily md.addrWidth md.dataWidth (d.syncReadOkB md.name)

/-- **The D37 check, per memory.** `false` exactly when `md` is written,
declares a non-zero reset image, and its shape maps to distributed RAM. -/
def Design.memInitOkFor (d : Design) (md : MemDecl) : Bool :=
  -- The middle disjunct is semantically redundant (`imageDelivered _ false`
  -- is `true`) and present as a cost guard: `memFamilyOf` runs D19's
  -- `syncReadOkB` over every rule, and only a non-zero image can fail.
  !d.memWrittenB md.name || !md.imageNonZeroB
    || imageDelivered (d.memFamilyOf md) md.imageNonZeroB

/-- The memories that fail the check, acknowledged or not. -/
def Design.memInitOffenders (d : Design) : List MemDecl :=
  d.mems.filter fun md => !d.memInitOkFor md

/-- **The D37 check.** `true` iff no memory of `d` depends on a reset image
this flow cannot deliver. Ignores `ackMemInit`: this is the property, and
`memInitAckOkB` is what `Design.emit` enforces. -/
def Design.memInitOkB (d : Design) : Bool := d.memInitOffenders.isEmpty

/-- The offenders the design has *not* written down in `ackMemInit`. -/
def Design.memInitUnacked (d : Design) : List MemDecl :=
  d.memInitOffenders.filter fun md => !d.ackMemInit.contains md.name

/-- What `Design.emit` enforces: every offender is an acknowledged one. -/
def Design.memInitAckOkB (d : Design) : Bool := d.memInitUnacked.isEmpty

/-- The refusal message: which memory, why the image cannot be delivered,
and what to do instead. -/
def Design.memInitError (d : Design) (md : MemDecl) : String :=
  s!"Design.emit: memory '{md.name}' declares a NON-ZERO reset image on a \
{2 ^ md.addrWidth}×{md.dataWidth} bank, whose shape this flow maps to \
{(d.memFamilyOf md).name}. The configuration path does not carry a \
distributed-RAM image to the fabric: the bank powers up ALL-ZERO on \
silicon while simulation and the proofs show the image (LOOM_GAPS.md D30 \
/ D37, Machines/Epoch/EPOCH_SPEC.md E13). Fix: put the reset state in an \
explicit reset sequence (a zeroing sweep rule that writes the image after \
reset), or declare the image all-zero. If the loss is known and argued \
harmless, record it by name in the design's `ackMemInit`."

/-- A human-readable D37 report line for one memory (the `syncReadReport`
counterpart). -/
def Design.memInitReport (d : Design) (md : MemDecl) : String :=
  s!"  {md.name}: {2 ^ md.addrWidth}×{md.dataWidth} written=\
{d.memWrittenB md.name} nonZeroInit={md.imageNonZeroB} \
family≈{(d.memFamilyOf md).name} ok={d.memInitOkFor md}" ++
  (if d.ackMemInit.contains md.name then "  (ACK)" else "")

end Loom.Hw
