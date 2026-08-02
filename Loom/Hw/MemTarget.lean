-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.MemInitOk
import Loom.Hw.Compile

/-!
# D38 — memory shape checks are stated against a *declared* target

`Loom/Hw/MEMTARGET_SPEC.md` is the recorded decision this module
implements, and it is short: a shape check that hardcodes one vendor's
block RAM makes every future design FPGA-shaped forever, so the checks
split in two.

**Universal, and deliberately *not* parameterized here:**

* **sync read (D19)** — ASIC SRAM macros are synchronous-read and so is
  FPGA block RAM; the asynchronous read is the outlier on *both*
  technologies. `Design.syncReadOkB` stays a plain, target-free check, and
  this module consumes its verdict rather than re-deciding it.
* **not relying on a reset image (D30/D37)** — SRAM has no initial
  contents at all. This is the ASIC rule; the FPGA merely tolerated
  violating it. What *is* target-specific is not the rule but which
  realizations deliver an image, which is a `MemTarget` field.

**Vendor-specific, i.e. the actual risk:** write-port budget, the capacity
and depth at which a bank stops being worth a macro. Those are the fields
of `MemTarget`.

## What discovered it

`Machines/CapWalk/CAPWALK_SPEC.md` deviations CE9/CE10. The naive capability
engine measured **9 523 LUT / 3 982 FF**; the disciplined one measures
**671 LUT / 442 FF** — a 14× area swing on *identical logic*, because two
banks asked for two write ports each and a 7-series block RAM has two ports
**total**, so they fell out of block RAM into flops and 1024:1 read muxes.
Nothing in the source says "this bank is now a thousand flops". The engine
grew a local guard (`Engine.memPortsOkB`); this module is that guard
promoted to Loom, where it belongs, and generalized so it does not encode
Xilinx into every design that follows (`LOOM_GAPS.md` D38).

## The check

`Design.realizableOnB t` is `true` iff every memory of the design is
realizable on target `t`:

1. **the write-port assignment is well formed** — `Compile.designTrace`'s
   port indices strictly increase along the design's syntactic write order.
   This is `Compile.MemWriteWF`'s port condition, which the compiler's
   correctness theorem already requires; it is un-ackable and target-free,
   and it is what `Engine.memPortsOkB` used to say by hand. Without it the
   *count* of write ports is not even meaningful.
2. **the reset image is one this target delivers** — D37's rule, now read
   through the profile: a written bank with a non-zero image must land in a
   realization whose image the target's configuration path carries. The
   target's write-port budget enters here, through the *prediction*: a bank
   asking for more write ports than a macro has is predicted soft, and a
   soft bank on `xc7` loses its image (D30, found on silicon). D37 could
   not see that, since its prediction was port-blind.

An unwritten memory is a ROM on every technology (a LUT truth table, a
synthesized ROM cone, a mask ROM), so it is not examined — D37's rule 1,
kept universal.

## One prediction, not two

`predictedFamilyWith` in `Loom/Hw/MemInitOk.lean` is the single mapping
rule, and both the design-time and the netlist-time checks descend from it:
`Loom.Netlist.checkImage` calls `imageDelivered` with the family it
*observed*, `Design.memInitOkFor` calls it with the port-blind `xc7`
prediction, and `MemTarget.familyOf` below calls the same rule with the
profile's numbers and the design's actual write-port count.
`xc7_imageDelivered` and `xc7_familyOf` below are the standing proofs that
the `xc7` profile *is* D37's rule rather than a fork of it.

## What the profiles do not capture

They predict a mapping; they do not control one. A synthesis tool may still
choose otherwise in either direction, which is exactly why the downstream
netlist checks (D31, `eqcheck`'s `meminit` verdict) stay. Nor do the
profiles model byte enables, initialization by an explicit reset sequence,
banking/replication a tool may perform, timing, or power.
-/

namespace Loom.Hw

/-! ## The profile -/

/-- A declared memory technology, as ordinary Lean data.

Only fields at least one shipped profile actually needs are present. In
particular there is **no** `syncReadOnly` field: every real target wants a
registered read port, so D19 stays unparameterized (`MEMTARGET_SPEC.md`,
"keep these unparameterized"), and there is no per-target write-port
*hard* limit either — any technology can build a bank with N write ports
out of flops and muxes. What a technology limits is how many write ports a
bank may have and still be a **macro**, which is `maxMacroWritePorts`. -/
structure MemTarget where
  /-- Profile name, as it appears in a refusal (`xc7`, `ecp5`, `asicSram`). -/
  name : String
  /-- What the dedicated memory primitive is called on this target; used in
  reports and refusals so the diagnosis names the technology's own part. -/
  macroName : String
  /-- What a bank that misses the macro becomes instead (distributed LUT
  RAM, a flip-flop array). -/
  softName : String
  /-- **D38's subject.** Write ports a bank may have and still be placed in
  the dedicated macro. Not a limit on what can be built — a bank over
  budget is built out of soft logic, at the cost CE9/CE10 measured. -/
  maxMacroWritePorts : Nat
  /-- Data bits a bank must have to be worth a macro (0 = no capacity
  floor asserted). -/
  macroMinDataBits : Nat
  /-- Words a bank must have to be worth (or to be offered as) a macro
  (0 = no depth floor asserted). -/
  macroMinDepth : Nat
  /-- Does the configuration/manufacturing path deliver a reset image to a
  bank held in the macro? -/
  macroInitDeliverable : Bool
  /-- … and to a bank held in soft logic? -/
  softInitDeliverable : Bool

namespace MemTarget

/-- Deliverability of an image by realization class, i.e. the profile read
as `MemFamily → Bool`. `.bram` is the target's macro and `.lutram` its soft
fallback; the constructor names are Xilinx-flavoured for the historical
reason that D30 was found there (`MemInitOk.lean`), and `macroName` /
`softName` are what a report prints. -/
def initDeliverable (t : MemTarget) : MemFamily → Bool
  | .bram => t.macroInitDeliverable
  | .lutram => t.softInitDeliverable

/-- The target's name for a realization class. -/
def familyName (t : MemTarget) : MemFamily → String
  | .bram => t.macroName
  | .lutram => t.softName

/-- **The deliverability rule (D30/D37), read through the profile**: the
image arrives iff it is all-zero — which every realization delivers — or
the realization it sits in is one this target initializes. -/
def imageDelivered (t : MemTarget) (fam : MemFamily) (nonZero : Bool) : Bool :=
  !nonZero || t.initDeliverable fam

/-! ## The profiles

Three, of which exactly one is validated end to end in this repo. Where a
number is a datasheet reading rather than a measurement it says so; where
it is neither, the docstring says *that*, because an honestly-marked TODO
beats a confident wrong number. -/

/-- **Xilinx 7-series** (XC7Z020 / ZC702, through the yosys + openXC7 path
this repo builds on). The only profile validated against a real flow and
real silicon.

* `maxMacroWritePorts = 1` — a `RAMB18E1`/`RAMB36E1` has **two** ports in
  total. yosys's `memory_libmap` serves a bank with more read sites than
  ports by *replicating* the bank, and every replica must carry every write
  port; a second write port therefore leaves no port for a read and the
  bank falls out of block RAM entirely. Measured, not reasoned: CapWalk
  CE10's `cell_flags` (3 reads + 2 writes) became "1024 `$dff` cells …
  3069 `$mux` cells" and cost 14× the LUTs of the fixed engine.
* `macroMinDataBits = 16384` — one `RAMB18E1`'s usable data capacity
  (parity bits not counted); D37's `bramDataBits`, whose boundary is the
  D30 evidence: 512×3 and 32×64 banks went `RAM*`, 512×32 and 512×64 went
  `RAMB*` (re-confirmed against yosys 0.33).
* `macroMinDepth = 0` — no separate depth floor is asserted; the capacity
  threshold accounts for every shape observed so far.
* images: block RAM `INIT_xx` are part of the bitstream and arrive;
  distributed RAM images do **not** arrive — that is D30, observed on the
  fabric as `-BADREF`. -/
def xc7 : MemTarget where
  name := "xc7"
  macroName := "block RAM"
  softName := "distributed LUT RAM"
  maxMacroWritePorts := 1
  macroMinDataBits := bramDataBits
  macroMinDepth := 0
  macroInitDeliverable := true
  softInitDeliverable := false

/-- **Lattice ECP5** (yosys + nextpnr-ecp5). Written from the DP16KD
datasheet characteristics; **nothing here has been run through nextpnr in
this repo**, so treat every number as a datasheet reading, not a
measurement.

* `maxMacroWritePorts = 1` — `DP16KD` is a true dual-port EBR: two ports in
  total, so the same replication argument as `xc7` applies. (Datasheet
  reading.)
* `macroMinDataBits = 16384` — an EBR is 18 Kbit, of which 16 Kbit is data
  in the ×1…×18 configurations. **TODO (unmeasured):** the *threshold* at
  which yosys prefers an EBR over PFU RAM on this target has not been
  measured; the xc7 heuristic ("a bank that does not fill one macro is
  predicted soft") is reused unchanged, which is conservative but is a
  guess about nextpnr's preferences, not a datasheet fact.
* `softInitDeliverable = false` — **TODO (unverified).** ECP5 distributed
  RAM (`DPR16X4`) is built from LUT INIT bits, which the bitstream does
  carry, so an image here might well survive where it does not on `xc7`.
  Whether the yosys/nextpnr flow actually propagates a Verilog `initial`
  image into a `DPR16X4` has not been checked. The value is set the
  conservative way (refuse) rather than the optimistic way, and this note
  is the reason it may be wrong. -/
def ecp5 : MemTarget where
  name := "ecp5"
  macroName := "EBR (DP16KD)"
  softName := "distributed LUT RAM (PFU DPR16X4)"
  maxMacroWritePorts := 1
  macroMinDataBits := 16384
  macroMinDepth := 0
  macroInitDeliverable := true
  softInitDeliverable := false

/-- **A generic compiled-SRAM ASIC flow** (an SRAM compiler such as OpenRAM
or a foundry's, plus standard cells). The profile the portability claim is
actually about: `realizableOn asicSram d` is what says a design is not
secretly FPGA-shaped.

* `macroInitDeliverable = false` and `softInitDeliverable = false` — **the
  ASIC rule, and the one certain entry in this profile.** An SRAM macro has
  no initial contents whatsoever: it powers up with whatever its cells
  settle to. A flop array *could* be reset to an image, but Loom emits a
  memory image as a Verilog `initial` block and emits no reset network for
  memories, so no image reaches a bank on this target by any route. A
  design that needs contents must write them from an explicit reset
  sequence — which is exactly the fix D37 already prescribes.
* `maxMacroWritePorts = 1` — the universally available compiler output is a
  single-port (1RW) macro. 1R1W and 2RW macros exist and are common, but
  assuming one is assuming a specific compiler; the conservative reading is
  the portable one.
* `macroMinDepth = 64` — **TODO (unsourced).** Compilers do have a minimum
  word count and an area crossover below which a flop array wins, but the
  number is foundry- and compiler-specific and no datasheet was available
  here; 64 words is a common floor, stated as a placeholder rather than a
  fact. It is low-stakes on this profile — neither realization delivers an
  image, so the classification does not change any verdict — and it is the
  field to fix first when a real PDK is in hand.
* `macroMinDataBits = 0` — no capacity floor asserted: on an ASIC the
  binding floor is depth, not total bits. -/
def asicSram : MemTarget where
  name := "asicSram"
  macroName := "compiled SRAM macro (1RW)"
  softName := "flip-flop array"
  maxMacroWritePorts := 1
  macroMinDataBits := 0
  macroMinDepth := 64
  macroInitDeliverable := false
  softInitDeliverable := false

/-- The profiles a report sweeps, in the order the table prints them. -/
def all : List MemTarget := [xc7, ecp5, asicSram]

/-- The target this repo builds for, and hence `Design.emit`'s default. -/
def default : MemTarget := xc7

end MemTarget

/-! ## Write ports of a memory -/

/-- How many write ports the compiled memory `m` uses: `Compile.numPorts`,
except that a memory no rule writes uses **zero** (`numPorts` reports one,
because the emitted module always declares at least one port). -/
def Design.writePortCount (d : Design) (m : String) : Nat :=
  if (Compile.designTrace d m).isEmpty then 0 else Compile.numPorts d m

/-- **The un-ackable, target-free half**: the write-port indices of memory
`m` strictly increase along the design's syntactic write order — the port
condition of `Compile.MemWriteWF`, which the compiler's memory correctness
theorem requires, and which `Compile.designWFCheck` asks of every memory.

Promoted here from `Machines/CapWalk/Engine.lean`, where the capability
engine had to write it by hand because two of its banks have two writers
(CAPWALK CE10). It belongs next to `Design.syncReadOkB`, not in one
machine. -/
def Design.memPortTraceOkB (d : Design) (m : String) : Bool :=
  decide ((Compile.designTrace d m).Pairwise (· < ·))

/-! ## Realizability -/

namespace MemTarget

/-- The realization class predicted for `md` in `d` **on this target**: the
one rule of `Loom/Hw/MemInitOk.lean`, with this profile's numbers and the
design's actual write-port count. -/
def familyOf (t : MemTarget) (d : Design) (md : MemDecl) : MemFamily :=
  predictedFamilyWith t.macroMinDataBits t.macroMinDepth t.maxMacroWritePorts
    md.addrWidth md.dataWidth (d.writePortCount md.name) (d.syncReadOkB md.name)

end MemTarget

/-- The image half of realizability, per memory: a written bank with a
non-zero reset image must land in a realization whose image this target
delivers. An unwritten bank is a ROM and is not examined (D37's rule 1,
universal). -/
def Design.memImageOkOn (d : Design) (t : MemTarget) (md : MemDecl) : Bool :=
  -- The middle disjunct is semantically redundant (`imageDelivered _ false`
  -- is `true`) and is a cost guard, as in D37: `familyOf` runs D19's
  -- `syncReadOkB` over every rule, and only a non-zero image can fail.
  !d.memWrittenB md.name || !md.imageNonZeroB
    || t.imageDelivered (t.familyOf d md) md.imageNonZeroB

/-- **The D38 check, per memory.** -/
def Design.memRealizableOn (d : Design) (t : MemTarget) (md : MemDecl) : Bool :=
  d.memPortTraceOkB md.name && d.memImageOkOn t md

/-- The memories of `d` that target `t` cannot realize, acknowledged or
not. -/
def Design.unrealizableOn (d : Design) (t : MemTarget) : List MemDecl :=
  d.mems.filter fun md => !d.memRealizableOn t md

/-- **The D38 check.** `true` iff every memory of `d` is realizable on `t`.
Ignores `ackMemInit`: this is the property, and `realizableAckOkB` is what
`Design.emit` enforces. So `d.realizableOnB .xc7 && d.realizableOnB .asicSram`
is the portability claim, as a Boolean anyone can run. -/
def Design.realizableOnB (d : Design) (t : MemTarget) : Bool :=
  (d.unrealizableOn t).isEmpty

/-- The offenders the design has *not* written down in `ackMemInit`. A
malformed port trace is never ackable — it is a compiler precondition, not
a mapping prediction — so only image offenders can be acknowledged. -/
def Design.unrealizableUnackedOn (d : Design) (t : MemTarget) : List MemDecl :=
  d.mems.filter fun md =>
    !d.memPortTraceOkB md.name
      || (!d.memImageOkOn t md && !d.ackMemInit.contains md.name)

/-- What `Design.emit` enforces: every offender is an acknowledged one. -/
def Design.realizableAckOkB (d : Design) (t : MemTarget) : Bool :=
  (d.unrealizableUnackedOn t).isEmpty

/-- The refusal: which memory, which target, why it cannot be realized
there, and what to do instead. -/
def Design.realizableError (d : Design) (t : MemTarget) (md : MemDecl) : String :=
  if !d.memPortTraceOkB md.name then
    s!"Design.emit: memory '{md.name}' has write-port indices that do not \
strictly increase along the design's write order \
({Compile.designTrace d md.name}). That is `Compile.MemWriteWF`'s port \
condition, which the compiler's memory theorem requires: two writes on one \
port in one cycle are not what the emitted module does. Fix: give each \
syntactic write site of the memory its own, ascending port index — or, \
better on target '{t.name}', mux the writers into ONE site (a bank with \
more than {t.maxMacroWritePorts} write port(s) does not fit \
{t.macroName}; Machines/CapWalk/CAPWALK_SPEC.md CE10 measured 14× the \
LUTs for exactly that mistake)."
  else
    s!"Design.emit: memory '{md.name}' declares a NON-ZERO reset image on a \
{2 ^ md.addrWidth}×{md.dataWidth} bank with \
{d.writePortCount md.name} write port(s), which target '{t.name}' realizes \
as {t.familyName (t.familyOf d md)} — a realization this target does not \
initialize. The image does not reach the hardware: the bank comes up \
ALL-ZERO (FPGA) or undefined (SRAM) while simulation and the proofs show \
the image (LOOM_GAPS.md D30 / D37 / D38, Machines/Epoch/EPOCH_SPEC.md \
E13). Fix: put the reset state in an explicit reset sequence (a sweep rule \
that writes the image after reset), or declare the image all-zero, or give \
the bank a shape this target keeps in {t.macroName}. If the loss is known \
and argued harmless, record it by name in the design's `ackMemInit`."

/-- A human-readable D38 report line for one memory on one target. -/
def Design.realizableReport (d : Design) (t : MemTarget) (md : MemDecl) : String :=
  s!"  {md.name}: {2 ^ md.addrWidth}×{md.dataWidth} \
wrPorts={d.writePortCount md.name} sync={d.syncReadOkB md.name} \
nonZeroInit={md.imageNonZeroB} on {t.name} → {t.familyName (t.familyOf d md)} \
ok={d.memRealizableOn t md}" ++
  (if d.ackMemInit.contains md.name then "  (ACK)" else "")

/-- One line per target: is `d` realizable on it, and which memories are
not. -/
def Design.targetReport (d : Design) : String :=
  String.intercalate "\n" <| MemTarget.all.map fun t =>
    let bad := (d.unrealizableOn t).map (·.name)
    s!"  {d.name} on {t.name}: realizable={d.realizableOnB t}" ++
    (if bad.isEmpty then "" else s!"  offenders={bad}")

/-! ## The `xc7` profile *is* D37's rule (no fork)

D37 states its deliverability rule once (`imageDelivered`) and its
prediction once (`predictedFamily`), and `Loom/Netlist/Mem.lean` calls the
former with the family it observed in a netlist. The two theorems below are
the standing evidence that D38 parameterized those statements rather than
copying them: on `xc7`, and at the one write port D37's port-blind
prediction assumes, the profile's answers are *definitionally* D37's. -/

theorem xc7_imageDelivered (fam : MemFamily) (nonZero : Bool) :
    MemTarget.xc7.imageDelivered fam nonZero = imageDelivered fam nonZero := by
  cases fam <;> cases nonZero <;> rfl

theorem xc7_familyOf (d : Design) (md : MemDecl)
    (h : d.writePortCount md.name ≤ 1) :
    MemTarget.xc7.familyOf d md = d.memFamilyOf md := by
  simp [MemTarget.familyOf, Design.memFamilyOf, predictedFamily,
    predictedFamilyWith, MemTarget.xc7, h]

/-- …and hence D38's image check on `xc7` is D37's, memory by memory, for
every bank D37 could see (one write port). -/
theorem xc7_memImageOk (d : Design) (md : MemDecl)
    (h : d.writePortCount md.name ≤ 1) :
    d.memImageOkOn MemTarget.xc7 md = d.memInitOkFor md := by
  simp [Design.memImageOkOn, Design.memInitOkFor, xc7_familyOf d md h,
    xc7_imageDelivered]

end Loom.Hw
