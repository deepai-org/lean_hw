-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.MemoryClass
import Loom.Hw.Compile
/-!
# Target-parameterized memory diagnostics

A `MemTarget` is ordinary engineering data describing a possible memory
technology: macro thresholds, write-port budgets, initialization support, and
report names. `Design.realizableOnB` evaluates a design against an explicitly
chosen profile.

These checks predict a realization; they do not control synthesis, interpret
a mapped netlist, or prove that a physical target implements the prediction.
Vendor-named profiles are optional data points and do not affect the design's
transition semantics or compiler-correctness theorems.
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

/-- Deliverability of an image by implementation class. -/
def initDeliverable (t : MemTarget) : MemClass → Bool
  | .macro => t.macroInitDeliverable
  | .soft => t.softInitDeliverable

/-- The target's name for a realization class. -/
def className (t : MemTarget) : MemClass → String
  | .macro => t.macroName
  | .soft => t.softName

/-- **The deliverability rule (D30/D37), read through the profile**: the
image arrives iff it is all-zero — which every realization delivers — or
the realization it sits in is one this target initializes. -/
def imageDelivered (t : MemTarget) (cls : MemClass) (nonZero : Bool) : Bool :=
  !nonZero || t.initDeliverable cls

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

/-- The implementation class predicted for `md` in `d` on this target. -/
def classOf (t : MemTarget) (d : Design) (md : MemDecl) : MemClass :=
  predictedClassWith t.macroMinDataBits t.macroMinDepth t.maxMacroWritePorts
    md.addrWidth md.dataWidth (d.writePortCount md.name) (d.syncReadOkB md.name)

end MemTarget

/-- The image half of realizability, per memory: a written bank with a
non-zero reset image must land in a realization whose image this target
delivers. An unwritten bank is a ROM and is not examined (D37's rule 1,
universal). -/
def Design.memImageOkOn (d : Design) (t : MemTarget) (md : MemDecl) : Bool :=
  -- The middle disjunct is semantically redundant (`imageDelivered _ false`
  -- is `true`) and is a cost guard: `classOf` runs D19's
  -- `syncReadOkB` over every rule, and only a non-zero image can fail.
  !d.memWrittenB md.name || !md.imageNonZeroB
    || t.imageDelivered (t.classOf d md) md.imageNonZeroB

/-- **The D38 check, per memory.** -/
def Design.memRealizableOn (d : Design) (t : MemTarget) (md : MemDecl) : Bool :=
  d.memPortTraceOkB md.name && d.memImageOkOn t md

/-- The memories of `d` that target `t` cannot realize, acknowledged or
not. -/
def Design.unrealizableOn (d : Design) (t : MemTarget) : List MemDecl :=
  d.mems.filter fun md => !d.memRealizableOn t md

/-- **The D38 check.** `true` iff every memory of `d` is realizable on `t`.
Ignores `ackMemInit`: this is the property, and `realizableAckOkB` is what
an explicit target check enforces. So
`d.realizableOnB targetA && d.realizableOnB targetB`
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

/-- What `Design.checkTarget` enforces: every offender is acknowledged. -/
def Design.realizableAckOkB (d : Design) (t : MemTarget) : Bool :=
  (d.unrealizableUnackedOn t).isEmpty

/-- The refusal: which memory, which target, why it cannot be realized
there, and what to do instead. -/
def Design.realizableError (d : Design) (t : MemTarget) (md : MemDecl) : String :=
  if !d.memPortTraceOkB md.name then
    s!"Design.checkTarget: memory '{md.name}' has write-port indices that do not \
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
    s!"Design.checkTarget: memory '{md.name}' declares a NON-ZERO reset image on a \
{2 ^ md.addrWidth}×{md.dataWidth} bank with \
{d.writePortCount md.name} write port(s), which target '{t.name}' realizes \
as {t.className (t.classOf d md)} — a realization this target does not \
initialize. The image does not reach the hardware: the bank comes up \
ALL-ZERO (FPGA) or undefined (SRAM) while simulation and the proofs show \
the image (Loom/Hw/MEMTARGET_SPEC.md, Machines/Epoch/EPOCH_SPEC.md \
E13). Fix: put the reset state in an explicit reset sequence (a sweep rule \
that writes the image after reset), or declare the image all-zero, or give \
the bank a shape this target keeps in {t.macroName}. If the loss is known \
and argued harmless, record it by name in the design's `ackMemInit`."

/-- A human-readable D38 report line for one memory on one target. -/
def Design.realizableReport (d : Design) (t : MemTarget) (md : MemDecl) : String :=
  s!"  {md.name}: {2 ^ md.addrWidth}×{md.dataWidth} \
wrPorts={d.writePortCount md.name} sync={d.syncReadOkB md.name} \
nonZeroInit={md.imageNonZeroB} on {t.name} → {t.className (t.classOf d md)} \
ok={d.memRealizableOn t md}" ++
  (if d.ackMemInit.contains md.name then "  (ACK)" else "")

end Loom.Hw
