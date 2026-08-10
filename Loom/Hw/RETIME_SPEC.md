# Verified retiming primitive

`Loom/Hw/Retime.lean` implements a deliberately restricted retiming
transformation for write-only registers.

`retimeReg d r w` adds `r__pre`, redirects writes to it, and appends a rule
that copies it into `r`. This cuts the combinational path feeding `r` and
delays its externally visible stream. It is suitable for observability and
other registers that the original design never reads.

## Legality

`RetimeLegal` and `retimeRegOkB` require the named register and width to
match, the generated name to be fresh, and neither the original register nor
the generated register to violate the proved no-read/no-conflict class.
Expression and action traversals provide the corresponding read/write checks.

## Proof

`retimeReg_simulation` is a strict forward simulation, and
`retimeReg_stutter` derives the stuttering simulation used to transport
invariants. The abstraction projects the new pre-register value into the
specification register and erases the implementation-only coordinate. This
choice accounts for Loom's pre-cycle read semantics.

`RetimeCut` and `retimePlan` lift the primitive to an ordered set of selected
cuts. `RetimePlanLegal` is indexed by every intermediate design, so a later
freshness/read check cannot accidentally ignore names or copy rules introduced
by an earlier cut. `retimePlan_stutter` composes the per-cut proofs into one
simulation, and `retimePlanAbs` exposes its state abstraction. Typed register
handles construct cuts with `RetimeCut.ofReg`.

`Machines/Substrate/RetimeDemo.lean` exercises the theorem on a write-only
observation latch. `scripts/retime_demo.sh` checks the expected one-cycle
artifact delay with Icarus Verilog when that optional tool is available.

The companion `Loom/Hw/Fanout.lean` provides the other implemented W3
primitive: selected consumer rules may read a fresh register replica while
producer writes are mirrored to both copies. Its proof uses an explicit
coherence invariant and a forward simulation over the implementation's
reachable state space; arbitrary hand-constructed incoherent states are not
silently included in the claim. `duplicateFanoutReg` derives the source width
from its typed handle, and `duplicateFanoutOkB_sound` proves that the
executable guard supplies exactly the legality witness used by the semantic
theorems. `Machines/Substrate/FanoutDemo.lean` and
`scripts/fanout_demo.sh` carry that result through emitted RTL: the testbench
checks visible-state agreement and replica coherence, then reports generic
synthesis measurements. With Yosys 0.33 the equivalent flops are merged (421
cells and 149 flops in both designs), so the proof establishes refinement but
does not claim that an unconstrained synthesis flow preserves the physical
replica. The same script applies a checked `keep` selection to both source
flops; this retains distinct replicas and reduces their maximum cell-input pin
loads from 15 to 9/8 at a measured cost of 482 cells and 172 flops. These are
synthesis measurements, not a timing theorem or post-place result.

The retiming primitive is not a general retimer. A plan covers several independent
write-only cuts, but does not yet insert several stages along one cone. It also
does not cover registers read by the original design, arbitrary pipeline
balancing, throughput equivalence, or cycle-accurate timing properties. Those
require a richer abstraction and separate proofs.
