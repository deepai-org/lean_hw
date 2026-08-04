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

`Machines/Substrate/RetimeDemo.lean` exercises the theorem on a write-only
observation latch. `scripts/retime_demo.sh` checks the expected one-cycle
artifact delay with Icarus Verilog when that optional tool is available.

The primitive is not a general retimer. It does not cover registers read by
the original design, arbitrary pipeline balancing, throughput equivalence, or
cycle-accurate timing properties. Those require a richer abstraction and
separate proofs.
