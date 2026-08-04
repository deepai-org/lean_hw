# LNP64-µ hardware implementation

The bounded LNP64-µ core is a direct Loom implementation of the cycle-level
machine: one hardware cycle corresponds to one specification cycle. The R-MC
result is therefore a plain forward simulation, not a timing abstraction.

## Encoding

Scalar specification fields map to fixed-width registers. Finite families of
domains, registers, slots, cells, regions, and gates use numbered register
families. Optional values use a validity bit plus payload. Main memory is a
Loom memory with explicitly ordered write ports.

The machine can issue a retiring core store, a mover data write, and a mover
status write in one cycle. The design assigns them to ordered ports matching
the specification phase order, so later-port collision behavior matches later
specification writes. `MemWriteWF` checks the constructed port trace.

The mover observes post-core-phase values that Loom expressions cannot read
directly because EDSL reads are pre-cycle. `SysOps.lean` therefore derives the
needed forwarded values explicitly, including same-cycle stores and changes to
capability and region state.

## Cycle structure

The ordered rules implement budget refill, instruction countdown/retirement
or fetch/decode/issue, one mover step, and the cycle tick. Decode uses the
fixed bounded instruction layout.

Capability revocation uses a hidden pointer-doubling mark engine rather than
an exponentially duplicated combinational tree. The abstraction erases this
implementation state; the bounded convergence and retirement proof connects
it to the specification result.

## Verification

`Tests/Lnp64uCore.lean` checks cycle-by-cycle full-state lockstep against the
ISS for base and system-operation manifests. The R-MC theorem proves
`Simulation (machine m) (core m).toTSys` through the field abstraction and
transports invariants to the implementation.

Artifact checks are available through the normal emitter and
`scripts/lockstep_lnp64u.sh`. The latter is intentionally outside the fast CI
path because the generated core and synthesis check are large.

This is a finite verification target. Its fixed domain/table/address bounds
are part of the theorem statement and should not be generalized to an
unbounded implementation.
