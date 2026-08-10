# LNP64mini architectural extensions

This file records the current contract for the bounded LNP64 mechanisms in
`Core.lean`. It is a specification and acceptance index, not a development
diary. The definitive instruction encodings remain in the LNP64 ISA sources;
`scripts/check_isa_agreement.py` checks the shared opcode surface.

## Scope

LNP64mini is a board-sized integration machine. It implements enough of the
architecture to exercise preemption, protection domains, fail-stop behavior,
parking and waking, gate crossings, capability transfer, translation, commit
tracing, caches, dual-core execution, and a real NetBSD network workload. It
does not claim the complete LNP64 profile or production performance.

All extensions must preserve:

- the certified Design-derived simulator as the primary executable model;
- explicit architectural outcomes and emitted-RTL comparison;
- emitted-RTL simulation for the affected path;
- declaration-derived state and comparison coverage;
- explicit memory, CDC, and target boundaries; and
- the accepted dual-core board workload when board integration changes.

Passing opcode agreement or a sampled differential alone is insufficient.

## EXT-1: preemption

The quantum counter requests a scheduler transition only at an architecturally
safe boundary. A switch preserves the outgoing thread's resume PC and restores
the selected thread's state. Directed tests cover no-switch and forced-switch
cases; observed switches are audited through typed state coordinates.

## EXT-2: protection domains

Each live thread carries a domain identity. Ordinary scheduling preserves it;
only a declared gate crossing changes the running domain. Domain state is part
of the generated comparison surface and is not reconstructed from host-side
metadata.

## EXT-3: fail-stop and poison

Detected fail-stop conditions latch a named cause and prevent ordinary forward
progress until the defined recovery/reset action. Debug observability is a
derived external view and does not add a second transition semantics.

## EXT-4: park and wake

Parking records the continuation required to resume a thread. Wake may be
spurious where the ISA permits it, but it must not corrupt the resume PC,
domain, gate depth, or gate continuation stack. The generic
`TransitionProperty` machinery proves this preservation for every slot and
stack depth.

## EXT-5: gates

A gate descriptor in memory supplies the destination domain and entry point.
Invalid descriptors fail closed. Gate entry pushes a bounded continuation
frame; gate return pops it. Nested gates are supported up to the declared
depth. Clone and park operations inside a gate must preserve the parent's
continuation and give a newly allocated thread clean gate state.

The sentinel ABI makes a gate handler an ordinary function: return from the C
handler reaches the machine gate-return sentinel, rather than depending on a
special compiler epilogue. The current board workload exercises the write
handler through gate 1/domain 1.

## EXT-6: capability transfer

Capability send and receive operate on the in-memory domain inbox. Occupancy
and validity are checked by the machine; clearing the relevant memory entry
revokes the transfer path. The receiving identity is the running domain, not
an untrusted operand naming another domain.

## EXT-7: translation and authority windows

The bounded VMA/TLB path translates declared guest regions and fails closed on
invalid or revoked entries. Guest-to-physical mapping is shared by image load,
debug access, trap response, and board readback rather than reimplemented at
each call site. DMA windows are separately revocable authority, not an
identity-mapping shortcut. External DDR, PS7 behavior, and host conversion of
an image into physical bytes remain outside the Lean proof.

## EXT-8: commit tracing

The commit ring records the retiring opcode, PC, and writeback observation
through the same retirement choke point used by the core. Capture is scalar;
a single drain rule writes the trace memory, preserving the declared
single-write-port shape. The trace-valid signal is a pulse, and directed tests
check useful ordering and payloads rather than merely comparing two models.

Trace storage and BSCAN transport are diagnostic evidence and are not part of
the architectural state promised by the ISA.

## EXT-9: caches

The instruction and data caches use declared synchronous memories and retain
the uncached/translated access boundary. Directed checks cover cold fill,
hit, conflicting tags, store invalidation, subword access, and the relevant
atomic and futex interactions. A design that cannot meet its declared memory
profile must fail before board emission; actual RAM mapping and timing remain
external evidence.

The dual-core design does not claim a general cache-coherent weak-memory
system. Any shared-cache behavior used by the board workload must be explicit
in `DUAL_SPEC.md` and the wrapper/evidence layer.

## Current board evidence

One accounted current-head artifact completes the full dual-core NetBSD
mission workload:

- direct generic 64-bit `MUL` executes correctly in the kernel;
- ping completes 4/4;
- `uname` and `echo e2e-ok-through-gate` return through gate 1/domain 1;
- the shmif driver uses the domain-2 path;
- the sentinel gate ABI and CDC snapshot structure coexist in the same
  bitstream; and
- the accepted guest uses roots `0x913000` and core-1 entry `0x8cae00`.

The accepted openXC7 build uses `-nodsp`: 59,035 of 106,400 LUTs (55%),
routing iteration 17, and reported `sysclk` maximum 32.86 MHz. The installed
openXC7 0.8.2 rejects a legal unused terminal DSP48 `PCOUT`; DSP-enabled
mapping is therefore an unaccepted optimization path, not part of the current
board claim.

These observations corroborate the integration artifact. They do not prove
synthesis, placement, routing, the bitstream, PS7, DDR, Ethernet, analog CDC,
or behavior outside the exercised workload.

## Out of scope

LNP64mini does not currently promise floating-point or vector profiles, an
unbounded capability table, a general coherent memory system, the full Mover
architecture, production MMU performance, or timing-independent multiclock
composition. Those require separate Designs, contracts, and acceptance work.

## Acceptance commands

The maintained repository gates are indexed by `STATUS.md` and
`REPRODUCING.md`. Machine-specific acceptance includes the core selftests,
opcode agreement, generated-coordinate coverage, emitted-RTL checks, memory
target checks, and the board ladder in `fpga/zc702/README.md`.
