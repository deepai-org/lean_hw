# Multiclock Loom

Loom composes ordinary synchronous `Design` islands through typed channels.
Cycle-sensitive logic stays inside an island; the System layer defines clock
schedules, reset policy, communication, realization, and composition proofs.

## Application model

Design authors need five concepts:

1. `hardware` defines an ordinary single-clock island.
2. `clock` places it in a named domain.
3. `channel` declares a typed logical queue.
4. `send` and `receive` transfer values without exposing raw handshakes.
5. `realize` selects a certified synthesizable crossing implementation.

```lean
system twoClock where
  clock clkA
  clock clkB
  clocks Clock.asynchronous
  reset Reset.together
  channel q : 8 depth 2

  island producer on clkA where
    output reg sent : 1
    rule transmit :=
      if ~sent then
        send 42 to q then sent <- 1

  island consumer on clkB where
    output reg got : 8
    rule accept :=
      receive value from q then got <- value

  connect q from producer to consumer
  realize q with Cdc.grayFifo
```

From this declaration Loom derives the checked `System`, endpoint adapters,
island certificates, realization, executable schedule replay, readable views,
crossing inventory, timing contract, and neutral physical requirements.
Application authors do not construct Gray pointers, refinement proofs, storage
witnesses, or lookup equalities.

Packed structs work as channel payloads and retain their nominal type at the
endpoints; CDC logic sees only their canonical packed bits.

## Clocks and schedules

The stock relations are:

| Relation | Admitted events |
| --- | --- |
| `Clock.asynchronous` | arbitrary phase, including coincident edges |
| `Clock.interleaved` | at most one named clock ticks per event |
| `Clock.aligned a b` | `a` and `b` tick together |
| `Clock.alignGroups base groups` | alignment within groups; `base` elsewhere |

`ClockEvent` and finite schedules are executable objects used by proofs,
simulation, replay, and bounded checks. Alignment is a semantic schedule
assumption, not proof of a physical clock relation. Differently named clocks
still require a CDC realization even if their schedules are aligned.

`Application.run` and `runCompact` execute a selected schedule. Kernel theorems
relate both to `System.runPrefix`; schedule seeds are replay metadata, not an
alternative semantics.

## Channel behavior and timing

An accepted payload is neither duplicated nor silently lost, remains FIFO
ordered, and is owned by exactly one source stage, queue slot, or destination
presentation point. These are safety properties and do not assume clocks keep
ticking.

Timing is explicit. `send` attempts acceptance on a source tick; it does not
promise same-event delivery. A realization reports endpoint stages,
synchronizer/storage stages, issue interval, co-tick policy, recovery effects,
and whether a finite bound requires a progress premise. Bounds use local clock
ticks, grants, or named events—not an invented global cycle or nanoseconds.

The compatible conservative sink accepts at most one item per two destination
ticks. `addFullRateChannel` selects the proved two-entry registered
presentation path, which sustains one item per destination tick after filling
without a combinational CDC path. Both implement the same abstract channel;
the selected artifact reports which timing contract applies.

Safety does not imply liveness. `TraceContract.BoundedService` states explicit
service assumptions and composes serial bounds by addition and independent
parallel bounds by maximum.

## Realizations

| Selection | Use |
| --- | --- |
| `Cdc.synchronousFifo` | same named physical clock; positive depth |
| `Cdc.grayFifo` | unrelated clocks; power-of-two depth of at least two |
| `Cdc.recoverableGrayFifo` | Gray FIFO with independent-flush recovery |

The portable asynchronous path is compiler-produced from ordinary per-domain
Designs: Gray-pointer control, two-stage synchronizers, endpoint presentation,
and neutral register-bank storage. It is suitable as a portable reference for
FPGA and ASIC synthesis. Larger designs may substitute a checked target RAM or
synchronizer binding without changing channel semantics or application logic.
Such a leaf remains an explicit external assumption unless separately proved.

Realization is total and explicit: every connection is selected exactly once,
and clock, reset, width, depth, storage, and endpoint incompatibilities fail
closed. Technology-specific profiles live under `Evidence/`, not generic
`Loom.Hw` APIs.

## Reset and recovery

`Reset.together` is the ordinary policy: the System starts from coordinated
reset before scheduled execution. Generated RTL currently uses active-high
synchronous reset per domain, so each domain must tick while reset is asserted;
release is sampled independently.

`Reset.independentFlush` is for deliberate reset of one island while neighbors
continue. Its protocol blocks traffic, drains or explicitly discards incident
traffic, resets both affected channel halves, and resumes only after a visible
completion handshake. The request is a level held until `recovered`, and
participating clocks must continue ticking. Loss is reported as discarded
traffic rather than mislabeled as delivery.

Reset delivery, synchronizer placement, clock availability, and electrical
behavior remain physical obligations. The generated reset intent records what
a backend must implement.

## Proof reuse and hierarchy

An island remains a plain `Design`, so its local invariants use the ordinary
single-clock proof tools. `liftIsland` transports them to System properties
quantified over every admitted schedule. Channel lemmas provide capacity,
ordering, conservation, and bounded-service facts for cross-island proofs.

Reusable `SystemFragment`s carry typed clocks, islands, channels, realizations,
and certificates. Compatible parents project their finite executions to the
fragment execution, allowing fragment safety and conditional-progress theorems
to be reused without flattening. Sibling placement is order-independent;
duplicate or incompatible inventories fail closed.

`System.InterfaceProof` seals application-level observations and trace
contracts for hierarchical reuse. External implementations may replace a
certified reference island only through a checked contract and exact byte
identity; simulation and proofs continue to use the reference Design, and the
external implementation assumption stays visible.

## Physical obligations

For every crossing, Loom emits a typed, technology-neutral manifest covering:

- endpoint clocks and synchronizer stages;
- Gray-bus launch/capture paths and period-relative delay/skew requirements;
- preservation/placement intent;
- reset behavior and domain association;
- storage presentation and target-leaf assumptions; and
- exact RTL/object identities.

A backend reports every required item as `PASS`, `FAIL`, `SKIP`, or
`UNCONSTRAINED`. Missing, duplicated, stale, or unresolved requirements cannot
produce signoff. A small reference backend checks this coverage contract;
target-specific XDC/SDC rendering and routed-tool interpretation remain
external integrations.

Loom proves the digital channel/control behavior and Gray-code adjacency. It
does not prove metastability resolution, MTBF, placement, timing closure,
vendor/foundry memories, or a tool's interpretation of constraints. The exact
boundary is in [`MULTICLOCK_BOUNDARY.md`](MULTICLOCK_BOUNDARY.md).

## Examples

- Small authored two-clock system:
  [`Machines/Substrate/TwoClock.lean`](Machines/Substrate/TwoClock.lean)
- Production-scale integration:
  [`Machines/Lnp64mini/Multiclock.lean`](Machines/Lnp64mini/Multiclock.lean)
- Typed reusable SoC composition:
  [`Machines/Multiclock/TypedSoCTile/Design.lean`](Machines/Multiclock/TypedSoCTile/Design.lean)
- Formal and silicon CDC gauntlets:
  [`Machines/Multiclock`](Machines/Multiclock)

Start with the small example. Use expert refinement/storage APIs only when
providing a custom realization.
