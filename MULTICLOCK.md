# Multiclock Loom

Loom's multiclock layer composes ordinary synchronous `Design`s. It does not
replace their cycle semantics and does not require elastic logic inside an
island.

## Intended application API

Loom's implementation is necessarily complex. Using a certified multiclock
channel should not be. A design author should need five concepts:

- **hardware**: an ordinary synchronous `Design` remains the unit of logic;
- **clock**: an island is placed in a named clock domain;
- **channel**: `Chan w` is a typed logical queue between islands;
- **send/receive**: generated endpoint operations move values without exposing
  raw valid/ready wiring; and
- **realize**: the application selects a certified synthesizable crossing
  implementation, with Loom's portable implementation as the stock choice.

`System.Invariant` and `System.liftIsland` are proof concepts, not concepts a
designer must learn before sending one value. Moving an island from one clock
to another should change its clock annotation, not its implementation or
existing local proofs.

`ClockHandle`, `IslandHandle`, and `ChannelRoute` keep application topology
out of raw strings. `Chan.SourceEndpoint` exposes only `canSend`/`send`, while
`Chan.SinkEndpoint` exposes only `hasData`/`data`/`consume`.
`SystemBuilder.addChannel` connects typed island handles and generates their
endpoint adapters. The completed declaration may call `System.realizePortable`
for one portable choice everywhere, or `System.realizeWith` with a total
`RealizationPlan`. A plan starts from a default and overrides typed
`ChannelRoute`s, so every declared connection is selected exactly once without
spelling a channel name. Loom currently supplies three closed compiler-produced
choices: the ordinary synchronous FIFO for aligned endpoints, at every
positive depth, and the portable Gray FIFO for unrelated clocks at arbitrary
power-of-two depths, either with coordinated reset or with the compiled
four-phase independent-recovery wrapper. `Chan.send`, `canSend`, `hasData`, `data`, and `consume`
provide the application vocabulary without exposing the generated handshake.

Dedicated `system ... where` or `#run_system` syntax remains optional
prettification. The mechanical API does not depend on it.

The ordinary-Lean shape (with island bodies abbreviated) is:

```lean
def tx := q.source
def rx := q.sink

def producer : Design := -- uses tx.canSend and tx.send
  ...

def consumer : Design := -- uses rx.hasData, rx.data, and rx.consume
  ...

def clkA : ClockHandle := .named "clkA"
def clkB : ClockHandle := .named "clkB"
def producerIsland : IslandHandle := .named "producer" producer clkA
def consumerIsland : IslandHandle := .named "consumer" consumer clkB

def builder : SystemBuilder :=
  System.empty
    |>.addIsland producerIsland
    |>.addIsland consumerIsland
    |>.addChannel (q.between producerIsland consumerIsland)
    |>.withClockRel .asynchronous

def system : System := builder.certify (by decide)
def application : System.Application system :=
  system.realizeWith RealizationPlan.portable (by decide)

def result := application.run schedule
#eval application.readReg result consumerIsland received
```

The two proofs shown are executable structural/readiness gates. Generator and
interactive code can instead call `realizePortableChecked` to receive a named
readiness report. They do not
ask the application to construct a refinement, certificate, storage witness,
or artifact-coverage theorem.

`PackedChan alpha` follows the same topology and per-route realization path. Its
directional endpoints accept and return `PackedExpr alpha`; the CDC machinery
sees only the canonical `HwPacked.width alpha` bits. A record payload therefore
does not create a parallel multiclock semantics or emitter. Packed hierarchical
exports retain `alpha`, so unrelated equal-width record types cannot be joined
at a block boundary.

Large assemblies may define `system.certifyIslands` once and pass the result
to `realizeWithCertified`. Changing FIFO choices then reruns only the reset,
connection, and clock-rule gates; cached island compiler/DAG certificates are
reused. `realizeWithChecked`, `selectedReadinessReport`, and the stock checked
entry point report the precise island, channel, clock mismatch, depth, or
generated component that failed.

Independent-reset applications use `Application.runRecovery` and
`runRecoveryChecked`. These retain the same certified DAG island states as
ordinary replay; projecting the result is proved equal to
`System.runRecoveryPrefix` on the identical event and input trace.

Ordinary `Application.run` has the public equality theorem
`run_semantic_eq`. Long campaigns may call `runCompact`: its result retains
only flat certified island states, abstract channels, and event time. The
kernel theorem `runCompact_agrees` relates every declared island coordinate
and the complete channel graph to the ordinary `System.runPrefix` result; it
is not an unchecked comparison or a second simulator.

## Progressive disclosure

Application authors define ordinary hardware, assign clocks, declare channels,
send and receive values, and select a realization. They should receive the
checked `System`, generated endpoints, stock realization, certified artifact,
readable inspection views, and replay entry point from that declaration.

Verification authors additionally use `System.Invariant`, `liftIsland`, and
channel/trace theorems. Schedules remain implicit except when deliberately
recording or replaying a particular execution.

Every `system ... where` connection also generates a stable proof handle such
as `chip.qConnection`. The handle closes the checked connection lookup once;
application theorems call `chip.qConnection.capacity`, `.safety`, or
`.traceConservation` without naming generated registers, constructing a
`SystemConnection`, or proving `find? = some ...`. The `.safety` theorem
packages capacity with the exact valid/payload presentation supplied to the
consumer at every reachable state.

`Loom.Hw.ChannelProtocol` is the deeper compositional layer. Its ownership
ledger assigns each in-flight payload to exactly one of destination
presentation, unreserved FIFO storage, or source staging. An outstanding
conservative pop is an acknowledgement debt, not a second copy of the FIFO
head. `OwnershipStep.comp` and `runLedger_conservation` therefore compose
accepted/consumed trace theorems across larger blocks without double-counting
endpoint state. `SourceEndpointCertificate` and `SinkEndpointCertificate`
state the local checked refinement of the exact `withSource`/`withSink`
`Design.cycleOpen`; their input assumptions are explicit. A
`RegisteredEndpointBinding` discharges those assumptions at System assembly
and derives the reachable registered-endpoint coherence invariant. Custom
endpoint libraries use this expert layer; ordinary application logic does not.
`System.InterfaceProof` is the sealing surface for larger designs: it bundles a
schedule-quantified safety invariant with application-level input/output trace
observations and a `TraceContract`. Its `comp` combinator hides the shared
intermediate transaction sequence and conjoins the two safety theorems.

Bounded progress remains separate from safety. `TraceContract.BoundedService`
names its service unit and supports serial addition of bounds, parallel maximum
of independent bounds, and explicit weakening. Loom does not infer progress
from the existence of a FIFO or hide a grant/fairness premise.

CDC realization experts may inspect generated controls and replace the stock
binding with a `Chan.Refinement`. Gray pointers, synchronizer stages, storage
contracts, lookup equalities, coverage proofs, and physical assumptions belong
at this level. Complexity remains accessible without being compulsory.

## Guarantees

A checked `System` guarantees:

- islands remain ordinary synchronous `Design`s;
- cross-domain application communication is declared through typed channels;
- unticked islands retain their state;
- ordinary island invariants lift over every admitted schedule;
- abstract channels preserve capacity, FIFO order, and accepted data;
- physical emission has exactly one selectable, refinement-backed realization
  for every declared connection;
- a certified realized artifact carries reset-policy/binding compatibility as
  a constructor proof, so an invalid mixture cannot be packaged before IO;
- RTL and the readable crossing/constraint reports cover the same ordered
  connection set; and
- a same-clock System lowers through the existing `Design` composition path.

`ClockRel.asynchronous` admits arbitrary phase, including coincident unrelated
edges represented by one multi-clock event. Proofs that intentionally
linearize every edge use the explicitly narrower `ClockRel.interleaved`.

The stock portable realization now derives exact neutral physical intent for
its two ordered synchronizer chains and both Gray buses, including period-
relative skew and datapath bounds. This is a requirement manifest, not a claim
that a backend honored it. A target adapter must report each requirement as
`PASS`, `FAIL`, `SKIP`, or `UNCONSTRAINED`; physical signoff is incomplete
until all required items pass. The same typed manifest now includes the exact
per-domain reset behavior of the generated RTL. A small reference backend
proves the coverage interface can consume every timing and reset requirement
without omission; it is not a target signoff result. Target reports bind every
result to one device/tool/version/run identity and to SHA-256 identities for
the theorem-bound RTL, physical-intent bytes, emitted target constraints, and
routed design. The implementation report must independently record the same
RTL and constraint input hashes. Required generated objects must resolve in
the post-synthesis namespace. Mixed, incomplete, or stale evidence is
therefore rejected even when every imported status says `PASS`.

The intended deployment modes share identical channel source code. Fully
neutral mode uses compiler-generated register storage on FPGA or ASIC. A
target-refined profile may substitute compatible FPGA RAM/synchronizer
resources or ASIC SRAM/synchronizer cells while recording explicit assumptions
and checking configuration compatibility. Those choices never enter `Design`
semantics or application hardware logic. Generated physical metadata lists
each such assumption against its exact connection and states explicitly that
RTL generation or successful target-cell inference does not discharge it.

Concrete evidence profiles may additionally impose an executable,
fail-closed target-selection policy without changing the generic leaf
contract. Qualification keys include the exact device, tool and version,
primitive mode, width/depth and storage configuration, read-presentation
contract, and clock relationship; changing any field invalidates the result.
Simulation, inference, routing, and silicon remain distinct claim stages. For
example, the repository's openXC7/Zynq-7000 profile rejects independent-clock
inferred storage wider than 36 bits after the recorded 46-bit 72-mode failure.
Passing that conservative selection gate only avoids a known-bad mode; it does
not turn the leaf's external assumption into a Loom theorem.

An optional openXC7 routed adapter lives under `Evidence`, never under generic
`Loom.Hw`. It resolves and audits routed synchronizer objects and binds reports
to exact input artifacts. Invoke it as `lake exe
openXc7ClockGauntletSignoff -- EVIDENCE_DIRECTORY RUN_ID SEED TOOL_VERSION`;
the audit must record the exact RTL and generated-constraint input hashes.
Since openXC7 0.8.2 cannot consume the required
asynchronous-group and period-relative Gray-bus delay/skew intent, those rows
remain `UNCONSTRAINED` and the adapter correctly refuses full signoff. This is
a tested extension boundary, not a dependency on openXC7.

`TraceContract` is an optional schedule-free relation for application proofs
that connect consumed and produced traces. Its `deliveredWithin` relation
states an explicit service bound over cumulative count traces, and serial
composition adds bounds. The application chooses the service unit (for
example, destination ticks or grants); Loom does not infer liveness merely
because a channel exists. None of this is required to create an island or use
`liftIsland`.

## Timing is part of the interface

`send` means “attempt this transfer on the source island's current tick”; it
does **not** promise that the value is visible at the destination on that tick.
Likewise, `consume` acts on a value already visible at the sink. FIFO depth,
registered stages, pointer synchronization, backpressure, arbitration, and
the admitted clock schedule can all change the interval between acceptance
and delivery.

The realization layer therefore exposes a machine-readable timing description
for every selected channel implementation. A description distinguishes:

- an exact number of source or destination ticks;
- a finite bound under explicit service premises, such as “the destination
  ticks and consumes whenever data is available”; and
- no finite bound under the chosen `ClockRel`.

Bounds are stated in clock-domain ticks, grants, or named System events—not in
an invented global cycle and not in nanoseconds. Physical time follows only
after clocks and timing closure are supplied externally. The selected
realization report shows source/sink endpoint registers, synchronizer and
storage stages, local issue intervals, the relevant co-tick behavior, and any
recovery interruption. Verification code may turn the same contract into
`deliveredWithin` theorems, and serial composition adds proved bounds.
Connecting or realizing a channel must never introduce a hidden latency absent
from that report.

`Application.timingFor` exposes the selected typed description and
`timingReport` renders an on-request human diagnostic. Normal emission creates
no CSV/TSV sidecars: it writes `crossings.md` and `clock_constraints.md` for
human review, while programs inspect the typed inventory directly. The
structured timing list's connection-key
coverage is proved identical to the checked crossing inventory. An expert
binding without a timing description fails emission. Structural stage counts
and the stock endpoint issue facts are derived from the selected generated
circuit. A positive end-to-end finite delivery number is intentionally absent
for the portable async FIFO because its proved synchronizer model permits
unbounded staleness. `TraceContract.deliveredWithin` remains the theorem-level
foundation for stronger application-specific progress assumptions.

The conservative endpoint cost is explicit rather than hidden: `send` uses one
registered source-offer stage and can issue every ready source tick, while the
registered `consume` request forces a bubble and can consume at most once per
two destination ticks even under continuous validity. It remains the default
for compatibility. Throughput-sensitive designs may select
`addFullRateChannel`, whose destination-local two-entry presentation buffer has
a conservation theorem, no combinational CDC path, and a one-item-per-
destination-tick steady-state theorem. The selected certified artifact reports
the corresponding one-tick issue interval. This is an endpoint presentation
choice, not a different abstract channel or target-specific FIFO.

## Reset and recovery contracts

“Recovery” here has one narrow meaning: one clock island is deliberately reset
while neighboring islands continue running. The stock protocol first blocks
new traffic, brings both ends of every incident channel to a common flush
point, discards the explicitly reported old epoch, resets the affected island
and channel halves, and then returns them to service. It is not ordinary FIFO
latency and is irrelevant to designs that use only coordinated whole-system
reset.

The default physical policy is explicitly `SystemResetPolicy.coordinated`:

- every island and abstract channel enters reset together;
- reset is released together before scheduled execution; and
- delaying an island's first clock tick does not mean it remains in reset.

`SystemResetPolicy.independentFlush` is now a separate executable semantic
contract. `RecoveryEvent` names reset islands alongside a clock event. Reset
dominates a simultaneous tick, every incident queue is empty after the event,
queued and same-event incident traffic is explicitly discarded, and
nonincident channels continue normally. Coordinated Systems reject live-reset
events; independent Systems validate names and replay the same executable event
objects. `channelCapacityRecoveryInvariant` proves capacity under every legal
recovery trace.

`RealizationPlan.recoveryPortable` selects the stock independent-recovery path.
For every incident channel it structurally joins the portable FIFO to two
compiler-produced endpoint controllers and compiler-produced traffic/reset
guards. The generated top exposes level `recover`/`recovered` ports per island,
ANDs completion across all incident endpoints with a compiled coordinator
cell. Each incident channel contributes both physical endpoint halves; the
requested island resets only after every one has quiesced.
Each FIFO half is held in reset throughout its endpoint's `flushed` phase.
This prevents an early-reset half from sampling the peer's pre-reset pointer;
release then uses the FIFO's proved independently delayed release discipline.
The request must remain asserted until `recovered`; participating clocks must
continue ticking until completion. The emission gate rejects an ordinary
binding under `independentFlush` and rejects a recovery binding under
`coordinated`.

The generated interface metadata makes the waveform precise: `recover` is a
level held through observed completion, and `recovered` is the live level
`recover && all incident endpoints complete`. It remains asserted after
completion while `recover` remains asserted, then deasserts when the requester
releases `recover`; it is neither a one-cycle pulse nor a sticky host status.
A slower or unrelated observation transport must supply its own CDC-safe level
observation or acknowledgement adapter.

The loss-explicit protocol refinement, endpoint cycle equation, guard behavior,
ordered binding coverage, and coordinator component are checked individually.
Because incident channels may finish at different times, the System-facing
coordinated refinement retains an early channel's logical old epoch while its
physical FIFO remains held reset. `CompiledPair.abstract_step` proves the two
compiled endpoint states follow that model. Once every exact incident endpoint
is done, `coordinatedProtocol_event_eq_systemRecovery` commits every channel on
the same island-level event, and
`recoveryPortable_globalCommit_refines_advanceRecovery` joins its queue and
loss accounting to the exact `System.advanceRecovery` projection.

The remaining whole-wrapper theorem must carry the compiled FIFO controls,
storage, and datapath guards through early local reset and re-establish their
empty representation at that proved global commit. The island side is already
closed generically: compiler correctness for
`cycleOpenWithReset` proves the exact certified island module reaches the
`System.advanceRecovery` reset state. RTL
simulation of unrelated clocks exercises quiescence, contained island reset,
FIFO flush, and return to service, but remains smoke evidence rather than that
composition theorem.

## Current production-SoC limits

The typed facade is suitable for flat or source-hierarchical point-to-point
systems with mixed synchronous/asynchronous FIFO selections, structured packed payloads,
arbitrary positive synchronous depths, portable power-of-two asynchronous
depths, coordinated reset, and graceful independently requested island reset.
Remaining large-SoC work is:

- close the remaining compiled FIFO/storage/guard state relation and package
  the resulting whole-wrapper recovery composition theorem;
- attach a checked, inspectable timing contract to each realization selection
  and provide composition lemmas/reports, so designers can see and prove the
  latency introduced at every channel boundary;
- automatic instance prefixing is remaining hierarchy ergonomics. Today
  sealed blocks carry checked typed exports, cached island certificates, and
  an arbitrary dependent theorem bundle; parents flatten them and close only
  source/sink endpoints indexed by the exact same `Chan`, while ordinary
  assembly rejects name collisions and parent/child reset-policy disagreement.

These are API and proof obligations, not a reason to add a catalogue of CDC
idioms. Typed queues plus a small number of proved reference realizations
remain the center.

## Realizations

`Chan` specifies behavior and does not select hardware. Loom ships a compiled
synchronous FIFO and a portable compiled Gray-pointer/register-bank FIFO.
Expert users may bind FPGA or ASIC implementations by
proving the same technology-neutral contract. No vendor, FPGA/ASIC choice, or
synthesis tool appears in `System` semantics.

## Explicit non-goals

Core Loom does not provide:

- analog metastability or MTBF proofs;
- timing closure, placement, routing, or synthesis correctness;
- implicit raw cross-domain wires;
- automatic deadlock freedom for arbitrary channel networks;
- liveness without stated service/tick premises;
- a universal temporal-logic or finite-state-search framework; or
- a mandated Gray FIFO, RAM primitive, FPGA family, ASIC library, or tool.

Clock Gauntlet's schedule search, protocol projection, rank certificate, digest
checker, and ZC702 shell are application/evidence machinery. They validate the
small abstraction but do not enlarge its ordinary-user API.

## Reference examples

`Machines.Substrate.TwoClock` is the small non-pipeline mailbox acceptance
example. It reuses the tutorial counter's existing invariant through
`liftIsland`, proves channel capacity without unfolding System wiring, selects
the portable realization with one `realizePortable` call, replays a schedule
through `Application.run`, inspects the result through `Application.readReg`,
and emits a certified exact-byte artifact.

`Machines.Multiclock.ClockGauntlet` is the stronger evidence workload. It adds
an arbitrary-schedule end-to-end trace theorem and bounded-progress evidence,
but its specialized liveness machinery is not a required Loom abstraction.

`Machines.Multiclock.RecoverySmoke` is the small three-clock recovery
acceptance design. An active source/forwarder/sink pipeline makes its center
island incident to two channels and establishes a nonzero FIFO epoch before
recovery, forcing the generated completion gate to cover four physical
endpoint halves. The repository RTL test checks completion coverage, held
common-empty pointer/synchronizer state, reset containment, and renewed
traffic after release under three unrelated clocks.
