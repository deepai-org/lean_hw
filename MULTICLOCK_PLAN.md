# Multi-clock systems and clock-domain crossings

This is the implementation plan for composing ordinary synchronous Loom
designs across clock domains. It refines the destination in
[`PLATONIC.md`](PLATONIC.md) and the ordered work item in
[`ROADMAP.md`](ROADMAP.md).

The first low-level foundation is shipped in `Loom/Hw/System.lean`:
executable clock events and schedules, a vector of synchronous Design islands,
schedule-quantified `System.Invariant`, per-event framing,
`System.island_reachable`, and `liftIsland`/`liftIsland₂`. The two-counter
example demonstrates schedule-independent lifting. The ergonomic assembly API
shown below (`System.empty`/`island`/`connect`), typed `Chan` handles, endpoint
adapters and laws, concrete CDC refinement, crossing inventories, hierarchy,
and verified multi-clock emission remain planned work.

The architectural rule is:

> Cycle-exact logic stays inside an ordinary single-clock `Design`. Every
> cross-domain edge is a declared abstract channel paired with a concrete CDC
> realization and a checked refinement. There is no raw cross-domain wire API.

This keeps pipelines, bypass networks, register-file forwarding, and
cycle-sensitive state machines in the semantics they already use. Elasticity
is system-level composition discipline, not an internal coding style imposed
on synchronous blocks.

## Non-negotiable boundaries

1. `Design.cycle`, its compiler theorem, `FastEval`, `DagEval`, lockstep, and
   the single-clock emitter remain unchanged.
2. A system may connect ordinary ports directly only within one declared
   clock domain. A crossing type-checks only through a packaged `Crossing`
   containing:
   - an abstract channel specification;
   - proved source and destination endpoint laws;
   - a concrete CDC component; and
   - a refinement from that component to the abstract channel.
3. Valid/ready, credits, payload buses, and pulses never cross an asynchronous
   boundary as unstructured wires. Valid/ready may be the abstract endpoint
   protocol; the realization is an asynchronous FIFO, toggle protocol,
   synchronized credit protocol, or another proved component.
4. Metastability physics is not silently formalized away. Concrete CDC proofs
   quantify over an adversarial digital resolution model. MTBF, aperture,
   placement, routing, and the claim that a first-stage flop settles before it
   is resampled remain explicit physical assumptions.
5. Safety and functional transfer theorems may be independent of clock ratios.
   Progress still names the necessary local-tick, readiness, capacity, and
   network-deadlock assumptions.

The system assembly API must make an undeclared crossing unrepresentable,
rather than relying on a report to discover one later.

## Public API and complexity budget

The multiclock layer must preserve the usability boundary Loom already has:
users write typed declarations and ordinary `Design` proofs; compiler
correctness, DAG certification, coverage planning, schedules, endpoint-law
proofs, and CDC refinements remain library machinery. The complete ordinary
user surface should have five parts.

### 1. Channels are typed handles

The intended shape is:

```lean
def cmdQ : Chan 32 := ⟨"cmd", depth := 2⟩
```

Inside an island, `cmdQ.enq e` is a guarded action and `cmdQ.canEnq` and
`cmdQ.deq` are typed expressions or declarations used like registers and
memories today. Users do not write valid/ready signals or prove payload
stability and no-retraction for a stock channel. The channel declaration
generates an endpoint adapter satisfying those laws by construction, just as
typed declarations generate ordinary state and port plumbing.

Custom endpoint protocols and new concrete CDC realizations remain possible,
but their authors cross an explicit expert boundary and must supply the laws
and refinement that an ordinary `Chan` gets from the library.

### 2. Composition is `par` with clock names

The intended assembly reads like:

```lean
def chip : System :=
  System.empty
    |>.island "core" coreDesign (clock := "clkA")
    |>.island "dsp"  dspDesign  (clock := "clkB")
    |>.connect cmdQ (from := "core") (to := "dsp")
```

Widths are checked by types, endpoints pair exactly once, names remain unique,
and a cross-clock reference outside a `Chan` is an assembly error. These are
construction and assembly gates, not application proof obligations. On one
clock, `System` is definitionally the familiar parallel composition of its
islands and channels use ordinary synchronous state underneath.

### 3. One combinator lifts island theorems

The public form of island determinacy is one theorem combinator:

```lean
theorem chip_core_ok : chip.Invariant (atIsland "core" CoreOk) :=
  liftIsland core_ok_invariant
```

`liftIsland` hides the local-run projection, framing, and determinacy proof.
Properties of an island continue to be stated and proved in ordinary
single-clock `Design` land; moving the island into a system does not require
restating them over schedules.

### 4. Channels supply the cross-island lemma library

Stock channels expose proved facts such as `Chan.noLoss`, `Chan.fifoOrder`, and
`Chan.deliveredWithin`. Cross-island proofs combine lifted island invariants
with these lemmas and simp-level connection facts. The generated adapter,
selected co-tick semantics, concrete CDC component, and refinement proof live
behind those statements.

### 5. System invariants hide schedules

`chip.Invariant P` quantifies internally over every schedule admitted by the
chip's declared clocks and over the permitted CDC-resolution choices. An
application proof does not mention `SchedulePrefix`, `ClockRel`, fairness, or
co-tick cases. Readiness or local-tick premises needed by a bounded-delivery
lemma are stated in channel terms. Raw schedules surface only in executable
debugging, for example `chip.run (scheduleSeed := 42)`, and in the expert API
used to implement and prove the library itself.

The governing acceptance test is:

> Going from one clock to two changes one clock annotation in the user's file
> and zero lines in the user's proofs.

If this test fails, multiclock mechanism has leaked through the abstraction
and must be moved back into the library.

## Hierarchical composition

The first hierarchy mechanism is Lean itself. A reusable block is a function
returning islands and channels, parameterized like any other Loom generator.
Its source remains hierarchical while assembly assigns collision-free
prefixed identities beneath it, following today's `par` discipline.

When designs need opaque reuse, a proved `System` may be sealed behind an
interface containing only exported channel endpoints and a theorem bundle.
Higher levels compose sealed interfaces without inspecting internal islands.
Sealing is an additive second stage: it must not change the flat composition
API, invalidate existing proofs, or introduce a second channel model.

## Executable clock model

The proof, runner, and bounded checker must consume the same schedule type.
The initial representation should therefore be executable data, not an
abstract set:

```lean
abbrev DomainId (n : Nat) := Fin n
abbrev ClockEvent (n : Nat) := DomainId n → Bool
abbrev SchedulePrefix (n : Nat) := Array (ClockEvent n)
```

`ClockEvent` says which domains tick at one logical event. It preserves truly
aligned edges while also representing gated and independently ticking
domains. `SchedulePrefix` is the object enumerated by BMC, generated by the
adversarial runner, recorded in a failure artifact, and replayed exactly.

A `ClockRel` is an executable, prefix-closed predicate over schedule prefixes,
with proved constructors for at least:

- one always-ticking domain;
- aligned 1:1 domains;
- explicit enable traces and integer-ratio schedules;
- singleton-event asynchronous interleaving;
- bounded drift or bounded starvation; and
- unconstrained finite schedules for safety checks.

The system transition reads every selected island and channel endpoint from
the pre-event state and commits the event atomically. Any alternative ordering
must be represented as a different explicit event or a named choice, never as
Lean evaluation order.

### Definitional single-domain compatibility

The degenerate case has a strict acceptance bar:

```lean
@[simp] theorem single_step (d : Design) (s : St) :
    (System.single d).step ClockEvent.always s = d.cycle s := rfl
```

The exact declaration may differ, but the equality must remain definitional
or close by `simp` without a simulation argument. The one-domain state type
must reduce to `St`, not a one-element product wrapper. This is what lets all
existing Design theorems and executable tooling continue to apply directly.

## Abstract elastic channels

Start with a typed one-entry channel. Its state contains occupancy and a
payload. Its interface records source valid/payload and destination ready/data
events plus accepted enqueue and dequeue events.

### Co-tick policy is mandatory data

A one-entry channel declaration must choose its behavior when it is full and
producer and consumer both tick:

```lean
inductive FullCoTickPolicy
  | refusePush
  | exchange
```

- `refusePush`: the consumer may remove the old payload, but the producer sees
  the pre-event full state and its push is not accepted.
- `exchange`: the consumer receives the old payload and the producer replaces
  it atomically, leaving the channel full.

The policy is mandatory checked data, but it need not be routine user input.
A stock `Chan` constructor selects and documents one library policy; expert
constructors may select another explicitly. In both cases the selected policy
is part of the abstract channel declaration, its throughput statements, trace
semantics, generated inventory, and the refinement obligation for a concrete
realization. It must never emerge accidentally from evaluator ordering or be
silently changed by the single-clock or multiclock backend.

Regressions must cover empty/full, push-only, pop-only, simultaneous push/pop,
backpressure, reset, and every policy. In particular, an aligned 1:1 exchange
channel must demonstrate one transfer per event after filling, while the
refuse policy must demonstrate its deliberately lower bound.

## Named nondeterminism and trace determinacy

Specification networks should be Kahn-deterministic except at declared merge
nodes. Arbitration must not appear as diffuse quantification over all system
steps. Each merge has a stable identifier and an explicit executable choice
oracle:

```lean
abbrev MergeId := String
abbrev ChoiceOracle := MergeId → Nat → Nat
```

The exact choice representation may be tightened per merge, but it must be
finite-prefix executable, recordable, and replayable. A runner failure records
both its schedule prefix and oracle decisions.

The central network theorem is then sharp:

> For fixed initial state, external accepted-message traces, and named choice
> oracles, observable transfer traces do not depend on the admissible clock
> schedule.

Oracle-free subnetworks are deterministic outright. Networks with merges are
deterministic relative to their declared oracles. If a purportedly
deterministic block cannot establish this property, it has either an
undeclared crossing, an undeclared arbiter, or a timing-sensitive interface.

## Endpoint laws reuse `TransitionProperty`

An endpoint is an ordinary island `Design` plus typed declarations identifying
its channel signals. Required laws are stated as existing general
`TransitionProperty` values and discharged with the existing footprint,
support, frame, and projected-cycle machinery.

Initial endpoint laws include:

- payload is stable while `valid && !ready`;
- valid is not retracted before acceptance;
- a consumer uses payload only on an accepted transfer;
- credit never exceeds declared capacity and is never overspent;
- reset establishes the endpoint's declared empty/quiet state; and
- any exclusion or environment reliance is named.

Internally, `Endpoint` packages the declarations and proofs, and
`System.connect` accepts only endpoints compatible with the selected abstract
channel. Stock `Chan` endpoints are generated with these proofs, so ordinary
island authors see only the channel handle operations. Authors of custom
endpoint adapters use the same `TransitionProperty` proof style as for current
invariants; the system layer introduces no parallel property language.

## Island determinacy

Unticked-domain framing is only the one-event lemma. The first major
composition deliverable is its cumulative form:

> An island's state is a function only of its initial state, number of local
> ticks, accepted input-message sequences, external input sequence, and named
> local choice oracles. The global schedule does not otherwise occur.

This theorem is the multi-domain analogue of Loom's frame results. It lets an
island retain ordinary cycle-indexed Design proofs, then transport them to a
system execution using the island's local tick trace. Failure to prove island
determinacy is itself a fail-closed indication of an undeclared dependency.

Necessary supporting results include:

- unticked islands and endpoint state are unchanged;
- disjoint island ticks commute when no declared channel event connects them;
- local projections of a system run equal the corresponding island run over
  accepted inputs; and
- channel transfer traces completely mediate cross-island influence.

## Bounded liveness first

The workhorse progress statement is finite-prefix bounded response, phrased in
local ticks or accepted transfers rather than a global reference clock:

> If a message is accepted and the destination satisfies its readiness
> contract, delivery occurs within `k` destination ticks.

This fits the existing `TSys` bounded-response and induction machinery, is
directly executable at small depths, and states the worst-case guarantee a
hardware consumer needs. Variants may count source ticks, destination ticks,
channel actions, or a `ClockRel` reference event, but the unit is always part
of the theorem.

Eventual delivery under fairness is a corollary of a suitable bounded theorem,
not the primary proof interface. Finite capacity does not by itself establish
network liveness: cyclic credit dependencies, arbitration, endpoint readiness,
and reset drainage remain named obligations.

## Concrete CDC refinement

Concrete components form a second layer below the abstract channels.
`CdcContract.lean` supplies the style: uncertainty at the first synchronizer
sample is an adversarial oracle, and the digital protocol is proved for every
oracle result under an explicit event-rate assumption.

The implementation order is:

1. Repackage the existing toggle synchronizer as a concrete realization of an
   abstract one-entry event channel without weakening its current theorem.
2. Add a bundled-data toggle channel whose payload-stability contract is
   proved at both endpoints.
3. Add a small dual-clock FIFO with binary storage indices, Gray-coded crossing
   pointers, synchronized pointer observations, and explicit reset behavior.
4. Prove the adjacent-Gray-code lemma: during one legal pointer transition,
   an adversarial sample denotes the old or new code, never a third pointer.
5. Prove the concrete FIFO stutter-refines the selected abstract queue policy,
   including no loss, duplication, corruption, overflow, underflow, or illegal
   reordering.

The abstract channel theorem must not assume a particular FPGA primitive,
ASIC synchronizer cell, synthesis tool, or clock ratio. Concrete physical
instantiation and sign-off remain external evidence.

## Derived crossing and constraint inventory

Reports arrive with the first system declaration, before verified top-level
emission. From the typed crossing graph Loom derives:

1. a complete crossing inventory containing channel identity, source and
   destination domains, endpoint widths, abstract policy, concrete component,
   reset policy, and discharged proof names; and
2. a technology-neutral constraint manifest describing asynchronous clock
   groups, synchronizer paths, maximum-delay requirements, false paths, and
   any component-specific placement requirements.

Thin evidence-layer renderers may turn that neutral manifest into SDC or XDC.
Vendor syntax and device-specific constraints do not enter generic `Loom/Hw`.
Every rendered entry cites its source crossing identity, and every declared
crossing must be covered exactly once. The board review checklist is generated
from the same data and fails on an unbound or multiply bound crossing.

These artifacts prevent omissions but do not prove that a P&R tool applied a
constraint, that synchronizer flops were placed correctly, or that silicon
meets MTBF. Those remain separately identified implementation evidence.

## Runner and bounded checking

The system runner operates on `SchedulePrefix` and `ChoiceOracle` directly.
It provides seeded generators for at least:

- aligned edges and alignment-boundary changes;
- starvation of each domain up to a configured bound;
- bursty producer and consumer clocks;
- maximum backpressure;
- full-channel simultaneous push/pop under every co-tick policy;
- reset assertion and staggered release; and
- named-merge contention.

Failures serialize the exact finite schedule, oracle choices, accepted
transfers, and artifact identity. Replay consumes those bytes without random
generation. The bounded checker enumerates the same `ClockEvent` values for a
small channel and shallow schedule; it must not maintain a second schedule
encoding or an unproved conversion.

## Implementation sequence

### Phase 1: single-clock `Chan` and `System` API

- Ship typed `Chan` handles, generated stock endpoints, `System.island`, and
  `System.connect` while every island still uses one clock.
- Make the one-clock system reduce definitionally to existing `par`/`Design`
  behavior and implement channels with ordinary synchronous state.
- Provide `System.Invariant`, `liftIsland`, and the initial `Chan` lemma
  library without exposing a schedule type to application code.
- Demonstrate modular composition and upward theorem reuse on existing
  synchronous examples before adding the multiclock backend.

This phase is independently useful and freezes the five public verbs while
their implementation is cheapest. Later phases strengthen their proofs and
backend without changing application code.

### Phase 2: executable multiclock spine and inventory

- Retain the shipped executable clock events, schedules, low-level `System`
  island vector, per-event framing, island reachability, and invariant lifting.
- Add named domains, finite schedule prefixes, and `ClockRel` in the
  internal/expert layer.
- Make raw cross-domain connections unrepresentable.
- Generate crossing and neutral constraint inventories immediately.
- Establish the rfl-tight one-domain always-tick case.
- Preserve the shipped frame and lifting theorems through the named assembly
  and channel layers.

### Phase 3: multiclock channel semantics and generated endpoint laws

- Define the abstract channel with mandatory `FullCoTickPolicy`.
- Generate stock source and destination adapters and package their endpoint
  laws as `TransitionProperty` proofs behind `Chan`.
- Prove no loss, duplication, corruption, overflow, or underflow for arbitrary
  finite schedules.
- Add executable and bounded exhaustive regressions for both co-tick policies.

### Phase 4: composition and determinacy

- Add named merge nodes and executable choice oracles.
- Prove island determinacy and local-run projection.
- Expose those results to applications only through `liftIsland` and the
  `Chan` lemma library.
- Prove schedule independence relative to choice oracles.
- Prove bounded delivery in destination ticks; derive the fairness corollary.

### Phase 5: concrete CDC components

- Connect the existing toggle proof to the abstract event channel.
- Add and refine a bundled-data toggle channel.
- Add and refine a small Gray-pointer asynchronous FIFO.
- Keep physical resolution and implementation assumptions explicit.

### Phase 6: runner, BMC, and evidence adapters

- Add adversarial schedule/oracle generation, recording, and replay.
- Enumerate shallow schedules through the same executable representation.
- Render neutral constraints into SDC/XDC in the evidence layer and verify
  complete crossing coverage.

### Phase 7: multi-clock structural emission

Only after the semantic and reporting layers are stable, consider a small
top-level structural emitter with explicit clock ports and instantiated proved
CDC components. Island RTL continues to come from the existing compiler.
Hand-written wrappers remain supported and are checked against the generated
crossing inventory.

## Demonstration ladder

The first proof vehicle should be two small non-CPU islands: a bounded
producer and consumer joined by the one-entry channel. It must demonstrate
both co-tick policies, schedule replay, bounded delivery, island determinacy,
and the rfl-tight single-island specialization.

The next vehicle should introduce a named two-input merge and show that traces
depend on its recorded oracle but not on the schedule. Only then should a real
machine integration adopt the layer. A CPU is a consumer of the theory, not
the example from which the generic endpoint interface is designed.

## Production adoption: LNP64mini

The work does not stop at the demonstration ladder. LNP64mini is the required
production consumer because its board integration already contains real
DRCK/JTAG-to-`sysclk` crossings, currently split between a proved standalone
toggle model and a hand-written wrapper.

The adoption must preserve the ordinary LNP64mini core as one unchanged
single-clock `Design`. The system layer describes the surrounding domains and
channels; it does not make the CPU pipeline elastic or move its cycle-sensitive
gate, scheduler, cache, or bus logic into a multi-clock semantics.

### LNP64mini crossing declaration

Add a machine-side system declaration, expected to live in a module such as
`Machines/Lnp64mini/MultiClock.lean`, with at least:

- the existing LNP64mini `sysclk` Design island;
- a debug/DRCK domain endpoint representing JTAG update and readback events;
- a bundled command channel carrying command index and data into `sysclk`;
- a response/readback channel or an explicitly classified tear-tolerant
  observation for values returning to DRCK;
- reset assertion and per-domain reset-release crossings; and
- the concrete toggle/FIFO realization selected for every channel.

The command payload must be one typed value. It is not acceptable to prove a
toggle crosses exactly once while leaving `cmd_idx` and `cmd_data` as unrelated
raw buses. Their stability window and association with the accepted command
event are part of the bundled channel refinement.

### Adoption ladder

1. **Inventory without wrapper mutation.** Declare every existing LNP64mini
   board crossing and generate the crossing plus neutral-constraint manifests.
   Add a fail-closed wrapper-binding check showing that every declared crossing
   is bound exactly once and that no known wrapper crossing is unlisted.
2. **Command ingress.** Repackage the existing toggle synchronizer theorem as
   the concrete realization of the bundled command channel. Connect its
   accepted-transfer trace to the existing `CmdPulseTrace`/open-Design input
   contract, so one theorem spans source update, adversarial synchronization,
   one destination command pulse, and the LNP64mini Design step that consumes
   the matching payload.
3. **Readback classification.** Replace each return path with either a proved
   response channel or an explicit tear-tolerant observation type. Quasi-static
   captures, counters, and coherent multiword responses must not share one
   undocumented category.
4. **Reset crossings.** Model assertion and staggered release for both domains.
   Prove channel occupancy, toggle phase, and endpoint valid state return to the
   declared quiet state for every supported release ordering.
5. **Generated constraints in the board gate.** Render the neutral manifest to
   the board's SDC/XDC evidence, bind each line back to its crossing identity,
   and make stale, missing, duplicate, or extra bindings fail the existing
   quality/reproduction workflow.
6. **Adversarial execution.** Run the same machine declaration under aligned,
   bursty, bounded-starvation, reset-boundary, and source/destination
   near-coincident schedules. Record and replay schedule prefixes and all CDC
   resolution or merge choices through the generic runner.
7. **Lift a real machine theorem.** Transport at least one existing LNP64mini
   property through the production system composition—not merely a channel
   invariant. The initial target should combine exactly-once command delivery
   with a typed machine consequence, such as preservation of the wake/gate
   continuation invariant or the command-constrained lifecycle invariant, for
   every admissible debug/`sysclk` schedule.

### Production acceptance

LNP64mini adoption is accepted only when:

- its core `Design`, compiler theorem, certified DAG simulator, and internal
  cycle semantics remain unchanged;
- every actual board crossing is present in the generated inventory and bound
  exactly once to the hand-written wrapper;
- raw `cmd_valid`/`cmd_idx`/`cmd_data` wiring is replaced at the system boundary
  by one proved bundled command channel;
- every readback path is proved coherent or visibly typed and reported as
  tear-tolerant;
- the board constraint artifact is generated from the crossing declaration and
  checked for freshness and complete coverage;
- adversarial schedule and synchronizer-resolution runs are replayable; and
  their bounded checks cover the command channel's small-depth state space;
- a real LNP64mini Design property has been lifted to the composed system for
  all admissible schedules; and
- the normal LNP64mini emission, selftest, debug-map, board-wrapper, and
  reproduction gates consume this declaration rather than maintaining a
  parallel crossing list; and
- moving the adopted system declaration between its synchronous test
  configuration and the real DRCK/`sysclk` configuration changes clock
  annotations and backend selection, but no lifted island proof.

This production leg is part of the workstream's definition of done, not a
follow-on integration suggestion.

## Completion criteria

This workstream is complete only when all of the following are direct checked
facts:

- ordinary users need only typed `Chan` handles, `System.island`/`connect`,
  `liftIsland`, the `Chan` lemma library, and `System.Invariant`;
- the same public API has a useful single-clock implementation before the
  multiclock backend, and changing one island to a second clock changes no
  application proof;
- existing single-clock designs, proofs, evaluators, and emission remain on
  unchanged `Design.cycle` semantics;
- the always-tick one-domain system step reduces definitionally to
  `Design.cycle`;
- no system declaration can type-check a raw asynchronous valid/ready or data
  crossing;
- every crossing selects an explicit co-tick policy and concrete realization;
- endpoint laws are ordinary checked `TransitionProperty` obligations;
- arbitrary-schedule safety, oracle-relative schedule independence, island
  determinacy, and bounded destination-tick delivery are proved;
- a concrete adversarial toggle channel and Gray-pointer FIFO refine their
  abstract channels under named assumptions;
- proof, runner, replay, and bounded enumeration share one executable schedule
  representation;
- crossing and neutral constraint inventories are total derived views, with
  evidence-layer SDC/XDC rendering; and
- at least two non-CPU islands and one named merge demonstrate the complete
  composition path before a large machine depends on it;
- a proved subsystem can be sealed behind exported channel endpoints and a
  theorem bundle, then composed without exposing its internals; and
- LNP64mini satisfies the production-adoption acceptance gates above, including
  a bundled command crossing and one lifted machine theorem.
