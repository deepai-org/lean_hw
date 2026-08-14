# Multiclock Loom roadmap

This is the implementation roadmap for Loom's multiclock layer. The concise
user contract is [`MULTICLOCK.md`](MULTICLOCK.md); the formal/physical trust
boundary is [`MULTICLOCK_BOUNDARY.md`](MULTICLOCK_BOUNDARY.md). This file lists
the current architecture and only the unfinished work that still belongs in
generic Loom.

The scope test is:

> Going from one clock to two changes a clock annotation and zero existing
> island proofs.

An application author should need only ordinary hardware, clock placement,
typed channels, send/receive operations, and a realization choice.
`System.Invariant` and `liftIsland` are the next, proof-author level rather than
prerequisites for constructing a crossing.

Cycle-sensitive logic remains inside an ordinary synchronous `Design`.
Elasticity is a composition discipline at declared boundaries, not a coding
style imposed inside CPUs, pipelines, register files, or state machines.

## Architecture

Three layers are enough.

### 1. System semantics

`System` provides named synchronous islands, named clocks, executable clock
events, typed connections, atomic abstract-channel transitions, and
schedule-quantified invariants. `SystemBuilder` is the generator-friendly raw
declaration type; only a checked `System` may be executed, proved, or emitted.

`ClockRel` is an executable, prefix-closed predicate over the same finite event
prefixes used by proofs and replay. Application invariants do not mention it:
`System.Invariant` quantifies over every admitted schedule internally.
`ClockRel.asynchronous` admits coincident unrelated edges; the narrower
`ClockRel.interleaved` relation is available only when a proof or executable
experiment deliberately linearizes them.

The public reset policy is deliberately narrow and explicit:

- all islands and abstract channels enter reset together;
- scheduled execution begins after their common release; and
- a delayed first tick is not a separate reset state.

There is no unilateral live-reset transition. Supporting one would require an
explicit flush, epoch, or recovery protocol in the abstract channel semantics;
it must never arise from an emitter or runner convention.

When every connected island has the same clock, `System.elaborate` lowers the
assembly through the existing `Design.par`/`Design.connect` path. The result is
an ordinary `Design` using `Design.cycle`, the existing compiler, simulators,
proofs, and emitter. Cross-clock systems cannot silently take that path.

### 2. Channel contracts and realizations

`Chan w` is a typed bounded-queue behavior, including an explicit full co-tick
policy. It does not name a circuit, vendor, FPGA/ASIC flow, clock ratio, or
synthesis tool.

`Chan.Refinement` is the expert interface for an executable realization. Loom
ships:

- the ordinary synchronous adapter;
- a toggle-mailbox model;
- an asynchronous FIFO model; and
- a portable certified power-of-two-depth realization whose control and
  register-bank storage are compiled ordinary `Design`s.

Physical emission selects exactly one realization per connection.
`RealizedSystem` derives structural RTL, a crossing inventory, and a neutral
constraint manifest from the same ordered connection set. Coverage theorems
prevent a connection from disappearing from any artifact. Optional FPGA RAM
or ASIC SRAM implementations remain replaceable leaves under the same
technology-neutral storage contract.

Gray-pointer logic is a supplied reference realization, not the meaning of
`Chan`. Generic Loom contains no handwritten behavioral CDC RTL on the
certified path. Metastability, MTBF, timing closure, placement, routing, and
downstream tool interpretation remain physical evidence.

### 3. Small theorem library

The reusable library is intentionally small:

- `Chan.noOverflow`, FIFO-head order, and finite-trace conservation;
- `System.channelCapacityInvariant` and `channelTraceConservation`;
- `System.liftIsland` for existing ordinary open-`Design` invariants;
- `ChannelInvariant.and` and `System.liftChannels` for relational channel
  safety;
- `TraceContract.comp` and `mapPrefix_comp` for schedule-free functional
  trace composition; and
- `TraceContract.deliveredWithin` for an explicit application-defined service
  bound, with serial bounds composed by addition.

The last item does not infer liveness from connectivity. A caller must state
and prove what one service index means (destination ticks, grants, rounds, or
another suitable unit) and discharge the component bounds.

### Timing-contract requirement

The five-concept application facade may hide handshake plumbing, but it must
not hide latency. Every selected realization will derive a technology-neutral
timing contract recording:

- where acceptance and delivery are observed;
- buffering and synchronizer stages;
- whether a bound is exact, conditional on named service/tick premises, or
  absent under the selected `ClockRel`;
- the bound's unit (source ticks, destination ticks, grants, or named System
  events); and
- whether independent recovery can interrupt service and what completion
  premises it requires.

No wall-clock bound is inferred from a logical schedule. In particular, an
asynchronous channel under an unconstrained relation has no finite
global-event delivery bound if the destination may stop ticking. A theorem may
give a finite destination-tick bound only after stating the consumer,
backpressure, and synchronizer-progress premises it uses.

The description is derived from the same `RealizationPlan` entry that selects
the hardware, appears through typed application inspection and an explicitly
requested human diagnostic, and is covered by the same ordered connection-key
theorem as the crossing inventory. Normal emission produces no CSV/TSV
sidecars: ordinary review artifacts are Markdown and programmatic consumers
use the typed values directly. Expert bindings with no timing
description fail emission. Positive semantic bounds must be usable directly
with `TraceContract.deliveredWithin`. Hierarchical composition preserves the
per-boundary contracts and adds serial bounds; it may not silently replace
them with a single optimistic number. This is core mechanics, not pretty
syntax.

## Current acceptance evidence

The small acceptance design is `Machines.Substrate.TwoClock`:

- it is a one-hop mailbox, not a three-stage Gauntlet pipeline;
- its producer and consumer are ordinary `Design`s connected by `Chan 8`;
- an existing tutorial `SatCounter` island is reused unchanged;
- the existing `satOk_invariant` is lifted without restating it over clocks or
  schedules;
- channel capacity is proved through the public connection law;
- the portable certified power-of-two-depth realization is selected; and
- its literal emitted `system.v` bytes, crossing inventory, and neutral
  constraints share the checked connection-key domain.

`Machines.Multiclock.ClockGauntlet` is stronger application/evidence work. It
adds arbitrary-schedule end-to-end trace safety and a specialized bounded
progress certificate. Its frontier search, rank, digest, campaign runner, and
board shell remain outside the ordinary Loom API.

`Machines.Lnp64mini.Multiclock` is the production-scale API consumer. It keeps
the CPU as one unchanged synchronous island and packages a technology-neutral
multiclock artifact. Board-wrapper adoption and silicon campaigns are useful
external evidence, not prerequisites for the generic abstraction to be
well-defined.

## Application facade

`Loom.Hw.Multiclock` now supplies the ordinary-Lean stock path:

- `Chan.send`, `canSend`, `hasData`, `data`, and `consume` expose channel use
  without raw valid/ready signals;
- `ClockHandle`, `IslandHandle`, directional channel endpoints, and
  `ChannelRoute` remove application-spelled topology strings;
- `PackedChan` endpoints and hierarchical exports carry semantic packed
  payload types while erasing to the same scalar CDC implementation;
- `SystemBuilder.addChannel` connects typed island handles and generates both
  endpoint adapters;
- `RealizationPlan` selects the compiler-produced synchronous, portable
  asynchronous, or independently recoverable portable implementation per
  typed `ChannelRoute`; `System.realizeWith`
  derives the channel refinements, ordered coverage, clock-rule proofs, and
  certified realized artifact from one checked gate;
- the synchronous reference accepts every positive depth, while the portable
  Gray FIFO and proved register-bank storage accept arbitrary power-of-two
  depths through the same `Chan`/`PackedChan` API;
- `CertifiedIslands` and `realizeWithCertified` cache the expensive
  island/compiler/DAG certificates independently of physical channel plans;
- `System.Application.run`, `runChecked`, `readReg`, `readChannel`, and `emit`
  provide replay, inspection, and exact certified emission without exposing
  certificates; `runRecovery` and `runRecoveryChecked` preserve the same
  certified island relation for reset-aware replay; and
- `readinessIssues`, `selectedReadinessReport`, `realizePortableChecked`, and
  `realizeWithChecked` provide named failures for generator and interactive
  use.

Both `Machines.Substrate.TwoClock` and `Machines.Lnp64mini.Multiclock` use this
facade. Neither constructs low-level storage/binding certificates, lookup
equalities, coverage proofs, or typed DAG register views. The Gauntlet artifact
remains the expert-level exercise of explicit realization assembly.

## Maintenance requirements

1. Keep the five-concept conceptual API frozen. Application code outside
   dedicated implementation/evidence modules should not normally mention
   `inputFor`, `connectionInput?`, generated endpoint names, `PackedQueue`, raw
   one-bit handshake conversions, `Chan.Refinement`, or storage witnesses.
2. Keep reset fail-closed. Adding a new `SystemResetPolicy` constructor must
   force an explicit semantic implementation rather than inherit coordinated
   behavior accidentally.
3. Keep one compact typed resolved-connection view for proofs and debugging,
   so callers do not unfold string dispatch or generated endpoint wiring.
4. Keep the second-design acceptance test and exact artifact/inventory checks
   in the ordinary test umbrella.
5. Keep the Gauntlet's specialized liveness proof intact, but do not move its
   finite-search or rank machinery into `Loom/Hw`.
6. At each substantial API increment, review one complete example as an RTL
   engineer rather than only as a proof author. The checkpoint asks:
   - Can the author predict latency, initiation interval, buffering, and reset
     interruption from the typed declaration?
   - Does generated RTL use recognizable ready/valid/FIFO structure and expose
     useful hierarchy and names for waveform debug and timing closure?
   - Is the common path shorter than hand-instantiating CDC plumbing, without
     requiring certificates, schedules, manifests, CSV/TSV files, or proof
     internals?
   - Can an FPGA or ASIC implementation replace the reference leaf without
     changing island code or weakening the channel theorem?
   - Did convenience introduce a throughput bubble, combinational loop,
     hidden clock assumption, or surprising reset loss?

   A negative answer changes the implementation plan; passing type checks and
   proofs alone is not sufficient evidence that the abstraction is natural.

Parser/elaborator sugar such as `system ... where`, `system_lift`, or
`#run_system` belongs to the separate prettification plan. It may later render
the facade pleasantly, but the facade must first be usable as normal Lean and
must not depend on new syntax.

## Bounded language milestone

Loom's responsibility ends at a precise language/verifier/compiler boundary.
It proves the digital multiclock semantics and generated portable
implementation, and emits a complete neutral description of the obligations
that a target flow must discharge. It does not prove MTBF, macro datasheets,
timing closure, tool interpretation, board clocks, or PPA.

The required milestone has three parts:

1. **Coherent portable storage — done.** The portable leaf is one clearly
   named first-word-fall-through combinational register bank. Its reader
   `Design` has no state or dead response pipeline; the wrapper consumes its
   sole `read_sample` output; its refinement computes the response from that
   expression; and timing reports zero physical storage-read stages.

2. **Precise reset behavior — done.** Every distinct clock domain has a typed
   `ResetIntent`. The current generated modules state that shared active-high
   `rst` is sampled synchronously, the domain must tick while reset is
   asserted, and release is sampled independently. This is intentionally not a
   reset-tree language. `SystemResetPolicy` remains the separate logical
   traffic-loss/recovery contract.

3. **Validated extension boundary — done.** The
   typed physical manifest includes every channel constraint and reset-domain
   contract. A backend report is constructible only with exact ordered
   coverage and reports `PASS`, `FAIL`, `SKIP`, or `UNCONSTRAINED` for every item. The
   small reference backend consumes every requirement exactly once. The
   target-storage mock receives the exact proof-matched width, depth, and read
   latency and makes its one external leaf assumption explicit. The generated
   neutral two-clock RTL passes an accessible technology-neutral synthesis
   sanity test; this is corroboration, not part of Loom's theorem or TCB.
   Reports now carry target/tool/run identity, exact
   RTL/intent/target-constraint/routed hashes, and post-synthesis object
   resolution. An optional openXC7 adapter consumes real
   routed-audit evidence and fails honestly on timing obligations that backend
   cannot discharge.

Two realization modes remain intentional:

- **Fully neutral:** compiler-generated register storage and controller RTL,
  unchanged between FPGA and ASIC flows.
- **Target refined:** the same channel semantics with compatible RAM/SRAM or
  synchronizer leaves selected by an evidence profile, with exact parameters
  and named external assumptions.

## Deferred library and evidence work

These are useful but are not gates on the language milestone:

- real FPGA block-RAM and ASIC SRAM bindings;
- production XDC, Quartus, and ASIC CDC/STA adapters;
- calibrated cost warnings beyond exact structural quantities;
- stable-level, event/pulse, mailbox, and reset-synchronizer components;
- further board campaigns; and
- the experimental independent-recovery whole-wrapper theorem.

The proved one-item-per-destination-tick buffered sink now exists as an
explicit option. The conservative half-rate endpoint remains the compatibility
default until broader use justifies changing source behavior.

Network-wide deadlock freedom, arbitration determinacy, and liveness without a
service premise remain application or reusable-component properties, not
automatic consequences of using a channel.

## Evidence policy

Portable formal claims must not depend on Xilinx, Zynq, openXC7, Yosys, an
ASIC library, or any other particular flow. Evidence-layer adapters may render
the neutral manifest to XDC, SDC, or tool-specific reports and may exercise an
available board.

The Clock Gauntlet ZC702 campaign is therefore corroboration of one exact
artifact, not a generic semantic premise. A syntax simulation is a wiring
smoke test, a routed CDC audit is implementation evidence, and a silicon soak
is physical evidence; none substitutes for `Chan.Refinement` or enlarges the
theorem boundary.

## Stopping criterion

The underlying generic mechanics are at a good stopping point when the small
non-pipeline acceptance design directly demonstrates all of the following:

- existing synchronous islands compose through typed channels;
- an existing island invariant lifts unchanged over all admitted schedules;
- a useful system property is proved without unfolding System wiring;
- the portable reference realization is selected through its contract;
- the selected realization's inserted buffering/synchronizer stages and
  provable latency class are inspectable rather than implicit;
- the exact emitted RTL plus crossing inventory and constraints are covered by
  one connection-key theorem; and
- no generic definition or theorem assumes a vendor, FPGA/ASIC choice, or
  synthesis tool.

The application API is at a good stopping point only when the same example's
source is dominated by its islands, channel operations, clock placement, and
realization choice. Stock certified emission and execution must not require a
second hand-written section of certificate, FIFO, storage, lookup, coverage,
view, and replay assembly. The LNP64mini consumer must use the same facade.

After this point, work should be driven by a concrete missing capability, a
failed abstraction test, or evidence that an existing guarantee is false—not
by completing the former Gauntlet-specific research wishlist.
