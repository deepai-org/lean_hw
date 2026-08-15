# The intended shape of Loom

Loom's organizing goal is:

> A design, its executable behavior, its proofs, its tests, its emitted
> logical artifact, and its external implementation evidence should be derived
> views of the same Lean value, with every non-derived link named as an
> assumption.

Loom is a hardware-design and proof system. It is not a synthesis tool, an
FPGA framework, an ASIC flow, or a formal reimplementation of an EDA tool.

The core expression language should cover ordinary fixed-width datapaths.
Multiplication is a same-width modular primitive with typed unsigned and signed
full-width constructors; concatenation is a typed constructor lowering to the
primitive algebra. Unsigned division and remainder use an explicit total
two-state contract (`a / 0 = 0`, `a % 0 = a`) preserved through emission; their mapping
to DSPs, gates, or staged units is not a Loom-level vendor decision.

This document describes the intended current destination. Current results are
recorded in [`STATUS.md`](STATUS.md), and the authoritative trust boundary is
recorded in [`TCB.md`](TCB.md).

## Immediate foundation

The following high-priority facilities are current requirements and are
implemented in the tree:

1. **Shared expression evaluation is the machine-simulation default.**
   `Loom/Hw/DagEval.lean` interns resolved expressions across every action root
   and evaluates each node once per cycle. LNP64mini's public `runDesign` and
   public runners prepare the certified DAG fail-closed, with no fallback to
   tree evaluation. The regression suite includes one nontrivial expression
   consumed by five separate funnels and checks that it has one shared DAG
   root with five consumers.

2. **The generated `Design` is the primary simulator.** LNP64mini's
   `runDesign` executes the certified shared-DAG core and derives peripheral
   requests from that core's state. `progtest` obtains its architectural
   outcomes from this path. LNP64mini's hand-written cycle mirror has been
   removed; architectural tests, RTL expectations, and board tooling derive
   from the Design.

3. **Typed declarations are the default observation surface.** `Design.coords`
   and resolved typed slots derive complete comparison or observation plans
   from the Design. LNP64mini's hand-maintained comparator, duplicate coverage
   tables, and mirrored state adapter have been removed.

4. **Checked properties are general over `Design`.** `ExprProperty` handles
   state properties and `TransitionProperty` handles typed before/after
   relations. Both infer their complete expression footprints, carry generic
   support/frame theorems, and reduce full Design cycles to the relevant
   writer cone. LNP64mini applies the general transition language to prove
   that wake preserves every slot's resume PC, gate stack frame, domain,
   depth, and in-gate state. In-gate parking is intentionally supported, so
   the checked rule preserves its continuation rather than falsely forbidding
   that state.

5. **Differential runs share one control plane.** `Loom.Runner` owns bounded
   stepping, mismatch and coverage events, immediate flushing, diagnostic
   limits, early-stop policy, and structured PASS/FAIL/SKIP results. Acc8,
   LNP64mini's core and bus components, and FastEval corroboration use it;
   machine code supplies only its opaque state and step callback.

6. **Artifact and command diagnostics are generic.** `Loom.Artifact` provides
   exact byte identities, identity-bound observations, verification, and
   change-only deterministic text writing. The generic shell diagnostics
   library provides freshness checks, captured producer logs, exact failing
   commands, and structured results. `artifact_identity.py` supplies portable
   SHA-256 manifests for external workflows; negative freshness, silent-log,
   and identity-mismatch cases run under `scripts/quality.sh`.

## Packed hardware values

Packed hardware values are implemented as a typed authoring facade over the
durable width-indexed `Expr`, `Reg`, `Mem`, and `Chan` core. `HwPacked` gives a
semantic Lean type one canonical fixed-width representation and proves
`pack`/`unpack` inverse laws. `HwPackedLayout` checks unique field names,
in-bounds disjoint slices, complete padding-free coverage, and MSB-first
declaration order. `PackedMember` additionally proves that each named Lean
record projection agrees with its hardware slice.

`PackedExpr`, `PackedReg`, `PackedInput`, `PackedOutput`, `PackedMem`, and
`PackedChan` retain the semantic type until an explicit `.bits` or `.fromBits`
boundary. Equal-width but unrelated records therefore do not become
assignment-compatible, and records acquire no accidental arithmetic or
ordering. Field reads and record construction lower to the existing
slice/concatenation expression algebra; packed channels use the unchanged
scalar queue, recovery, realization, and emission machinery.

Conversion follows the same nominal boundary. A semantic conversion constructs
the destination record field-by-field; Loom cannot infer that two equally wide
fields mean the same thing. Intentional representation conversion is spelled
`reinterpret value to Destination` in pretty syntax, requires equal packed
widths, and lowers exactly to `Destination.fromBits(value.bits)`. It adds no
implicit coercion, truncation, extension, logic, state, or latency.

`Act.writeSlice` is the one core action added for partial packed-register
assignment. Its bound proof makes an invalid slice unrepresentable. Every RHS
still observes pre-cycle state, preserved bits come from the ordered write
accumulator, and overlapping writes are last-write-wins. The semantics,
compiler correctness, evaluators, transformations, footprints, artifact and
release certificates, generators, and existing proof libraries all handle the
constructor directly.

The stable layout contract is:

- there is no padding or alignment;
- total width is exactly the sum of field widths;
- declaration order fixes placement, with the first field occupying the most
  significant bits and the last field the least significant bits;
- reset values and executable observations use the same `pack` function; and
- equality is packed bit equality.

The core currently supports named scalar `BitVec` fields and whole-element
packed memory access. Nested packed values, arrays, tagged unions, optional
fields, padding, memory-field read/modify/write, and external ABI matching are
separate features, not implied by “struct.” Native SystemVerilog structs are
also unnecessary: certified emission continues to use the established packed
vector and static slices. The omitted declaration syntax belongs only to
[`PRETTY.md`](PRETTY.md); it does not block typed packed designs or multiclock
use.

## Multiclock system composition

Ordinary synchronous `Design`s remain the proof and implementation unit inside
clock islands. A typed `Chan` or `PackedChan` is the only application-level
crossing: scalar and structured payloads use the same queue semantics,
schedule theorems, realization plan, and emitted binding. Packed records are
values carried by an endpoint, not a second interface or CDC language.

The application facade owns typed clock/island handles, directional endpoints,
per-route selection from a small proved realization set, arbitrary positive
same-clock depths, arbitrary power-of-two portable asynchronous depths, named
readiness reports, and reusable island certification. It must remain agnostic
to FPGA versus ASIC implementation and to every vendor or synthesis tool.
It must also make boundary latency inspectable: each selected realization
derives a coverage-checked timing description naming acceptance/delivery
points, buffering and synchronizer stages, exact or premise-dependent bounds
in domain ticks or System events, and any recovery interruption. Typed
convenience must never turn inserted cycles into a hidden implementation
detail.

The compatibility sink's registered request has an explicit two-destination-
tick issue interval. An opt-in, destination-local two-entry presentation
buffer provides a proved one-item-per-destination-tick steady state without a
combinational CDC path. This remains an endpoint presentation choice rather
than a new channel semantics or a target-specific primitive.

Physical evidence is keyed by exact device, tool/version, primitive mode,
storage configuration and presentation contract, and clock relationship.
Changing any key invalidates qualification. Target reports cover every neutral
requirement, bind exact RTL/intent/target-constraint/routed hashes and
post-synthesis object names, and fail unless every row is `PASS`; vendor
adapters remain outside generic Loom
imports.

Independent reset is a separate loss/recovery contract, never an implicit
variation of coordinated reset. Its current `independentFlush` semantics make
reset dominance and discarded incident traffic explicit. A loss-explicit
channel recovery refinement, schedule-executable request/acknowledgement
protocol, compiler-produced endpoint/guard/coordinator components, and stock
structural physical binding now implement the graceful request/completion
shape through the ordinary application facade. Binding/policy mismatches fail
closed at certified-artifact construction, and hierarchical parent/child reset
contracts must agree. Every incident channel contributes both endpoint halves
to the generated completion gate; reset-aware application replay retains the
certified DAG/semantic relation. Each FIFO half remains reset throughout its
endpoint's `flushed` phase, so reset skew cannot reintroduce a peer pointer
from the discarded epoch. Protocol completion is exactly the abstract
flush event for a single channel. For multi-channel islands, the coordinated
refinement retains each early-reset channel's logical epoch until the exact
generated coordinator domain is complete, then commits every incident channel
to the same `System.advanceRecovery` event. The compiled endpoint-pair
transition and this global event alignment are proved. The remaining formal
gap is the whole-wrapper state relation for the compiled FIFO, storage, and
guards across early local resets; generic reset-aware compiler correctness
already joins the exact compiled island reset. Checked
sealed blocks now carry typed exported endpoints, cached
island certificates, and dependent theorem bundles; packed exports retain
their semantic record type, and parent composition closes only endpoints
indexed by the same channel. Automatic instance prefixing is
ergonomic follow-up rather than a new semantic layer.
[`MULTICLOCK_PLAN.md`](MULTICLOCK_PLAN.md) is the detailed roadmap and
[`MULTICLOCK_BOUNDARY.md`](MULTICLOCK_BOUNDARY.md) states the remaining
physical assumptions.

## SoC construction architecture

Loom should grow from a verified design kernel into a practical SoC
construction system without turning every useful abstraction into a core
constructor. The admission rule is semantic, not popularity-based:

- **Core architecture** owns durable composition boundaries and distinctions
  that change observable transition behavior: typed components, domain
  membership, reset participation, and memory-port behavior.
- **Verified libraries** construct core designs and carry reusable refinement
  theorems. Streams, synchronizers, pipelines, arbiters, register maps, and bus
  protocols belong here.
- **Assumption-bound boundaries** describe behavior Loom cannot derive from
  ordinary logic, including PLLs, pads, bidirectional pins, SRAM macros, and
  vendor primitives. Each use names its contract and the evidence, theorem, or
  assumption connecting an implementation to it.
- **Tool bridges** exchange artifacts, traces, properties, and counterexamples
  with conventional tools. A bridge may strengthen evidence but may not add an
  external parser, simulator, or solver to a kernel theorem's hidden TCB.

Syntax is not an architectural layer. The facilities below must first have a
precise Lean API and semantics; convenient spelling belongs in
[`PRETTY.md`](PRETTY.md). In particular, streams, bus kinds, arbitration
policies, reset policies, memory configurations, and IP kinds are library
values rather than an expanding collection of language keywords.

### Typed components and external IP

A component is a reusable typed interface plus an implementation or behavioral
contract. Its interface contains packed ports with direction, semantic payload
type, and clock-domain ownership. Reset, combinational dependencies, latency,
and statefulness are explicit interface facts rather than conventions inferred
from signal names. An instance has a stable hierarchical path and may connect
only type-equal, direction-compatible endpoints. Width-only compatibility is
insufficient for nominal packed types.

There are three implementation classes:

1. An **internal component** contains an ordinary Loom implementation. Loom
   proves that instance elaboration and optional flattening preserve its
   component semantics. Flattened and hierarchy-preserving emission are views
   of the same instance graph, not distinct designs.
2. A **contracted component** has a technology-neutral transition or trace
   contract but no Loom body. It is an explicit cut point. Any theorem that
   depends on its behavior carries that contract as a named premise.
3. A **refined external component** pairs the same contract with checked
   evidence: a Lean refinement theorem, neutral-netlist equivalence, or an
   explicitly classified external result. Only a kernel-checked refinement or
   checked neutral equivalence can discharge a Loom logical proof obligation;
   a contract alone remains a premise and an external report remains external
   evidence.

The external-IP seam is therefore not arbitrary HDL interpolation. A leaf
declares its exact interface, clock/reset contract, state and latency contract,
allowed combinational paths, stable artifact identity, and implementation
binding. Unsupported parameters, unconnected required ports, multiple drivers,
domain-crossing connections, contract/version mismatches, and undeclared
combinational paths fail closed. Verilog, VHDL, FPGA, and ASIC bindings may all
implement one contract without entering generic imports.

Top-level pads and bidirectional pins terminate at this seam. The verified core
sees separate input, output, and output-enable signals; the physical binding
may join them into an `inout`. PLL lock, generated-clock quality, analog pad
behavior, SRAM electrical behavior, and vendor primitive semantics remain
named assumptions. Internal tri-state nets are not introduced.

The hierarchy milestone is complete only when Loom has:

- typed component definition and instantiation;
- deterministic instance paths and collision-free derived names;
- structural checks for ownership, directions, domains, and drivers;
- compositional component semantics;
- a proved flattening/refinement theorem;
- separate compilation without changing observable behavior; and
- one internal component and one assumption-bound external memory leaf used
  interchangeably behind the same contract.

### Same-clock streams and protocol libraries

A same-clock stream is a nominal payload carried by `valid`, `ready`, and
`payload`. A transfer occurs exactly on a domain tick for which both `valid`
and `ready` are true. While `valid` is true and no transfer occurs, the producer
must retain the payload and keep `valid` asserted. These obligations are part
of the stream contract; neither truthiness nor best-effort loss is implicit.
Empty payload observation is irrelevant unless `valid` is true.

Stream endpoints and combinators should be ordinary typed library values over
packed ports and components. The initial verified set should include direct
connection, register slice, skid buffer, FIFO, fork, join, mux, demux, width
adapter, mapper, and explicit lossy adapter. Each operator states its buffering,
latency, ordering, backpressure, and loss contract and carries a refinement to
an abstract transaction trace. Combinational ready/valid dependency cycles are
rejected structurally or broken by an explicitly buffered operator.

An asynchronous stream connection is never an implicit rewiring. It selects a
proved CDC adapter such as a synchronizer, pulse/toggle bridge, or asynchronous
queue and exposes that adapter's capacity, reset, recovery, and latency
contract. The existing `Chan` semantics and multiclock realizations should
provide this foundation rather than being duplicated by a second CDC system.

Bus protocols are typed compositions of streams and packed payloads. AXI,
APB, TileLink, Wishbone, or a machine-specific bus belongs in a library with:

- a configuration type fixing optional channels, ID/address/data widths, and
  supported protocol features;
- nominal request and response payload types;
- protocol monitors expressed as reusable safety properties;
- adapters whose ordering, response, buffering, and narrowing behavior is
  proved; and
- an explicit subset boundary when Loom does not implement an entire external
  standard.

No bus adapter may silently discard transactions, invent ordering, or cross a
clock domain. Unsupported bursts, atomics, reordering, or response modes fail
at construction. A minimal same-clock stream library should precede branded
bus libraries so protocol names do not conceal an unproved handshake core.

### Memory-port semantics

Memory behavior belongs in the core wherever it affects a cycle-visible
result. A neutral memory declaration should separate stored contents from a
typed list of ports. Every port records:

- owning clock domain;
- address, element, and physical-lane widths;
- read, write, or combined read/write capability;
- read latency in ticks of its owning domain;
- enable behavior and byte/bit write-mask granularity;
- read-during-write behavior for same-address collisions;
- relationships to other ports; and
- initialization/reset contract, if any.

Read-during-write behavior must be an explicit closed choice such as old data,
new data, unchanged output, or unspecified-by-contract. “Unspecified” is a
named nondeterministic premise and cannot be simulated as a convenient fixed
value. The semantics must also define simultaneous writes: conflicting writes
are either rejected, assigned an explicit priority, or left nondeterministic
by a named contract. Source order is not an accidental memory-port priority.

The first complete core profile should cover asynchronous read, synchronous
read, synchronous write, simple dual-port, and true dual-port memories. Mixed-
width ports require a single declared bit/lane mapping, alignment rule, and
endianness; invalid or overlapping accesses fail or follow an explicit
contract. Byte and bit enables update only the selected lanes. Resetless or
uninitialized contents begin as symbolic state, never silently as zero.

A neutral logical memory may refine to registers, an FPGA RAM, or an ASIC SRAM
macro. Register-bank lowering is a proved implementation. A target memory leaf
uses the external-component seam and must match the exact port, latency, mask,
collision, initialization, and domain contract. Area, timing, inference style,
and macro selection remain external. This division permits one logical SoC to
target FPGA and ASIC without pretending their memories have behavior that the
contract did not state.

### Lean-native plugins and services

Large generated systems need decentralized construction, but plugins are an
elaboration facility, not hardware semantics. A plugin has a typed manifest of
services it provides and requires, configuration values, component/port
resources it claims, and the components or connections it contributes. A
service key includes its Lean type; a width-compatible but semantically
different service cannot satisfy it.

Construction proceeds in explicit phases:

1. **declare** publishes requirements, provisions, and resource claims without
   reading unresolved services;
2. **negotiate** resolves unique and multi-provider services, configuration
   constraints, and optional capabilities;
3. **build** produces typed components, instances, connections, properties,
   and refinement obligations; and
4. **seal** rejects unresolved handles, dependency cycles, duplicate unique
   providers, conflicting resource claims, unstable names, or unconsumed
   required services and records an auditable manifest.

Service handles are single-assignment and may be consumed only after their
declared phase. Resolution is deterministic and independent of plugin list
order except where an explicit ordered policy says otherwise. An apparent
elaboration dependency cycle reports the service path that created it rather
than deadlocking or observing a partially built design.

Plugins may generate ordinary Lean data and use functions, recursion, types,
and proofs freely. They receive no escape from component typing, domain checks,
driver checks, channel-footprint checks, or contract closure. A plugin system
therefore enables NaxRiscv-scale configuration without becoming a second,
less-checked HDL. The first validation must assemble independently developed
producer and consumer plugins, replace one provider, diagnose a real cycle,
and show that two plugin orderings seal to the same canonical component graph.

### Pipelines, register maps, arbitration, and protocols

These facilities are verified libraries built on components, streams, packed
types, and ordinary state:

- A **pipeline** carries a typed set of payloads through named nodes and links.
  Links explicitly provide combinational forwarding, registered staging,
  buffering, stalling, flushing, or replay. The builder may derive transport
  wires and registers, but it must publish exact latency and prove transaction
  conservation and ordering under its stated stall/flush policy. Retiming is a
  refinement-preserving transform, not a syntactic rearrangement.
- A **register map** owns typed, non-overlapping address regions with alignment,
  access width, endianness, read/write permissions, reset values, and explicit
  side effects such as write-one-to-clear or read-to-clear. It derives bus
  decode, documentation, software constants, and proof obligations from that
  single declaration. Ambiguous decode and unsupported partial accesses fail
  closed.
- An **arbiter** names its policy: fixed priority, round robin, weighted, or a
  supplied proved policy. Safety guarantees mutual exclusion and transaction
  conservation. Starvation freedom is claimed only with explicit environment
  premises and a liveness proof; it is never inferred from the word “fair.”
- A **protocol component** packages endpoint types, legal traces, monitors,
  adapters, and optional progress assumptions. Composition proves that adapter
  output traces satisfy the receiving protocol rather than merely connecting
  equal-width wires.

The first CPU-scale gate should exercise payload propagation, backpressure,
flush, bypass, arbitration, and replacement of one service-provided pipeline
stage. LNP64mini need not be rewritten merely to demonstrate the framework;
the gate should expose pressure that a smaller hand-wired pipeline does not.

### Clock and reset modeling

Every state element and sequential port belongs to exactly one clock domain.
A domain specifies its logical active edge and reset-observation policy.
Schedule semantics determine which domain edges occur, including coincident
unrelated edges; they do not assume a frequency or phase relation that was not
declared.

State initialization and reset are distinct:

- **resetless** state has an unconstrained initial value unless a separate
  initialization contract is selected;
- **synchronous reset** is observed only on the domain's active edge;
- **asynchronous reset assertion** may dominate without a clock edge, while
  its release behavior and any required synchronization are explicit; and
- **boot/initialization values** are implementation contracts and are not
  silently treated as reset behavior.

Active polarity, reset value, and participation are declaration facts. A
clock enable is a guarded state transition in the same domain. A generated or
gated physical clock is instead an assumption-bound clock component with a
declared relation to its source; arbitrary logic may not become a clock.

Domain crossings remain typed and explicit. Single-bit levels, pulses,
monotonic counters, Gray snapshots, reset release, and bulk streams require
different verified adapters and contracts. A generic “synchronize” operation
that guesses from width is forbidden. Physical MTBF, pulse-width, skew,
placement, clock-quality, and reset-recovery requirements remain named target
requirements. PLLs and clock muxes sit behind component contracts rather than
adding analog behavior to the two-state core.

### Simulation, waveform, and conventional formal bridges

Loom's proved evaluator remains the reference executable semantics. A
conventional simulation layer should derive a signal database from component
paths and typed declarations, accept explicit clock/reset schedules and
environment drivers, and emit standard waveforms such as VCD or FST. Protocol
drivers and monitors are libraries over the same stream/bus contracts. A trace
records the exact design/artifact identity, schedule, inputs, and observation
schema so it can be replayed against the proved evaluator or an external HDL
simulator.

External simulators are differential or implementation-evidence producers,
not semantic authorities. Cosimulation must compare at declared observation
boundaries and report unsupported four-state values explicitly; it must not
coerce `X` or `Z` to zero and call the run equivalent.

A conventional property fragment may provide `assert`, `assume`, `cover`,
bounded temporal delay, `past`, `rose`, `fell`, and `stable` over typed Loom
expressions. Its Loom trace semantics is primary. SVA generation is accepted
only for the fragment with a documented semantic correspondence; unsupported
sampling regions, four-state operators, or event controls fail closed.
SymbiYosys and other engines remain untrusted search/proof producers.
Counterexamples should replay in Loom, and a successful external proof is
reported as external unless Loom checks an accepted proof certificate or a
separate theorem closes the result.

These bridges are complete when the same named property can run in the proved
simulator, emit to the supported SVA subset, replay an external counterexample,
and distinguish a checked Loom proof from an external `PASS` in the report.

### Arithmetic conveniences

Additional arithmetic should preserve Loom's width-explicit, two-state
semantics. The constructor audit should cover arithmetic right shift, reduction
AND/OR/XOR, rotates, dynamic bit selection, fixed-width dynamic part selection,
widening add/sub with carry or borrow, and explicit saturating arithmetic.
Every operation states operand/result widths, signed interpretation, shift
amount treatment, out-of-range behavior, and total behavior at exceptional
inputs. Unsized literals never justify silent truncation.

Operations enter the core only when they provide a useful primitive semantic
or enable materially better compilation/proof structure. Derived rotates,
reductions, saturation, and fixed-point arithmetic should otherwise be verified
library definitions. Nominal signed, unsigned, and fixed-point facades may
improve typing without changing the durable `BitVec` representation. Dynamic
selection, if added, requires direct evaluator, compiler, footprint,
bit-blasting, and bounds theorems rather than a pretty-only lowering.

Four-state arithmetic, implicit signedness, context-dependent result widths,
silent narrowing, and tool-dependent division or shift behavior remain
excluded.

### Explicit exclusions

The expanded SoC surface does not admit arbitrary event controls, inferred
latches, unrestricted multiple drivers, internal tri-state logic, four-state
`X` as ordinary computation, implicit CDC crossings, target-specific
primitives in generic designs, or synthesis and physical implementation.
These exclusions are enabling constraints: they keep transition semantics
total, composition checkable, and FPGA/ASIC neutrality credible.

## Reusable machine infrastructure

The reusable control plane lives in Loom. Acc8 is the independent demonstrated
port: it uses the same runner, derived coordinate coverage, and structured
results as LNP64mini, and its bespoke comparator and recursive runner are gone.
LNP64mini's core and component tests use Design-derived execution and generic
structured results; its prior parallel runners and duplicated comparison
metadata are gone. Component adapters reuse the same control plane without
standardizing their machine-specific inputs.

The boundary remains deliberate:

- Loom owns result/control policy, complete coordinate planning, closed named
  exclusions, deterministic writes, byte identity, freshness, and command
  diagnostics.
- Machines own inputs, environment and peripheral policy, reference adapters,
  programs, expected architectural outcomes, and properties.
- Boards own transports, probes, deployment configuration, and read-path
  health policy, while attaching Loom artifact identity to observations.

Test-program shapes remain machine-side. Dwell, park/wake, replicated spawn,
and loop-until-refused are useful patterns to name in prose, not code to
generalize into Loom.

Generic certified-DAG runner packaging, multi-design orchestration, and a
standard open-Design environment interface remain deferred. The interface must
be co-designed against at least two machines including a non-CPU, and must not
encode `MiniIn`, command-index/data conventions, LNP64mini FSM widths, or its
DDR latency model.

## Scope boundary

Loom's kernel-facing architecture must be agnostic to:

- FPGA vendor and device family;
- FPGA versus ASIC implementation;
- synthesis, mapping, placement, and routing tool;
- netlist serialization format;
- standard-cell or FPGA-primitive library.

The durable equivalence boundary is a small, technology-neutral logical
netlist. Vendor formats and cells stay outside Loom. External converters may
produce the neutral interchange, but Loom does not maintain their target-cell
semantics as part of its roadmap.

### Loom owns

Loom should own:

- the typed design language and its transition semantics;
- typed component interfaces, instance graphs, and compositional semantics;
- technology-neutral clock/reset and memory-port behavior;
- proved compilation into a small logical hardware IR;
- refinement-preserving logical transformations;
- derived and proved executable models;
- a technology-neutral logical-netlist IR;
- structural validation of that IR;
- Boolean and sequential semantics for that IR;
- equivalence-miter and CNF construction;
- proof-certificate checking independent of the solver;
- reports that distinguish theorems, checked certificates, assumptions,
  external comparisons, and measurements.

### Loom does not own

Loom should not attempt to own or reverify:

- synthesis optimization passes;
- technology mapping;
- arbitrary Verilog or SystemVerilog elaboration;
- Yosys, Vivado, Quartus, Synopsys, Cadence, or another EDA implementation;
- an open-ended catalogue of FPGA primitives;
- ASIC Liberty libraries or foundry-cell behavior;
- FPGA bitstream semantics;
- placement, routing, clock-tree synthesis, DFT, power intent, or GDS;
- timing closure or physical correctness.

Those systems remain untrusted producers or external sign-off steps. Loom's
job is to reject an incorrect logical result, not to prove how a tool computed
it.

## The intended artifact boundary

The core flow should have this shape:

```text
Lean Design
    │
    ├── proved simulator and property theorems
    │
    ▼
proved logical compilation
    │
    ▼
µVerilog / logical module semantics
    │
    ├────────────── side A
    │
external synthesis tool and converter
    │
    ▼
technology-neutral LogicalNetlist
    │
    ├────────────── side B
    ▼
proved equivalence miter
    │
    ▼
CNF → untrusted solver → checked proof certificate
```

The synthesis tool is not trusted for correctness: a wrong logical output
should make the miter satisfiable. Loom consumes only its documented neutral
interchange. The claim that a tool-specific source file or mapped artifact was
converted into that interchange correctly is external unless separately
proved, and must be reported as such.

The preferred synthesis checkpoint is before target-specific technology
mapping. It should contain only a deliberately small logical vocabulary, such
as:

- primary inputs and outputs;
- current-state and next-state boundaries;
- constants;
- inversion;
- a small complete Boolean basis, such as AND/XOR/MUX;
- explicit opaque state or memory cut points.

The exact basis may change without changing the scope rule: it must describe a
Boolean transition system, not a vendor architecture.

## Claim ladder

Loom reports must distinguish these claims:

1. **Design theorem.** A property holds for the Lean transition system.
2. **Compiler theorem.** The logical IR implements that transition system.
3. **Logical equivalence theorem.** An imported neutral netlist implements the
   logical IR for the checked boundary.
4. **Conversion claim.** Particular tool-specific bytes produced the checked
   neutral netlist.
5. **Implementation evidence.** A mapped FPGA or ASIC artifact was produced
   from the checked logical checkpoint.
6. **Physical evidence.** Timing, area, routing, board, or silicon measurements
   were observed.

Only the first three are Loom proof obligations. The last three are external
evidence and must never be presented as kernel consequences.

Logical equivalence does not establish:

- four-state HDL behavior beyond the stated two-state boundary;
- clock-domain correctness;
- analog or hard-macro behavior;
- timing;
- physical implementation correctness;
- identity between a logical netlist and a bitstream or GDS artifact.

## External conversion boundary

Loom defines and validates one small neutral interchange. A synthesis tool may
emit it directly, or an external converter may translate another format into
it. Tool- and technology-specific conversion is not a Loom capability
workstream.

The neutral input must contain enough information for Loom to check:

- widths, node kinds, and graph references;
- input, output, current-state, and next-state boundaries;
- combinational acyclicity;
- exact drivers;
- opaque state and memory cut points;
- explicit exclusions;
- an identity for the neutral bytes actually checked.

Loom must fail closed on malformed or unsupported neutral input. It does not
need to recognize the original synthesis format or mapped cell library.

There is no current netlist checker. Any future integration belongs outside
the generic Loom library and may produce the neutral interchange like any
other external flow.

## FPGA and ASIC neutrality

FPGA and ASIC designs share the same core obligation at Loom's boundary:
their logical next-state and output functions must match the verified design.

Target-specific mapping happens later:

```text
LogicalNetlist
    ├── FPGA LUT/carry/register mapping
    └── ASIC standard-cell/macro mapping
```

Loom may record external equivalence or implementation reports supplied by
these flows. It does not interpret either target library or mapped artifact.

## What the finished toolchain should feel like

A user should declare state and behavior once, prove properties at the natural
abstraction level, select verified logical transformations, emit a small
artifact, and receive a report whose claims and assumptions are unambiguous.

The intended workflow has these properties:

1. **One declaration per fact.** Names, widths, reset values, interfaces,
   simulator fields, and comparison coverage derive from one declaration.
2. **Local proof cost.** An invariant proof sees only rules that can affect its
   support.
3. **Provable logical optimization.** A transformation carries a refinement
   theorem rather than relying on a comment or downstream synthesis behavior.
4. **Fast views remain proved views.** Specialized simulators and generators
   come with kernel-checked equality or soundness theorems.
5. **External evidence is translation validation.** Synthesis outputs are
   checked, not trusted as proofs and not reimplemented inside Loom.
6. **Physical predictions remain estimates.** Abstract cost models may guide
   engineering, but target measurements retain their provenance and
   uncertainty.
7. **No green result by omission.** New state, ports, operators, cut points,
   and assumptions are checked or explicitly reported.

## Non-negotiable constraints

- The publication theorem retains its documented axiom closure.
- No convenience feature silently adds a compiler, solver, printer, parser,
  synthesis tool, or external converter to the theorem TCB.
- Generic Loom definitions contain no FPGA-vendor, ASIC-library, or
  synthesis-tool dependency.
- Unknown logical constructs fail closed.
- Counterexamples improve definitions and designs; they are not hidden by
  weakened prose.
- Public documentation describes the current state. Version control and
  compact evidence records preserve history.
- Target measurements never become universal facts without a named target,
  configuration, tool version, and controlled baseline.

## Capability workstreams

### W1 — typed, single-source designs

Typed register, memory, input, and output handles should remain the sole source
for widths and names. Generated adapters, comparators, debug descriptions, and
coverage checks must derive from those declarations.

Typed interfaces cover LNP64mini and the migrated examples. Their state
adapters, comparison plans, debug taps, output selection, coverage, and
memory-policy reports derive from typed handles, properties, or the resulting
`Design`. Designs authored directly in the stable core EDSL remain supported;
they do not require a parallel typed schema. Independent oracles may remain
for diagnostic diversity, but never as an unlabelled production semantic
mirror. New facilities must preserve this single-source discipline rather
than introduce parallel metadata.

Packed hardware types extend that discipline from scalar coordinates to
structured values. One packed declaration owns field names, widths, layout,
semantic pack/unpack, expression projections, typed state/storage/channel
handles, debug views, and source rendering. None may be restated in a separate
port map or comparator schema, and equal total width must not make two distinct
packed types assignment-compatible. `Act.writeSlice` is the sole core mechanism
for partial packed-register lvalues; it must remain a bounded static-slice
operation whose compiler and simulators preserve accumulator ordering and
pre-cycle RHS evaluation.

### W2 — property-directed proof automation

Footprints, support inference, frame rules, projected actions, and cycle
tactics should make proof effort scale with a property's dependency cone.
Open-system assumptions must remain explicit in theorem statements.

The current register/memory footprint machinery, projected cycles, expression
properties, and generated support checks establish this direction. Further
work should improve composition and proof ergonomics without changing machine
semantics.

### W3 — verified logical transformations

Balancing, retiming, duplication, and pipelining belong in Loom only when
expressed as logical design transformations with refinement theorems.

Whether a downstream tool preserves a particular structural optimization is
an external measurement, not a reason to encode that tool's passes in Loom.
Cost information may guide transform selection but does not replace semantic
legality.

### W4 — technology-neutral logical equivalence

W4's destination is equivalence over `LogicalNetlist`. Synthesis formats,
FPGA primitives, ASIC cells, and other mapped technologies are outside that
destination.

The generic layer should provide:

- exact drivers and dependencies;
- certified acyclicity for combinational cones;
- explicit state and opaque-memory boundaries;
- total, fuel-independent reference semantics for validated graphs;
- memoized evaluation whose correctness is proved;
- vector and named-port routing;
- bidirectional CNF correctness;
- miter soundness;
- checked UNSAT certificates and useful SAT counterexamples.

There is currently no `LogicalNetlist` implementation. Loom's generic CNF and
proved LRAT infrastructure remains available, but graph semantics, structural
validation, and the equivalence connection must be designed directly around
the neutral boundary.

The implementation order is:

1. Define the minimal `LogicalNetlist` IR and its semantics.
2. Define and prove graph evaluation, routing, CNF, and miter operations on
   that IR.
3. Connect µVerilog side A directly to the neutral equivalence theorem.
4. Define a small, documented neutral serialization and fail-closed parser.
5. Add neutral graph fixtures and generated positive and negative controls.
6. Exercise LNP64mini through the neutral boundary without mentioning its
   synthesis producer in the theorem.
7. Demonstrate producer independence by checking neutral graphs with different
   provenance, without importing either producer's semantics.

Generic logical-graph proofs are in scope. Adding FPGA primitives, ASIC
standard cells, or synthesis-tool graph behavior is not.

### W5 — derived simulation

Fast evaluators, DAG evaluators, state comparators, and test matrices should be
generated from `Design` and connected to it by proofs. Hand-maintained ISS or
emulator models remain useful differential oracles, but their non-derived
status must be explicit.

The current certified DAG evaluator and derived state comparison are the
primary path. Further work should extend their use and performance rather than
introduce additional manually synchronized simulators.

### W6 — abstract cost guidance

Loom may attach symbolic, target-parameterized cost vectors to proved
transformations. This is useful for choosing among semantically valid designs.

The generic layer may describe quantities such as logical depth, node count,
fanout, state bits, and abstract memory demand. FPGA utilization, ASIC density,
timing, packing, and routing are measurements supplied by target profiles and
external tools. They are not portable theorems and are not requirements for
the logical-equivalence core.

### W7 — typed hierarchy and IP contracts

Define typed component interfaces, deterministic instance graphs,
compositional semantics, and proved flattening before adding convenient
instance syntax. Then add the external-component seam with exact
clock/reset/latency/dependency contracts and artifact-bound implementations.
The acceptance gate is substitution of an internal memory implementation and
an external memory leaf behind one unchanged client and contract, with every
remaining assumption visible in the result.

### W8 — streams and bus protocols

Build a verified same-clock valid/ready stream and its transaction-trace
refinement, followed by buffered combinators and structural ready/valid-loop
checking. CDC stream adapters must reuse the existing proved channel
realizations. Bus libraries follow only after the stream basis is stable, and
must state the exact supported subset rather than borrowing a standard's name
for an incomplete, unchecked collection of wires.

### W9 — complete memory ports

Extend neutral memory semantics with synchronous reads, masks, explicit
read-during-write and write-collision policies, dual-port operation, and
declared mixed-width lane mapping. Each addition must land together in the
reference evaluator, optimized evaluator, compiler, footprints, proofs,
emission, and external-memory contract. Register-bank refinement is the first
portable implementation; FPGA RAM and ASIC SRAM bindings remain evidence- or
assumption-bound leaves.

### W10 — plugin and service construction

Implement the phased, typed, deterministic service resolver over component
construction. It must fail closed on missing or duplicate services, cycles,
unresolved handles, and resource conflicts, and produce a canonical auditable
manifest. No plugin API graduates until order-independence and provider
replacement are demonstrated on separately authored plugins.

### W11 — reusable SoC libraries

Build pipeline, arbitration, register-map, protocol-monitor, and adapter
libraries from packed values, streams, components, and ordinary state. Every
library reports exact buffering/latency and separates safety from conditional
progress. Generated documentation and software views derive from the same
register-map declaration as the hardware and its proofs.

### W12 — clock and reset completeness

Generalize domain-owned state to distinguish resetless initialization,
synchronous reset, asynchronous assertion, synchronized release, polarity,
and clock enable. Preserve schedule semantics for coincident unrelated edges.
Add distinct verified CDC libraries for levels, pulses, snapshots, reset
release, and streams; do not introduce a width-directed generic synchronizer.
Generated/gated clocks, PLLs, and clock muxes remain contracted boundaries with
named physical requirements.

### W13 — ecosystem bridges

Derive hierarchical signal metadata, replayable traces, and VCD/FST waveforms
from the design. Provide differential adapters to external simulators and a
small Loom-defined temporal-property fragment with a fail-closed SVA export.
External simulation and SymbiYosys results remain classified evidence unless
connected to a checked certificate; counterexamples should replay against the
reference semantics.

### W14 — arithmetic completion

Audit arithmetic right shift, reductions, rotations, dynamic selection,
carry/borrow, saturation, and fixed-point helpers against actual SoC uses.
Prefer proved library definitions; add a core constructor only when its direct
semantics, compilation, or proof structure is materially valuable. Every
accepted operation ships with explicit width/signedness rules and all semantic,
compiler, evaluator, CNF, and diagnostic coverage required by its role.

### Derived debug instrumentation

Debug descriptions should derive typed dependencies and observation layouts
from the design. Passive observation can be generated without adding a second
machine model. Any hold, halt, reset, clock crossing, wrapper capture, scan,
or transport behavior remains an explicit implementation-boundary decision.

The generic facility must not depend on BSCAN, a particular FPGA wrapper, or a
vendor debug primitive. Existing board-specific generation is external
integration code, not part of Loom's generic destination. Loom does not model
debug transports.

## Scope test for new work

Before adding netlist or implementation work, ask:

1. Does this define or prove a fact about a technology-neutral Boolean
   transition system?
2. Could the theorem be reused unchanged with a different FPGA vendor?
3. Could it be reused unchanged for an ASIC logical netlist?
4. Could another synthesis tool supply the input without changing the proof?

If all answers are yes, the work may belong in generic Loom. It belongs in the
semantic core only when it changes observable transition behavior or is needed
to state a durable composition boundary; otherwise prefer a verified library
or tool bridge. Reuse alone is not a reason to enlarge the core language.

If the work mentions a vendor cell, tool-specific synthesis serialization,
standard-cell library, board primitive, bitstream, timing database, or physical
tool, it belongs outside the generic Loom roadmap. It may provide external
evidence, but it must not add core semantics or proof obligations.

## Success criteria

Loom reaches the intended shape when:

- a substantial design changes at one declaration site and all derived views
  update or fail with named obligations;
- a structured hardware value changes at one field declaration and its packed
  width, projections, state/storage/channel types, observations, proofs, and
  emitted vector layout update or fail from that same source;
- proofs recheck in proportion to affected logic;
- logical transformations compose through refinement theorems;
- the emitted logical artifact is connected to the design;
- a neutral synthesized netlist is checked by the same generic equivalence
  theorem regardless of producer or eventual FPGA/ASIC target;
- switching synthesis tools requires only external production of the neutral
  interchange, not new Loom proofs;
- switching FPGA vendors or moving to ASIC does not change Loom's logical
  semantics;
- a component client can substitute an internal implementation or contracted
  external leaf without changing its typed interface or abstract proof;
- stream and bus composition preserves transactions under explicitly stated
  buffering, backpressure, ordering, and progress premises;
- every memory port has explicit latency, mask, collision, initialization, and
  domain behavior, and target memories match that exact contract;
- plugin order does not change the sealed component graph unless an explicitly
  ordered policy is present, and every provided/required service is recorded;
- resetless state, reset behavior, clock-domain crossings, and generated-clock
  assumptions are distinguishable in both semantics and reports;
- external waveforms, counterexamples, SVA results, and implementation reports
  bind to exact artifacts and remain visibly separate from checked Loom
  theorems;
- every conversion assumption, exclusion, cut point, and physical assumption
  appears in the release report;
- target measurements remain useful without being confused with theorems.

The central discipline is simple:

> Loom proves designs and technology-neutral logical equivalence. External
> tools produce the neutral checkpoint and choose implementations; physical
> flows validate the rest.
