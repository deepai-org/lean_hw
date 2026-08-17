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

This document records unfinished architectural destination and durable scope
rules. Current capabilities belong in [`README.md`](README.md), checked results
in [`STATUS.md`](STATUS.md), multiclock behavior in
[`MULTICLOCK.md`](MULTICLOCK.md), and the authoritative trust boundary in
[`TCB.md`](TCB.md).

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

### Hierarchy and external-IP completion

Multiclock fragments already reuse ordered child island certificates and
transport their execution theorems through compatible parents. Contract-bound
external islands already provide an exact, assumption-retaining emission seam.
The remaining hierarchy milestone is semantic separate compilation rather
than structural assembly:

- prove that canonical graph flattening refines component composition;
- reuse sealed child semantic certificates through hierarchy-preserving
  single-clock component compilation instead of certifying one flattened
  `Design`;
- support separate compilation without changing observable behavior;
- make hierarchy-preserving and flattened emission certified views of the same
  instance graph; and
- qualify one internal memory and one assumption-bound external memory leaf as
  interchangeable implementations of the same exact client contract.

Multidomain contracted leaves such as PLLs, PHYs, and dual-clock macros must
instantiate at the `SystemFragment` boundary rather than masquerading as
single-clock components. Top-level pads expose separate logical input, output,
and output-enable signals; joining them into a physical `inout`, along with
PLL quality and analog or electrical behavior, remains a named external
assumption. Internal tri-state nets remain excluded.

### Same-clock streams and protocol libraries

A same-clock stream is a nominal payload carried by `valid`, `ready`, and
`payload`. A transfer occurs exactly on a domain tick for which both `valid`
and `ready` are true. While `valid` is true and no transfer occurs, the producer
must retain the payload and keep `valid` asserted. These obligations are part
of the stream contract; neither truthiness nor best-effort loss is implicit.
Empty payload observation is irrelevant unless `valid` is true.

Attach component-derived transaction traces to the existing direct, mapper,
and register-slice operators, then add skid buffer, FIFO, fork, join, mux,
demux, width adapter, and explicit lossy adapter. Each operator states its
buffering, latency, ordering, backpressure, and loss contract and carries a
refinement to an abstract transaction trace. Combinational ready/valid
dependency cycles are rejected structurally or broken by an explicitly
buffered operator.

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
macro. A target memory leaf uses the external-component seam and must match the
exact port, latency, mask, collision, initialization, and domain contract.
Area, timing, inference style, and macro selection remain external. This
division permits one logical SoC to target FPGA and ASIC without pretending
their memories have behavior that the contract did not state.

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
semantics. The remaining constructor audit covers rotates, dynamic bit
selection, fixed-width dynamic part selection, and fixed-point helpers. Every
operation states operand/result widths, signed interpretation, shift-amount
treatment, out-of-range behavior, and total behavior at exceptional inputs.
Unsized literals never justify silent truncation.

Operations enter the core only when they provide a useful primitive semantic
or enable materially better compilation/proof structure. Rotates and
fixed-point arithmetic should otherwise be verified library definitions.
Nominal fixed-point facades may improve typing without changing the durable
`BitVec` representation. Dynamic selection, if added, requires direct
evaluator, compiler, footprint, bit-blasting, and bounds theorems rather than a
pretty-only lowering.

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

1. **Local proof cost.** An invariant proof sees only rules that can affect its
   support.
2. **Provable logical optimization.** A transformation carries a refinement
   theorem rather than relying on a comment or downstream synthesis behavior.
3. **External evidence is translation validation.** Synthesis outputs are
   checked, not trusted as proofs and not reimplemented inside Loom.
4. **Physical predictions remain estimates.** Abstract cost models may guide
   engineering, but target measurements retain their provenance and
   uncertainty.

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

## Remaining capability workstreams

Workstream identifiers are retained for continuity with issues and historical
plans; completed workstreams are no longer repeated here.

### W2 — property-directed proof automation

Footprints, support inference, frame rules, projected actions, and cycle
tactics should make proof effort scale with a property's dependency cone.
Open-system assumptions must remain explicit in theorem statements.

Further work should improve composition and proof ergonomics without changing
machine semantics.

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

### W6 — abstract cost guidance

Loom may attach symbolic, target-parameterized cost vectors to proved
transformations. This is useful for choosing among semantically valid designs.

The generic layer may describe quantities such as logical depth, node count,
fanout, state bits, and abstract memory demand. FPGA utilization, ASIC density,
timing, packing, and routing are measurements supplied by target profiles and
external tools. They are not portable theorems and are not requirements for
the logical-equivalence core.

### W7 — typed hierarchy and IP contracts

Prove the semantic flattening/refinement boundary, reuse child certificates
through hierarchy-preserving compilation, and support separate compilation.
The remaining acceptance gate is substitution of an internal memory
implementation and an external memory leaf behind one unchanged client and
exact contract, with every residual assumption visible in the result.

### W8 — streams and bus protocols

Build a verified same-clock valid/ready stream and its transaction-trace
refinement, followed by buffered combinators and structural ready/valid-loop
checking. CDC stream adapters must reuse the existing proved channel
realizations. Bus libraries follow only after the stream basis is stable, and
must state the exact supported subset rather than borrowing a standard's name
for an incomplete, unchecked collection of wires.

### W9 — complete memory ports

Finish integrating the typed port policies through the optimized evaluator,
compiler, footprints, proofs, emission, and exact external-memory contract.
Complete symbolic resetless initialization and any still-unrepresented mixed-
width or collision contracts without assigning accidental source-order
semantics. FPGA RAM and ASIC SRAM bindings remain evidence- or
assumption-bound leaves.

### W11 — reusable SoC libraries

Extend the initial pipeline, arbitration, checked register-map, monitor, and
adapter libraries into a coherent SoC library set. Every operator must report
exact buffering/latency, preserve ordered payload traces, and separate safety
from conditional progress. Generated documentation and software views derive
from the same checked register-map declaration as the hardware and its proofs.

### W12 — clock and reset completeness

Generalize domain-owned state to distinguish resetless initialization,
asynchronous assertion, synchronized release, polarity, and clock enable.
Add distinct verified CDC libraries for levels, pulses, snapshots, and reset
release; do not introduce a width-directed generic synchronizer. Generated or
gated clocks, PLLs, and clock muxes remain contracted boundaries with named
physical requirements.

### W13 — ecosystem bridges

Bind waveform recording to theorem-bound artifact bundles, add FST and robust
external-simulator adapters, and establish a tested semantic correspondence
for the supported SVA subset. External simulation and SymbiYosys results remain
classified evidence unless connected to a checked certificate;
counterexamples should replay against the reference semantics.

### W14 — arithmetic completion

Finish the SoC-driven audit of rotations, dynamic selection, and fixed-point
helpers. Prefer proved library definitions; add a core constructor only when
its direct semantics, compilation, or proof structure is materially valuable.
Every accepted operation ships with explicit width/signedness rules and all
semantic, compiler, evaluator, CNF, and diagnostic coverage required by its
role.

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

- proofs recheck in proportion to affected logic;
- logical transformations compose through refinement theorems;
- a neutral synthesized netlist is checked by the same generic equivalence
  theorem regardless of producer or eventual FPGA/ASIC target;
- switching synthesis tools requires only external production of the neutral
  interchange, not new Loom proofs;
- switching FPGA vendors or moving to ASIC does not change Loom's logical
  semantics;
- stream and bus composition preserves transactions under explicitly stated
  buffering, backpressure, ordering, and progress premises;
- every memory port has explicit latency, mask, collision, initialization, and
  domain behavior, and target memories match that exact contract;
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
