# The intended shape of Loom

Loom's organizing goal is:

> A design, its executable behavior, its proofs, its tests, its emitted
> logical artifact, and its external implementation evidence should be derived
> views of the same Lean value, with every non-derived link named as an
> assumption.

Loom is a hardware-design and proof system. It is not a synthesis tool, an
FPGA framework, an ASIC flow, or a formal reimplementation of an EDA tool.

This document describes the intended current destination. Current results are
recorded in [`STATUS.md`](STATUS.md), and the authoritative trust boundary is
recorded in [`TCB.md`](TCB.md).

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

Current typed interfaces cover the main examples and LNP64mini. Remaining work
is migration and removal of duplicated stringly metadata, not creation of
parallel schemas.

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

If all answers are yes, the work belongs in Loom's generic core.

If the work mentions a vendor cell, tool-specific synthesis serialization,
standard-cell library, board primitive, bitstream, timing database, or physical
tool, it belongs outside the generic Loom roadmap. It may provide external
evidence, but it must not add core semantics or proof obligations.

## Success criteria

Loom reaches the intended shape when:

- a substantial design changes at one declaration site and all derived views
  update or fail with named obligations;
- proofs recheck in proportion to affected logic;
- logical transformations compose through refinement theorems;
- the emitted logical artifact is connected to the design;
- a neutral synthesized netlist is checked by the same generic equivalence
  theorem regardless of producer or eventual FPGA/ASIC target;
- switching synthesis tools requires only external production of the neutral
  interchange, not new Loom proofs;
- switching FPGA vendors or moving to ASIC does not change Loom's logical
  semantics;
- every conversion assumption, exclusion, cut point, and physical assumption
  appears in the release report;
- target measurements remain useful without being confused with theorems.

The central discipline is simple:

> Loom proves designs and technology-neutral logical equivalence. External
> tools produce the neutral checkpoint and choose implementations; physical
> flows validate the rest.
