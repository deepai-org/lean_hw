# Loom — hardware design and proof in Lean 4

Loom is a technology-neutral hardware language, verifier, simulator, and
structural Verilog compiler embedded in Lean 4. One typed `Design` is the
source for executable semantics, proofs, tests, interfaces, an optimized
simulator, and emitted RTL.

Loom supports ordinary synchronous designs and typed composition across clock
domains. It is not a synthesis tool or an FPGA-vendor framework: FPGA and ASIC
synthesis, technology mapping, place and route, timing closure, and physical
signoff remain downstream.

The project is especially interested in two boundaries that hardware flows
often leave informal:

- the simulator used during development is theorem-connected to the same
  `Design` semantics as the compiler; and
- selected release theorems bind the exact rendered UTF-8 bytes presented to
  downstream tools, not merely a nearby internal representation.

## Quick start

Install [Elan](https://lean-lang.org/lean4/doc/quickstart.html), then run:

```console
git clone https://github.com/deepai-org/lean_hw.git
cd lean_hw
lake build
lake test
lake exe audit
```

`lean-toolchain` pins Lean 4.28.0, and `lake-manifest.json` pins Lean
dependencies. The generic build requires no Verilog simulator, synthesis
tool, FPGA software, or hardware.

The broader reproduction wrapper exercises emission, artifact binding, and
available external corroboration:

```console
scripts/reproduce.sh
```

Optional legs report `PASS`, `FAIL`, or `SKIP`; a successful wrapper does not
mean that every host-dependent tool ran. See [STATUS.md](STATUS.md) for the
last recorded gate results and [REPRODUCING.md](REPRODUCING.md) for the review
tiers.

## Writing hardware

The friendly authoring layer lowers to the small, typed `Loom.Hw.Design` core.
For example:

```lean
import Loom.Hw.Dsl

open Loom.Hw Loom.Hw.Dsl

hardware satcounter where
  output reg count : 8
  output reg saturated : 1

  rule tick :=
    if count == 255 then
      saturated <- 1
    else
      count <- count + 1

#trace_cycle design with {} from { count := 254 }
#run_hardware design for 256 cycles
```

A synchronous cycle has a deliberately simple meaning: every right-hand side
reads the pre-cycle state, enabled writes commit at the edge, and a later write
to an overlapping destination wins. The language checks widths, declarations,
static slices, endpoint direction, and other structural obligations while
lowering. Informational lints call out easy-to-misread constructs such as
read-after-write, overlapping writes, unguarded channel operations, and costly
dynamic register-family selection.

The authoring surface includes:

- typed registers, inputs, outputs, register families, and memories;
- design-local constants and named finite-state encodings;
- guarded rules, conditionals, exhaustive cases, local expression lets, and
  static generate loops;
- modular arithmetic, signed and unsigned comparisons, logical and arithmetic
  shifts, multiplication, unsigned division and remainder, concatenation,
  slices, and explicit extension; and
- inspection commands that show reconstructed hardware, execute cycles, and
  report timing without creating a second semantics.

Multiplication emits neutral Verilog `*`, leaving DSP, standard-cell, or logic
mapping to the downstream flow. `Expr.umulWide` and `Expr.smulWide` retain the
full unsigned or two's-complement product. Division and remainder are total:
`a / 0 = 0` and `a % 0 = a`; Loom emits explicit guards rather than inheriting
Verilog unknowns for a zero divisor.

The complete syntax contract and its deliberate omissions are documented in
[PRETTY.md](PRETTY.md). [TUTORIAL.md](TUTORIAL.md) is the guided introduction.

## Packed and nested values

Packed types preserve semantic identity instead of treating every interface as
an interchangeable bit vector:

```lean
packed struct Header where
  tag : 3
  address : 5

packed struct Packet where
  header : Header
  payload : 16

hardware packet_register where
  input wire incoming : Packet
  output reg pending : Packet

  rule capture := {
    pending.header <- incoming.header,
    pending.payload <- incoming.payload
  }
```

Nested packed structs, registers, inputs, outputs, memories, and channels lower
to one padding-free, first-field-MSB vector. Nested projection and partial
assignment compose static field coordinates; they introduce no hidden state,
logic stage, or latency. Partial writes retain the normal pre-cycle-read and
ordered last-write-wins semantics.

Packed types are nominal. Equal width does not make two records assignment
compatible:

```lean
Destination {
  opcode := source.command       -- semantic conversion: map fields explicitly
  payload := source.data
}

reinterpret source to WireImage -- representation conversion: preserve every bit
```

`reinterpret` requires definitionally equal packed widths and lowers exactly
to `WireImage.fromBits(source.bits)`. Loom never infers field meaning,
truncation, extension, or whole-record arithmetic.

## Derived execution and proof support

A `Design` contains typed declarations and an ordered action list. From that
value Loom derives:

- **Reference semantics.** `Design.cycle` and open-design semantics define the
  mathematical transition system.
- **Fast execution.** `FastEval` uses indexed state; `DagEval` shares expression
  subtrees across the whole cycle. A structural certificate is checked before
  execution, and cycle/run theorems relate the optimized evaluator to `Design`
  for arbitrary states, inputs, and cycle counts.
- **Typed observations.** Register and memory handles resolve to simulator
  slots with checked names and widths. `Design.coords` derives the comparison
  surface so a new architectural coordinate cannot silently disappear from
  derived lockstep coverage.
- **Proof support.** Footprints, support inference, frame rules, projected
  actions, `ExprProperty`, and `TransitionProperty` focus invariants on the
  rules and state they actually depend on.
- **Structured test results.** `Loom.Runner` provides common run control,
  immediate mismatch output, explicit coverage, and structured outcomes.
- **Emission.** The proved compiler lowers the same `Design` to µVerilog;
  structural checks and deterministic rendering produce neutral RTL.

Independent ISS or external RTL simulation can still be useful corroboration,
but neither is the primary semantic implementation. LNP64mini's former
hand-maintained cycle ISS has been removed; its primary simulator and expected
architectural observations derive from its `Design`.

## Multiclock systems

Clock islands remain ordinary synchronous `Design`s. Typed channels are the
normal application-level crossing, and realization is selected separately:

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

The application surface is intentionally small: hardware, clocks, typed
channels, guarded send/receive, and an explicit realization. Packed payloads
use the same channel path. Advanced users can inspect or replace the stock
realization without exposing Gray pointers or raw valid/ready signals in
ordinary application logic.

The checked System layer provides:

- explicit clock relations and executable schedule replay;
- fail-closed island, endpoint, depth, reset-policy, and realization checks;
- schedule-quantified lifting of ordinary island invariants;
- FIFO capacity, ordering, conservation, and storage-collision results;
- compiler-produced same-clock FIFOs and portable asynchronous Gray-pointer
  control, synchronizer, and register-bank storage Designs;
- one refinement-backed physical binding per connection;
- a derived crossing inventory, typed timing description, reset-delivery
  intent, and technology-neutral physical requirements; and
- certified per-island DAG execution plus exact structural System emission.

Normal emission produces readable Markdown reports; programmatic clients use
the underlying typed inventory rather than CSV or TSV sidecars. A physical
backend must report every requirement as `PASS`, `FAIL`, `SKIP`, or
`UNCONSTRAINED`. A target signoff report also binds the device, tool/version,
run/seed, exact RTL, neutral-intent, emitted-constraint, and routed-design
hashes, the implementation run's matching RTL/constraint input hashes, and
post-synthesis object resolutions.
Generic Loom emission never manufactures a physical `PASS`.

The portable register implementation is shared by FPGA and ASIC flows. A
target profile may instead bind a compatible FPGA RAM, ASIC SRAM, or
synchronizer leaf while recording its exact external assumption. This choice
does not alter the source channel semantics.

Timing remains visible. In particular, the current conservative registered
sink consumes at most once per two destination ticks under continuous traffic;
an opt-in destination-local buffered sink has a proved one-item-per-tick
steady-state contract and reports that distinct timing. Independent-reset
recovery also has a documented remaining whole-wrapper state-relation proof.
These are not hidden behind the general multiclock claim.

See [MULTICLOCK.md](MULTICLOCK.md) for the application model,
[MULTICLOCK_BOUNDARY.md](MULTICLOCK_BOUNDARY.md) for the precise digital versus
physical boundary, and [MULTICLOCK_PLAN.md](MULTICLOCK_PLAN.md) for remaining
work.

## What is proved

The generic compiler-correctness development covers registers, memory images
and ordered writes, combinational outputs, open-design inputs, and supported
expressions from `Design` to µVerilog module semantics.

The publication-facing declaration is:

```lean
theorem Loom.Release.Theorems.verifiedReleases :
  Nonempty Loom.Release.Theorems.VerifiedReleases
```

It packages fixed Acc8 and LNP64-µ processor artifacts plus a portable
two-clock `CertifiedRealizedSystem`. For the selected artifacts, the kernel
checks the semantic/compiler results and equality with the exact rendered byte
trees; the System member includes the literal `system.v` bytes traversed by its
emitter. The checked axiom closure is exactly:

```text
propext
Classical.choice
Quot.sound
```

Build that boundary independently with:

```console
scripts/build_verified_release.sh
```

This theorem is not a theorem about arbitrary Verilog, host files without the
documented association step, synthesis correctness, a placed netlist, timing,
or silicon. [TCB.md](TCB.md) is the authoritative statement;
[CONCRETE_SSA_BOUNDARY.md](CONCRETE_SSA_BOUNDARY.md) documents the Verilog text
boundary, and [TRUST.md](TRUST.md) gives the broader property limits.

## Scope and honest limits

Loom is vendor-, target-, and synthesis-tool-neutral at the semantic and proof
layers. Generic emission selects no FPGA family or memory profile and does not
depend on Yosys. External tools may consume Loom artifacts as evidence, but
their behavior is not silently imported into Loom's theorem.

Loom does not currently prove:

- preservation by synthesis or post-synthesis logical equivalence;
- metastability resolution, MTBF, timing closure, CDC-tool signoff, reset-tree
  delivery, or clock-tree behavior;
- vendor primitive, foundry cell, SRAM-macro, PDK, or proprietary-tool
  correctness;
- place and route, bitstream generation, ASIC layout, PPA, power, signal
  integrity, or silicon behavior; or
- properties of DMA, interrupts, debug, external agents, or platform behavior
  absent from the modeled design and its stated assumptions.

Loom emits a complete neutral description of the physical obligations it
knows about; FPGA and ASIC flows remain responsible for lowering and
discharging those obligations on a concrete target. There is currently no
post-synthesis equivalence checker in Loom.

## Included machines and evidence

| Machine | Role |
|---|---|
| **Acc8** | Small end-to-end pathfinder for ISA refinement, compilation, emission, and release certificates. |
| **LNP64-µ** | Capability-machine model with the T1–T9 theorem ledger and a theorem-bound emitted artifact. |
| **LNP64mini** | Larger soft core and SoC integration vehicle using the certified Design-derived simulator. |
| **Substrate** | Small bring-up, transformation, and multiclock examples. |
| **Epoch** and **CapWalk** | Focused protocol machines for freshness and capability-walk properties. |

LNP64-µ is a demonstrator, not the definitive LNP64 architecture. Recorded
external ZC702 evidence includes a dual-core LNP64mini NetBSD workload over
native GEM0 and dedicated multiclock stress campaigns. Those runs strengthen
engineering confidence; they are not premises of the release theorem. Current
machine, gate, and hardware facts live in [STATUS.md](STATUS.md), with scoped
board details in [fpga/zc702/README.md](fpga/zc702/README.md).

## Repository map

- `Loom/` — generic semantics, authoring DSL, verified execution, compiler,
  emitter, proof support, and release machinery.
- `Machines/` — machine definitions, refinements, invariants, and examples.
- `Evidence/` — target profiles, optional bindings, and empirical evidence
  outside the generic theorem layer.
- `Tests/` — kernel checks and focused regressions.
- `Tools/` — audit, emission, release, inspection, and simulation executables.
- `scripts/` — CI, reproduction, artifact, and optional external-tool flows.
- `fpga/zc702/` — untrusted board wrappers and the local hardware record.

The main documents have separate roles:

- [CHARTER.md](CHARTER.md) — mission and scope.
- [STATUS.md](STATUS.md) — current checked facts, limitations, and gate results.
- [REPRODUCING.md](REPRODUCING.md) — commands and review tiers.
- [TCB.md](TCB.md) — authoritative release theorem and trusted set.
- [TRUST.md](TRUST.md) — property and platform limitations.
- [ROADMAP.md](ROADMAP.md) — ordered unfinished work.
- [PLATONIC.md](PLATONIC.md) — strategic destination and scope test.
- [PRETTY.md](PRETTY.md) — user-facing hardware syntax contract.
- [MULTICLOCK.md](MULTICLOCK.md) — multiclock application model and guarantees.
- [MULTICLOCK_PLAN.md](MULTICLOCK_PLAN.md) — remaining multiclock engineering.
- [MULTICLOCK_BOUNDARY.md](MULTICLOCK_BOUNDARY.md) — proved digital boundary
  and external physical obligations.

## Licensing

The repository is Apache-2.0 ([LICENSE](LICENSE)); `Machines/` is also offered
under Solderpad SHL-2.1 ([Machines/LICENSE](Machines/LICENSE)). Contributions
use a DCO ([CONTRIBUTING.md](CONTRIBUTING.md)). Emitted Verilog from a user's
design is not made a derivative work merely by generation; see [NOTICE](NOTICE).
