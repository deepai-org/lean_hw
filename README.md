# Loom — a proof-carrying processor toolchain in Lean 4

Loom is a hardware EDSL and processor-verification toolchain written in Lean
4. A design is a Lean value; the repository supplies synchronous semantics, a
verified compiler to a small µVerilog IR, structural Verilog emission,
certificate-checked SAT workflows, and machine proofs built on the same
definitions.

The repository contains several deliberately different machines:

| Machine | Role and demonstrated result |
|---|---|
| **Acc8** | Small end-to-end pathfinder: ISA, refinement, compilation, emission, and release certificate. |
| **LNP64-µ** | Four-domain capability-machine model with the T1–T9 theorem ledger and a release theorem for an emitted artifact. |
| **LNP64mini** | Larger soft core and SoC integration vehicle. The current head has a board/network regression and is not hardware-green. |
| **Substrate** | Board bring-up designs, including bit-exact model/RTL/silicon checks on a ZC702. |
| **Epoch** and **CapWalk** | Focused protocol machines for freshness and capability-walk properties. |

LNP64-µ is a demonstrator, not the definitive LNP64 architecture. Detailed
hardware evidence and current limitations are recorded in
[`fpga/zc702/README.md`](fpga/zc702/README.md) and
[`STATUS.md`](STATUS.md).

## Quick start

Install [Elan](https://lean-lang.org/lean4/doc/quickstart.html), then run:

```console
git clone https://github.com/deepai-org/lean_hw.git
cd lean_hw
lake build
lake test
lake exe audit
```

`lean-toolchain` pins Lean 4.28.0 and `lake-manifest.json` pins dependency
revisions. `lake build` needs no Verilog tools. The current results for these
commands, including which broader workflows were not rerun, are recorded in
the gate table in [`STATUS.md`](STATUS.md).

For the broader repository workflow, including emission and optional external
corroboration, use:

```console
scripts/reproduce.sh
```

Yosys, CaDiCaL, and Icarus Verilog checks self-skip when their tools are not
installed. `scripts/ci.sh` is therefore a portable Lean gate plus stronger
checks on suitably provisioned hosts, not proof that every optional external
check ran.

## Verified release

The publication-facing declaration is
`Loom.Release.Theorems.verifiedReleases` in
`Tools/VerifiedRelease.lean`. It packages Acc8 and LNP64-µ artifacts and, for
each one, checks:

- equality between a structural renderer's bytes and theorem-bound byte
  literals;
- complete declarative denotation of the concrete SSA witness as the
  reference compiler output;
- simulation from the processor model to the compiled transition system; and
- transport of model invariants to reachable compiled states.

For LNP64-µ the bundle names authority confinement, machine-wide W^X, lineage
ledger conservation, and budget boundedness. The final theorem's checked axiom
closure is exactly `propext`, `Classical.choice`, and `Quot.sound`.

Rebuild it separately with:

```console
scripts/build_verified_release.sh
```

This command builds the precise theorem dependency closure, emits and binds
both RTL files, checks generated certificates, runs RTL hygiene checks, and
audits the final theorem's axiom closure. It intentionally does **not** replace
the repository-wide `lake build`, `lake test`, or `lake exe audit` gates. At
the current head it stops at the known package-quality failure recorded in
[`STATUS.md`](STATUS.md).
Independent-review tiers, restart rules, and resource requirements are in
[`REPRODUCING.md`](REPRODUCING.md); measured planning costs are in
[`RELEASE_COST.md`](RELEASE_COST.md).

## Semantics and compiler

A `Loom.Hw.Design` contains named registers, memories, ports, and an ordered
list of guarded actions over width-indexed expressions. Reads observe the
pre-cycle state; writes commit at the cycle edge; later writes win. See
[`Loom/Hw/DESIGN.md`](Loom/Hw/DESIGN.md).

`Loom.Hw.Compile.compile` lowers a design to the µVerilog module IR. The
generic compiler-correctness results cover register updates, memory write
ports, outputs, and open-design cycles. The printer emits explicitly sized SSA
wires and one positive-edge sequential block.

The exact release path does not trust the optimized compiler, printer, or
witness generator. Those programs propose data; generated Lean declarations
check the witness against reference definitions and prove its renderer equals
the bound byte tree. Associating that tree with a host file is one explicit
exact-comparison step. Interpreting the resulting Verilog remains the narrow
semantic assumption stated in
[`CONCRETE_SSA_BOUNDARY.md`](CONCRETE_SSA_BOUNDARY.md).

Loom currently makes no post-synthesis equivalence claim. The intended future
boundary is a small technology-neutral logical netlist, independent of FPGA
vendor, ASIC library, and synthesis producer. Tool-specific conversion and
mapped or physical artifacts remain external evidence. The generic proved
LRAT checker remains available to certificate-backed decision procedures.

## Design-derived tooling

Beyond the compiler, the same `Design` value now derives the surrounding
toolchain, so a fact stated once in a declaration cannot drift in a
hand-maintained mirror:

- **Typed declarations.** `Reg w`, `RegArray w n`, and `Mem aw dw` handles
  declare a name and width once and elaborate to the unchanged core EDSL;
  the `Declarations` builder derives register, memory, port, sync-read, and
  initialization metadata from the same source. `Design.emit` enforces
  read-validity, name uniqueness, declared sync-reads, and write-port shape
  at emission time — an obligation a caller cannot skip.

- **Certified simulation.** `DagEval` hash-conses a design's expression trees
  and independently certifies node dependencies, expression/action
  correspondence, and state layout before exposing cycle execution
  (`VerifiedSimulator`, with run and reset-to-run theorems). It executes
  within about 2× of a hand-written simulator while remaining a checked view
  of the design rather than a second description of it.

- **Differential running.** `Loom.Runner` owns step control, bounded and
  immediately flushed mismatch events, and structured PASS/FAIL/SKIP results
  for comparing a design against an independent oracle. Comparison coverage
  is derived **fail-closed** from `Design.coords`: every declared coordinate
  is compared or explicitly excluded, so the coordinate nobody thought to
  list is a failure, not a blind spot. On its first audit this surfaced
  eleven constant, never-written bus qualifiers that hand-enumerated
  comparisons had silently skipped.

- **Property automation.** Footprint and support inference reduce an
  invariant's proof obligation to the rules that can touch it;
  `PropertyFootprint`/`ExprProperty` build reduced cycles with proved
  observational agreement, and `TransitionProperty` states typed
  single-transition properties (unchanged-coordinate preservation and
  similar) checked against the real design's declaration surface.

- **Verified transformations.** Retiming plans over ordered write-only cuts
  and fan-out duplication of a register come with stuttering-simulation
  refinements and invariant transport; `StutterSimulation` composes, so a
  chain of passes yields one refinement from the legible source design.

- **Evidence discipline.** `Loom.Artifact` gives emitted and observed
  artifacts exact-byte identity with deterministic, change-only writes;
  script-level SHA-256 manifests and freshness checks name the producing
  command when an artifact is stale or a producer fails silently. Debug
  instrumentation is generated, not hand-wired: a `DebugMap` tap list
  produces both the wrapper-side decode and the host-side reader from one
  declaration, including typed first-event sticky captures with optional
  halt-on-trigger — explicitly outside the theorem boundary, and labelled
  as such in its own report.

These facilities are machine-independent (`Loom/Runner.lean`,
`Loom/Artifact.lean`, `Loom/Hw/DagEval.lean`, `Loom/Hw/DebugTap.lean`, and
the `Loom/Hw` proof modules); the machines in `Machines/` consume them, and
the largest ones exercise every item above in their standing gates.

## Hardware boundary

Target-specific blocks enter through three explicit interfaces:

1. Semantically pure synchronous idioms may be inferred as RAMs, arithmetic
   blocks, or other target resources.
2. Clock, reset, CDC, scan, SERDES, and board primitives remain in untrusted
   wrappers.
3. External processors, buses, DMA engines, and peripherals are environments
   across declared ports and require their own assume/guarantee contracts.

The core theorems do not cover reset electronics, synthesis/P&R correctness,
DMA, interrupts, debug, analog behavior, timing channels, or physical side
channels. The authoritative trust inventory is [`TCB.md`](TCB.md); the longer
claim audit is [`TRUST.md`](TRUST.md).

## Repository map

- `Loom/` — generic semantics, hardware EDSL, compiler, emitter, decision
  procedures, and release machinery.
- `Machines/` — machine definitions, refinements, invariants, and examples.
- `Evidence/` — explicit target profiles and empirical calibrations outside
  Loom's generic theorem layer.
- `Tests/` — Lean test driver and focused regression modules.
- `Tools/` — executables for audit, emission, release, books, and simulation.
- `scripts/` — CI, reproduction, certificate generation, and external-tool
  workflows.
- `fpga/zc702/` — untrusted board wrappers and the hardware evidence log.

Document roles are intentionally non-overlapping:

- [`CHARTER.md`](CHARTER.md): mission, scope, and governance.
- [`STATUS.md`](STATUS.md): current checked state and known red gates.
- [`REPRODUCING.md`](REPRODUCING.md): commands and review tiers.
- [`TCB.md`](TCB.md): authoritative release claim and trusted list.
- [`CONCRETE_SSA_BOUNDARY.md`](CONCRETE_SSA_BOUNDARY.md): exact text-semantics
  assumption.
- [`TRUST.md`](TRUST.md): property and platform limitations.
- [`ROADMAP.md`](ROADMAP.md): ordered unfinished work.
- [`PLATONIC.md`](PLATONIC.md): strategic destination.

## Licensing

The repository is Apache-2.0 ([`LICENSE`](LICENSE)); `Machines/` is also
offered under Solderpad SHL-2.1 ([`Machines/LICENSE`](Machines/LICENSE)).
Contributions use a DCO ([`CONTRIBUTING.md`](CONTRIBUTING.md)). Emitted
Verilog produced from a user's own design is not made a derivative work of
the toolchain merely by generation; see [`NOTICE`](NOTICE).
