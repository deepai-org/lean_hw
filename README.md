# Loom — hardware design and proof in Lean 4

Loom is a hardware EDSL and verification system. A synchronous design is a
Lean value used to derive its semantics, executable simulator, proofs, tests,
and structural Verilog. Loom includes a proved compiler to a small
µVerilog IR, certificate-checked SAT infrastructure, and several example
processors and protocol machines.

Loom is not a synthesis tool or an FPGA-vendor framework. Its generic layer is
independent of FPGA versus ASIC implementation and does not depend on Yosys or
another synthesis producer. Synthesis, technology mapping, place and route,
bitstreams, and physical behavior remain external evidence.

## Quick start

Install [Elan](https://lean-lang.org/lean4/doc/quickstart.html), then run:

```console
git clone https://github.com/deepai-org/lean_hw.git
cd lean_hw
lake build
lake test
lake exe audit
```

`lean-toolchain` pins Lean 4.28.0 and `lake-manifest.json` pins all Lean
dependencies. These commands require no Verilog or synthesis tools. For the
last recorded outcome of each gate, see [`STATUS.md`](STATUS.md).

The broader reproduction wrapper adds emission, artifact checks, and optional
external corroboration:

```console
scripts/reproduce.sh
```

Optional Yosys, CaDiCaL, and Icarus Verilog legs report or self-skip according
to the tools installed on the host. A successful wrapper is not by itself a
claim that every optional leg ran; retain its PASS/FAIL/SKIP output.

## The Design workflow

A `Loom.Hw.Design` contains typed register, memory, and input declarations plus
an ordered list of guarded actions. Reads observe pre-cycle state, writes
commit at the cycle edge, and later writes win. The detailed semantics are in
[`Loom/Hw/DESIGN.md`](Loom/Hw/DESIGN.md).

Expressions include fixed-width modular multiplication, emitted directly as
technology-neutral Verilog `*`; typed unsigned and signed full-width products
(`Expr.umulWide` and `Expr.smulWide`); and a typed concatenation constructor
(`++#`). Full-width products lower through the same proved primitive path.
Unsigned `/` and `%` are total: division by zero returns zero and remainder by
zero returns the dividend. The compiler emits that guard explicitly instead
of inheriting Verilog's unknown-valued zero-divisor behavior.

The current workflow derives these views from the Design:

- **Declarations and interfaces.** `Reg w`, `RegArray w n`, and `Mem aw dw`
  handles keep signal names and widths at their declaration sites. The
  `Declarations` builder lowers them into the core EDSL and records inputs,
  outputs, memory policy, and initialization policy.
- **Execution.** `FastEval` lowers the Design to flat indexed state.
  `DagEval` shares expression subtrees across the whole cycle and checks a
  structural certificate before execution. Its cycle and run theorems connect
  the optimized evaluator to the declarative Design for arbitrary states,
  inputs, and cycle counts; direct theorems also connect the same executions
  to the proved µVerilog compiler. Loom proves that preparation of its own
  lowered DAG succeeds for every well-formed fast simulator.
- **Typed state views.** Register and memory handles resolve once into flat
  simulator slots. Resolution fails on a missing declaration or stale width;
  slot-read theorems connect those values to the same semantic agreement
  relation as the simulator.
- **Comparison and tests.** `Design.coords` derives the comparison surface.
  `Loom.Runner` reports structured results, and undeclared coverage gaps fail
  by name. Independent ISS models can still be useful differential oracles,
  but they are not the primary simulator or part of the universal simulator
  refinement theorem.
- **Proof support.** Footprints, support inference, projected actions, and
  general expression and transition properties reduce invariants to the
  design rules that can affect them.
- **Emission and evidence.** The compiler lowers the Design to µVerilog;
  structural emission validates its generic obligations. `Loom.Artifact`
  records exact byte identity, while target profiles, external tools, and
  board observations stay in the separate evidence layer.

LNP64mini's cycle mirror has been removed; its execution, architectural
observations, and RTL expectations derive from the Design. Some integration
adapters across the wider tree remain machine-specific. The ordered remaining
work is in [`ROADMAP.md`](ROADMAP.md), and
the destination and scope test are in [`PLATONIC.md`](PLATONIC.md). Typed
`Chan w` handles now generate source/sink endpoints and synchronous FIFO
adapters; named `System` assembly provides fail-closed clock/realization
checks, executable schedule replay, a derived crossing inventory, and
schedule-quantified lifting of ordinary Design invariants. Physical CDC
components, refinement, constraints, hierarchy, and the LNP64mini production
adoption remain ordered in [`MULTICLOCK_PLAN.md`](MULTICLOCK_PLAN.md).

To exercise both LNP64mini execution paths:

```console
lake exe minitest progtest   # architectural checks on the Design-derived simulator
lake exe minitest selftest   # architectural checks on the Design-derived simulator
```

[`TUTORIAL.md`](TUTORIAL.md) is the guided introduction to writing and proving
a smaller Design.

## Included machines

| Machine | Current role |
|---|---|
| **Acc8** | Small end-to-end pathfinder for ISA refinement, compilation, emission, and release certificates. |
| **LNP64-µ** | Capability-machine model with the T1–T9 theorem ledger and a theorem-bound emitted artifact. |
| **LNP64mini** | Larger soft core and SoC integration vehicle; its primary simulator is the certified Design-derived DAG evaluator. The current dual-core NetBSD board workload is hardware-green as external evidence. |
| **Substrate** | Small bring-up and transformation examples, including recorded ZC702 observations. |
| **Epoch** and **CapWalk** | Focused protocol machines for freshness and capability-walk properties. |

LNP64-µ is a demonstrator rather than the definitive LNP64 architecture.
Current machine and hardware limitations are recorded in
[`STATUS.md`](STATUS.md) and [`fpga/zc702/README.md`](fpga/zc702/README.md).

## What is proved

The generic compiler-correctness results cover register updates, memory write
ports, outputs, and open-design cycles from `Design` to the µVerilog module
semantics. The exact release path checks concrete SSA witnesses against
reference definitions and binds their rendered byte trees to emitted files.

The publication-facing declaration is
`Loom.Release.Theorems.verifiedReleases` in
`Tools/VerifiedRelease.lean`. It packages the Acc8 and LNP64-µ release
results. Its checked axiom closure is `propext`, `Classical.choice`, and
`Quot.sound`.

To rebuild that release boundary separately:

```console
scripts/build_verified_release.sh
```

This command is distinct from the repository-wide build, test, and audit
gates. Its current rerun status is recorded in [`STATUS.md`](STATUS.md);
[`REPRODUCING.md`](REPRODUCING.md) gives review tiers and exact commands.

The theorem is not a claim about arbitrary Verilog, synthesis correctness,
timing, FPGA bitstreams, ASIC layout, or silicon. Loom currently has no
post-synthesis equivalence checker. The authoritative trusted-computing-base
inventory is [`TCB.md`](TCB.md), the precise Verilog-text assumption is
[`CONCRETE_SSA_BOUNDARY.md`](CONCRETE_SSA_BOUNDARY.md), and broader limitations
are in [`TRUST.md`](TRUST.md).

## Repository map

- `Loom/` — generic semantics, EDSL, verified execution, compiler, emitter,
  proof support, decision procedures, and release machinery.
- `Machines/` — machine definitions, refinements, invariants, and examples.
- `Evidence/` — target profiles and empirical calibration outside the generic
  theorem layer.
- `Tests/` — kernel checks and focused regressions.
- `Tools/` — audit, emission, release, and simulation executables.
- `scripts/` — CI, reproduction, artifact, and external-tool workflows.
- `fpga/zc702/` — untrusted board wrappers and the hardware evidence log.

The main documents have separate roles:

- [`CHARTER.md`](CHARTER.md) — mission, scope, and governance.
- [`STATUS.md`](STATUS.md) — current checked facts and known red gates.
- [`REPRODUCING.md`](REPRODUCING.md) — commands and review tiers.
- [`TCB.md`](TCB.md) — authoritative release claim and trusted list.
- [`TRUST.md`](TRUST.md) — property and platform limitations.
- [`ROADMAP.md`](ROADMAP.md) — ordered unfinished work.
- [`PLATONIC.md`](PLATONIC.md) — strategic destination and scope boundary.
- [`MULTICLOCK_PLAN.md`](MULTICLOCK_PLAN.md) — clock-domain and CDC
  architecture, with shipped foundation and remaining phases identified.

## Licensing

The repository is Apache-2.0 ([`LICENSE`](LICENSE)); `Machines/` is also
offered under Solderpad SHL-2.1 ([`Machines/LICENSE`](Machines/LICENSE)).
Contributions use a DCO ([`CONTRIBUTING.md`](CONTRIBUTING.md)). Emitted Verilog
from a user's design is not made a derivative work merely by generation; see
[`NOTICE`](NOTICE).
