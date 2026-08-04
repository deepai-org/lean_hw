# Loom implementation map

This document describes the repository as it is organized now. The mission
and governance rules are in [`CHARTER.md`](CHARTER.md), current health is in
[`STATUS.md`](STATUS.md), and the ordered work queue is in
[`NEXTSTEPS.md`](NEXTSTEPS.md).

## Architectural principles

1. **One transition-system spine.** `Loom.Core.TSys` is the common language
   for machine models, hardware semantics, refinement, invariants, bounded
   properties, and emitted-module semantics.
2. **Toolchain and machines are separate.** `Loom/` is generic and never
   imports `Machines` or `Tools`; the audit enforces this direction.
3. **Structure before syntax.** ISA and hardware DSL notation elaborates to
   ordinary Lean data. Proofs and tools consume those data structures, not a
   parallel syntax tree.
4. **Solvers propose; the kernel checks.** SAT/UNSAT workflows use checked
   certificates. `native_decide` and trusted compiler evaluation are excluded
   from theorem paths.
5. **Artifact claims stop at named boundaries.** Formal module behavior,
   exact bytes, synthesis corroboration, and physical hardware are separate
   layers with separate assumptions.
6. **Machine campaigns drive generic features.** New infrastructure should
   close a demonstrated machine, proof, release, portability, or integration
   need.

## Repository layers

| Layer | Location | Current responsibility |
|---|---|---|
| Transition systems | `Loom/Core/` | `TSys`, simulations, stuttering simulations, traces, bounded-response machinery |
| ISA framework | `Loom/Isa/` | Encoding signatures, instruction declarations, encode/decode, DSL notation |
| Decision procedures | `Loom/Dp/` | CNF, BMC, k-induction, solver interfaces, proved LRAT checking |
| Hardware EDSL | `Loom/Hw/` | Expressions, actions, synchronous semantics, composition, compilation, outputs, memory/CDC/target contracts |
| µVerilog | `Loom/Emit/MicroVerilog/` | Typed AST, semantics, printer, parser, and round-trip results |
| Release path | `Loom/Release/` | Concrete SSA, structural rendering, denotation certificates, exact release packaging |
| Netlist checks | `Loom/Netlist/` | Yosys JSON model, cones, miters, proved encoder fragment, memory checks |
| Documentation | `Loom/Book/` | Extraction and HTML rendering from Lean data |
| Machines | `Machines/` | Processor/protocol definitions, refinements, invariants, examples, and integration designs |
| Executables | `Tools/` | Audit, emission, release, simulation, book, target, and equivalence-check drivers |
| Independent LRAT check | `checker/` | Separate unproved LRAT implementation for cross-validation; not a Lean kernel checker |

## Dependency direction

```text
Loom.Core
  ├── Loom.Isa
  ├── Loom.Dp
  ├── Loom.Hw ── Loom.Emit
  └── Loom.Logic

Loom.* ──> Machines.* ──> machine theorem ledgers
Loom.*, Machines.* ──> Tools
```

Arrows show allowed use from left to right. `Loom.Hw` does not depend on a
particular ISA; machine refinement modules see both layers. `Tools` is a leaf:
nothing in the proof libraries imports it.

## Main verification chain

For LNP64-µ, the current end-to-end chain is:

1. `Machines.Lnp64u.machine` defines the processor model on `TSys`.
2. T1–T9 state and prove the model properties under their explicit premises.
3. R-MC simulates that model with the reachable compiled EDSL core.
4. `Compile.compile` is related generically to `Design` cycle semantics.
5. A concrete SSA witness is checked to denote that reference compilation.
6. Its structural renderer is proved equal to theorem-bound byte ropes.
7. A small external binder associates those ropes with the two RTL files.
8. Verilog-tool interpretation and physical implementation remain explicit
   downstream assumptions and corroboration layers.

The publication bundle selects four LNP64-µ invariant consequences rather
than embedding every T1–T9 theorem. See [`TCB.md`](TCB.md).

## Machine roles

- **Acc8:** smallest release/refinement path and fast regression target.
- **LNP64-µ:** theorem and release-certificate driver.
- **LNP64mini:** open-design composition, simulation, FPGA, and architecture
  extension vehicle; not covered by the LNP64-µ theorem bundle.
- **Substrate:** small board bring-up and long-run state comparison.
- **Epoch and CapWalk:** protocol-machine, memory-target, and integration
  campaigns.
- **Tutorial and PingPong:** public examples and documentation tests.

## Verification commands

| Scope | Command |
|---|---|
| Generic and machine libraries | `lake build` |
| Test driver | `lake test` |
| Trust/axiom/import inventory | `lake exe audit` |
| Repository CI workflow | `scripts/ci.sh` |
| Full reproduction wrapper | `scripts/reproduce.sh` |
| Publication release theorem | `scripts/build_verified_release.sh` |
| Reviewer-scale release sample | `scripts/review_verified_release.sh 4` |
| Manual timing/resource gates | `scripts/nightly_gates.sh` |

These commands are not interchangeable. Current results are recorded only in
[`STATUS.md`](STATUS.md).

## Definition of clean

A publicly releasable revision must satisfy all of the following:

- package-quality, build, test, and audit gates pass from a clean checkout;
- the release theorem is rebuilt without supplied generated objects;
- its axiom closure is exactly the three documented standard axioms;
- emitted files are freshly generated, hygienic, and exactly bound;
- every optional external check used as evidence reports whether it ran,
  skipped, excluded a signal, or acknowledged a defect;
- public documentation describes the current revision, while dated evidence
  is labeled as evidence for a specific artifact; and
- the release tag records toolchain, manifest, resource envelope, and known
  platform limitations.
