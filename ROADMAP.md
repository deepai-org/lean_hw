# Loom roadmap

This is Loom's ordered queue of unfinished work. The intended architecture and
scope are in [`PLATONIC.md`](PLATONIC.md); current verified capabilities,
limitations, and gate results are in [`STATUS.md`](STATUS.md).

Completed work belongs in Git and the changelog, not in this file.

## 1. Finish gate and release polish

- Make every optional workflow report `PASS`, `FAIL`, or `SKIP`, including the
  reason and relevant tool version.
- Recheck the complete CI, reproduction, and verified-release workflows and
  record their exact outcomes in `STATUS.md`.
- Reduce high-volume compiler warnings where doing so does not destabilize
  proof scripts.

Acceptance: release logs distinguish every executed and skipped leg without
manual interpretation, and the current status table cites fresh runs.

## 2. Improve proof scaling

- Extend footprint, support, frame, and projected-cycle automation so proofs
  simplify only the rules relevant to their property.
- Improve composition of register, memory, and open-system properties.
- Add reusable refinement-by-cases support for staged engines and protocols.
- Keep environment assumptions explicit and checkable for non-vacuity.

Acceptance: representative LNP64mini invariants recheck through small declared
dependency cones without unfolding the complete machine cycle.

## 3. Complete typed single-source views

- Derive state adapters, comparison membership, debug descriptions, output
  layouts, and coverage reports from typed declarations.
- Remove remaining hand-maintained name/width tables.
- Require every exclusion from a generated comparison or report to be named.
- Migrate or deliberately retire LNP64mini's remaining gate-stress,
  fault/sentinel conformance, capability-transfer, trace, opcode-matrix, and
  relocation commands before deleting their `MiniIss` support. Keep an
  independent oracle only when its diagnostic value justifies a second
  semantic implementation, and label it as sampled corroboration rather than
  proof.

Acceptance: adding or changing one state element updates every derived view or
fails with a specific obligation; no production command depends on an
unlabelled hand-maintained semantic mirror.

## 4. Grow verified logical transformations

- Generalize retiming and fanout duplication only through transformations with
  refinement theorems.
- Add useful composition laws and legality checks.
- Keep preservation by downstream implementation tools as external evidence,
  never as a premise hidden in the logical theorem.

Acceptance: a nontrivial machine can compose several transformations while
transporting its model property through one checked refinement chain.

## 5. Add technology-neutral logical equivalence

- Define a minimal `LogicalNetlist` Boolean transition graph with explicit
  inputs, outputs, state, drivers, and opaque memory cut points.
- Define structural validation and total reference semantics.
- Prove memoized evaluation, routing, CNF construction, and miter soundness.
- Check UNSAT certificates with Loom's generic LRAT infrastructure and return
  useful counterexamples for SAT results.
- Define a small neutral serialization with a fail-closed parser.
- Demonstrate producer independence without importing synthesis-tool formats,
  vendor primitives, or ASIC cell libraries into Loom.

Acceptance: the same theorem checks neutral logical artifacts from different
external producers and remains unchanged across FPGA vendors and ASIC use.

## 6. Derive fast executable views

- Extend the certified DAG evaluator and generated state comparison path.
- Reduce dependence on manually synchronized ISS/emulator implementations;
  retain them as explicitly independent differential oracles where useful.
- Keep every optimized evaluator connected to reference semantics by a
  kernel-checked equality or soundness theorem.
- After the generic diagnostic/runner/coverage extraction has settled,
  package fail-closed DAG execution and multi-design orchestration without
  adding parallel public runner names.

Acceptance: large-machine simulation is practical without adding an unproved
semantic implementation to the trusted path.

## 7. Strengthen compositional system contracts

- Add first-class rely/guarantee contracts over environment steps and traces,
  including satisfiability witnesses and composition rules.
- Compose multiple single-clock domains through proved CDC components and
  declared clock relationships rather than changing Loom's core synchronous
  semantics.
- Add proved monitor synthesis for safety and bounded-response properties.
- Define authenticated-view boundaries for bulk untrusted external state.
- Design a generic open-Design environment/core stepping interface only after
  comparing at least two existing machines, including one non-CPU. It must not
  freeze LNP64mini's command, FSM-width, or DDR-latency assumptions into Loom.

Acceptance: open and multi-domain designs state their assumptions at typed
ports and transport guarantees compositionally.

## 8. Maintain release clarity

- Keep theorem, checked-certificate, conversion, implementation, and physical
  claims distinct in generated evidence.
- Record exact dependency revisions, tool versions, optional-check outcomes,
  resource envelopes, and artifact identities for releases.
- Keep public documentation limited to current state; preserve campaign detail
  in scoped evidence records.

Acceptance: a reviewer can reproduce each claimed layer and can see every
external assumption or skipped check without interpreting shell logs.
