# The intended shape of Loom

Loom's organizing goal is simple:

> A design, its executable behavior, its proofs, its tests, its emitted
> artifact, and its hardware evidence should be derived views of the same Lean
> value, with every non-derived link named as an assumption.

This is the strategic destination. The ordered implementation queue is
[`NEXTSTEPS.md`](NEXTSTEPS.md); current facts are in
[`STATUS.md`](STATUS.md).

## What the finished toolchain should feel like

A user should be able to declare state and behavior once, prove properties at
the natural abstraction level, select verified transformations, emit a small
structural artifact, and obtain a report that distinguishes theorem,
certificate, external comparison, and physical measurement without ambiguity.

The ideal workflow has six properties:

1. **One declaration per fact.** Register names, widths, reset values,
   interfaces, simulator fields, and comparison coverage are generated from
   one declaration.
2. **Local proof cost.** An invariant proof reasons only about rules that can
   touch its support; unrelated logic disappears through generic frame lemmas.
3. **Provable optimization.** Balancing, retiming, duplication, and pipelining
   are transformations with refinement theorems, not handwritten semantic
   rewrites justified by comments.
4. **Fast views remain proved views.** Specialized simulators and generators
   are derived from the design and accompanied by kernel-checked equality or
   soundness theorems.
5. **External evidence is translation validation.** Synthesis and target
   checks produce precise, certificate-backed reports with exclusions. They
   never masquerade as additions to the kernel theorem.
6. **Physical predictions are models with uncertainty.** Timing, area, memory
   mapping, and CDC assumptions are target-parameterized and empirically
   calibrated, with residual error stated.

## Non-negotiable constraints

- The publication theorem retains its three-axiom closure.
- No convenience feature silently adds the Lean compiler, solver, printer,
  parser, or synthesis flow to the theorem TCB.
- `Loom` remains machine- and target-generic. Target facts enter through data
  profiles and wrappers.
- A green result cannot be obtained by omission: new state, signals, memories,
  operators, and assumptions must be checked or explicitly excluded.
- Counterexamples improve statements and designs; they are not papered over by
  weakening prose.
- Public documentation describes the current system. Git, the changelog, and
  compact evidence records preserve history.

## Capability workstreams

### A typed, single-source design language

Typed register/memory handles and declaration notation should eliminate
stringly duplicated widths and names while elaborating to the current EDSL.
Generated state adapters and comparators should make simulation coverage
complete by construction.

### Property-directed proof automation

Footprints, support inference, frame rules, and cycle tactics should make proof
cost scale with a property's dependency cone. A future one-rule-at-a-time
reasoning layer is worthwhile only if it is verified to flatten to the current
ordered last-write-wins semantics.

### A verified transformation library

The existing tree builders and retiming seed should grow into composable
refinement-preserving optimization passes. The legible design remains the
source; the fast implementation is a proved transform chain.

### Derived simulation

A specialized evaluator generated from `Design` should replace hand-maintained
cycle mirrors. The generated equality theorem and complete state comparator
are part of the feature, not follow-up documentation.

### Translation validation and target models

The netlist checker should cover every shipped artifact it claims, grow by
explicit operator/cell instances, and keep LRAT checking independent of the
solver. Static timing/area estimators should be useful engineering predictors
without being oversold as physics theorems.

## Success criteria

Loom reaches this shape when a substantial processor can be changed at one
declaration site; all derived views either update automatically or fail with a
named obligation; properties recheck in proportion to affected logic; the
optimized emitted implementation is connected by composed proofs; and the
release report makes every remaining trusted or empirical link obvious to an
outside reviewer.
