# Release theorem and trusted computing base

This is the authoritative release claim. Commands are in
[`REPRODUCING.md`](REPRODUCING.md); current gate results are in
[`STATUS.md`](STATUS.md).

## The theorem

```lean
theorem Loom.Release.Theorems.verifiedReleases :
  Nonempty Loom.Release.Theorems.VerifiedReleases
```

`Tools/VerifiedRelease.lean` fixes Acc8, LNP64-µ, and one portable two-clock
System artifact.

For each processor, the kernel checks:

- the compiler's module behavior—SSA wires, registers, memories, and outputs—
  against `Compile.compile`;
- simulation from the processor model to reachable compiled states;
- transport of model invariants through that simulation; and
- equality between the rendered byte rope and the theorem-bound bytes.

For the System, the kernel checks certified islands and compiler-produced FIFO
components, the parametric channel refinement, exactly one compatible binding
per connection, schedule replay against public System semantics, and the
literal emitted `system.v` bytes. The top wrapper is structural wiring; a
quality gate rejects handwritten behavioral CDC logic on this path.

The combined theorem's exact axiom closure is:

```text
propext
Classical.choice
Quot.sound
```

It does not invoke Loom's µVerilog adequacy boundary assumptions. The theorem
ends at formal denotation and exact bytes.

## Trust added by each stronger claim

| Claim | Additional trusted premise |
| --- | --- |
| Lean declaration | Lean kernel and the three axioms above |
| Named host RTL files | narrow file-association logic in `scripts/check_release_binding.py`; exact comparison, not hashes |
| Verilog as interpreted by a tool | [`CONCRETE_SSA_BOUNDARY.md`](CONCRETE_SSA_BOUNDARY.md) |
| Synthesized/netlist/physical artifact | synthesis, conversion, technology mapping, external-IP, and downstream signoff assumptions |
| Physical CDC behavior | synchronizer/metastability resolution model, MTBF, placement, routing, clocks, reset, and timing assumptions |

These are conditional layers, not one claim that every downstream artifact is
verified. Yosys is used for corroboration and RTL-import normalization; the
release theorem does not depend on Yosys.

## Not trusted for kernel acceptance

Optimized `implemented_by` paths, certificate/witness generators, the compiled
evaluator, audit reporter, SAT solver, simulators, SHA-256, and cached `.olean`
files may propose data or cause rejection/nontermination. They cannot make the
kernel accept an invalid proof term.

They can still matter outside the theorem: the host-file binder is trusted for
associating disk bytes, and an external report is only as reliable as its tool,
driver, parser, configuration, and artifact identity. `lake exe audit` enforces
repository policy for project axioms, `sorry`, `native_decide`, imports,
`unsafe`, `implemented_by`, `partial`, and `extern`; it is a CI gate, not an
axiom.

## Boundary

The theorem concerns fixed two-state processor models and one schedule-driven
portable multiclock System. It does not establish post-synthesis equivalence,
four-state behavior outside the admitted subset, external IP or memories,
DMA/interrupt/debug policy, liveness under arbitrary stalls, timing closure,
electrical reset delivery, metastability/MTBF, power behavior, physical side
channels, or silicon correctness.
