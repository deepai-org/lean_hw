# Release theorem and trusted computing base

This is the authoritative inventory for the publication release. Operational
instructions are in [`REPRODUCING.md`](REPRODUCING.md); limitations of the
properties and platform are in [`TRUST.md`](TRUST.md).

## The theorem

```lean
theorem Loom.Release.Theorems.verifiedReleases :
  Nonempty Loom.Release.Theorems.VerifiedReleases
```

`Tools/VerifiedRelease.lean` fixes one Acc8 artifact and one LNP64-µ artifact.
For each, the kernel checks:

- exact equality between `SSA.Program.renderTree`'s byte rope and a
  theorem-bound disk byte rope;
- `Symbolic.ModuleBehavior`, covering metadata, indexed SSA wires, register
  next-state expressions, memory images and writes, and outputs against the
  reference `Compile.compile` result;
- a simulation from the processor model to the reachable part of that
  compiled transition system; and
- transport of every model invariant through the simulation.

The combined LNP64-µ bundle instantiates that transport for authority
confinement, machine-wide W^X, lineage-ledger conservation, and budget
boundedness. `Tools/ReleaseAudit.lean` checks that this declaration depends on
exactly:

```text
propext
Classical.choice
Quot.sound
```

The theorem does not invoke either project µVerilog boundary axiom
(`ImplementsStandard` or `implements_standard_spec`). It stops at formal
denotation and exact theorem-bound bytes.

## Trusted for each extension of the claim

The trusted set grows only when the claim is extended:

1. **Lean statement:** the Lean kernel and the three standard axioms above.
2. **The two host files:** additionally, the narrow file-association step in
   `scripts/check_release_binding.py`. It reconstructs theorem literals in
   declared order and invokes exact `cmp -s`; hashes are not used for
   soundness.
3. **Verilog as interpreted by a tool:** additionally, the concrete-SSA
   semantic adequacy assumption in
   [`CONCRETE_SSA_BOUNDARY.md`](CONCRETE_SSA_BOUNDARY.md). The current
   corroborating tool/version is Yosys 0.33 (`2584903a060`), but the Lean
   theorem does not depend on Yosys.
4. **A synthesized or physical implementation:** additionally, all synthesis,
   tool-specific conversion, technology mapping, and downstream physical-flow
   assumptions. Loom currently supplies no post-synthesis equivalence claim.
   Profiles and calibrations under `Evidence/` are engineering inputs to this
   layer, not premises of generic Loom theorems.
   Placement, routing, configuration generation, timing, and physics remain
   downstream.
5. **Board CDC behavior:** additionally, a physical resolution assumption for
   the board wrappers that use the toggle/2FF/XOR crossings. A metastable first
   flop is modeled as resolving adversarially to either Boolean value before
   the next sampling edge. `Loom/Hw/CdcContract.lean` proves the digital
   protocol for every such oracle; it does not prove MTBF, aperture, routing,
   or analog behavior. The closed single-clock release cores do not require
   this item.

These are conditional layers, not one claim that every downstream artifact is
formally verified.

## Not trusted for theorem acceptance

The optimized `implemented_by` compiler/printer paths, witness and certificate
generators, generated-source orchestrator, compiled evaluator, audit reporter,
SAT solver, simulators, SHA-256, and cached `.olean` files propose data,
schedule work, or provide corroboration. A defect may cause rejection,
nontermination, or missed diagnostics, but cannot make the Lean kernel accept
a declaration with an invalid proof term.

One qualification matters: such tools can still affect claims outside the
kernel. The file binder is explicitly trusted for associating host bytes, and
external drivers/parsers are trusted to the extent that a user relies on
their synthesis or hardware reports.

`lake exe audit` separately enforces the repository policy for project axioms,
`sorry`, `native_decide`, imports, unsafe declarations, `implemented_by`,
`partial`, and `extern`. It is a reporting and CI gate, not an axiom and not a
replacement for kernel checking.

## Claim boundary

The release theorem concerns two-state, synchronous, closed processor models
and exact Verilog core bytes. It does not establish electrical reset,
four-state behavior outside the admitted subset, external DMA or interrupts,
debug and SoC-fabric policy, timing closure, liveness under arbitrary platform
stalls, power behavior, or physical side-channel resistance.
