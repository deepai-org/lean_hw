# Reproducing the verified release

This document is for a reviewer starting with a clean machine and no trust in
the release builder. It distinguishes rechecking the claim from merely
identifying files that somebody else checked.

## The claim being re-derived

The publication-facing Lean declaration is
`Loom.Release.Theorems.verifiedReleases` in
`Tools/VerifiedRelease.lean`:

```lean
theorem verifiedReleases : Nonempty VerifiedReleases
```

`VerifiedReleases` contains one `VerifiedSymbolicArtifact` for Acc8 and one
for LNP64-µ. Each artifact contains:

```lean
exactBytes : program.renderTree.flattenBytes = disk.flattenBytes
denotation : Symbolic.ModuleBehavior design program ...
refinement : Simulation spec (Compile.compile design).toTSys.reachablePart
invariants : ∀ {P}, spec.Invariant P →
  (Compile.compile design).toTSys.Invariant
    (fun state => P (refinement.abs state))
```

The combined structure additionally instantiates invariant transport for
LNP64-µ authority confinement, machine-wide W^X, ledger conservation, and
budget boundedness. In plain English:

> The exact externally bound Acc8 and LNP64-µ bytes are structural renderings
> of concrete SSA programs whose complete declarative denotations agree with
> the reference compiler outputs. Those outputs simulate the proved processor
> models, and the named model security invariants hold of every reachable
> compiled state under the simulation abstraction.

The theorem deliberately does not claim that the Lean kernel reads a host
filesystem. The one external byte-binding step connects its `disk` literals
to the two files after the kernel has checked the theorem.

## Tier A: full independent recheck

This is the gold-standard artifact evaluation. Install Elan, Git, Python 3,
and ordinary POSIX build tools, then use a fresh clone:

```console
git clone https://github.com/deepai-org/lean_hw.git
cd lean_hw
scripts/build_verified_release.sh
```

The repository pins `leanprover/lean4:v4.28.0` in `lean-toolchain` (Lean commit
`7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`) and pins every dependency revision
in `lake-manifest.json`. The command:

1. builds the checked-in Lean project;
2. freshly emits `rtl/acc8.v` and `rtl/lnp64u.v`;
3. generates untrusted concrete SSA witnesses and bounded proof modules;
4. rejects the release unless each parsed witness equals `Design.toProgram`
   — the in-Lean reconstruction of the compiler's own output — so the
   shipped program cannot drift from the verified compilation
   (`toProgram parity gate`, since 2026-07-28);
5. repeats source generation and rejects any content drift;
6. checks the exact byte binding for both files;
7. rejects four-state/X/Z syntax, missing register resets, and incomplete
   memory images in the freshly emitted files;
8. kernel-checks every generated declaration and the single combined theorem;
9. runs the repository trust audit; and
10. rejects the release unless the combined theorem's axiom closure is
    exactly `propext`, `Classical.choice`, and `Quot.sound`.

On success the material outputs are `rtl/acc8.v`, `rtl/lnp64u.v`, and
`.lake/build/lib/lean/Tools/VerifiedRelease.olean`; the checked declaration's
readable source remains `Tools/VerifiedRelease.lean`. The final console line
names the theorem and repeats the external Yosys boundary so a successful
build cannot be mistaken for an end-to-end physical-hardware theorem.

No Verilog simulator or synthesizer is needed to establish the Lean theorem.
Yosys is needed only to cross the explicitly assumed text-semantics boundary.

The optional positional argument controls parallel Lean processes. The safe
default is eight:

```console
scripts/build_verified_release.sh 8
```

The LNP64-µ register certificates dominate the cost. A publication machine
with 32 logical ARM64 cores and 123 GiB RAM was used for final acceptance;
the authoritative runs' wall time and observed resource envelope are recorded
with the release tag and summarized in [`RELEASE_COST.md`](RELEASE_COST.md).
Any per-leaf distribution from an interrupted earlier run is labeled
preliminary rather than blended into the final evidence. Reviewers should
provision substantial RAM, allow tens of CPU
hours, and prefer fewer jobs on machines below 64 GiB. Verification is
CPU/memory intensive but requires no network access after Elan and Lake have
fetched the pinned inputs.

### Interruption and resume

Re-running the same command in the same worktree resumes accepted generated
modules. Both generators preserve an unchanged source file's modification
time, and the build skips a leaf when its `.olean` is newer than that source.
The cache is valid only when all of these remain fixed:

- Git commit and dirty tracked sources;
- `lean-toolchain` and `lake-manifest.json`;
- emitted RTL bytes; and
- generator arguments, including the 128-item leaf rule.

Do not publish `.lake` as proof evidence. It is only a restart convenience;
a Tier A clean-clone run recreates every object. Delete `.lake` and
`GeneratedRelease` after any toolchain, dependency, proof-source, or release
input change.

On Linux, every full invocation writes its measurement record under
`.lake/release-metrics/`. (The proof build remains portable when `/proc`
telemetry is unavailable.) `environment.json` records toolchain, architecture,
core count, start time, and the number of leaves already cached;
`register-leaves.csv` records each observed process duration and sampled peak
RSS; and `summary.json` records wall time, percentiles, observed CPU-hours,
parallelism, and memory peaks. Measurements do not participate in proof
acceptance.

### Scheduled enforcement

On the publication host the four standing bounds are enforced nightly by
`scripts/nightly_gates.sh` (crontab, 02:00 UTC): the wiped-tree Tier A run
inside a 4-hour bound, the `toProgram` parity gates inside it, the
documented tutorial path (`TUTORIAL.md`) with its exact three-axiom
closure, and warm-cache single-edit recheck classes against the 600-second
CI-tier gate. Each night appends one CSV row per gate under
`.lake/release-metrics/nightly-<stamp>/gates.csv`.

## Tier B: reviewer-scale substantive check

This tier is useful on a laptop but is not evidence that every LNP64-µ leaf
was independently kernel-checked. Run:

```console
scripts/review_verified_release.sh 4
```

It comprises:

1. `lake build`, `lake test`, and `lake exe audit` for the checked-in proof
   corpus;
2. the complete Acc8 release chain via
   `scripts/build_release_witness.sh acc8 4`;
3. fresh LNP64-µ emission, witness generation, and exact byte binding; and
4. kernel checks of a declared, evenly spaced sample of LNP64-µ semantic
   register leaves.

The fixed LNP64-µ sample is register leaves 0, 206, 412, 618, and 824. The
script prints an explicit warning that it did not build the full LNP64-µ
release theorem. A cached LNP object supplied for convenience may shorten
this tier, but trusting that object is explicitly a bypass of its kernel
recheck.

Tier B can expose non-determinism, broken instructions, byte drift, most trust
surface regressions, and representative large-leaf failures. It cannot replace
Tier A because the unsampled generated declarations remain unchecked by that
reviewer.

## Tier C: identification only

Published SHA-256 values identify the tagged source archive and two RTL files.
Recomputing those hashes proves only that the bytes match the publication; it
does not recheck any theorem and is not part of the soundness argument.

## Complete trusted boundary

For the final hardware interpretation, the intended trusted boundary is:

1. the Lean kernel and the three axioms named above;
2. one deterministic LF-oriented file-binding step, implemented by
   `scripts/check_release_binding.py`, which reconstructs the theorem-bound
   disk leaves in their declared order and invokes one exact `cmp -s`;
3. the adequacy statement that Yosys gives the deliberately small concrete
   SSA Verilog rendered by `SSA.Program.renderTree` the behavior described by
   `Symbolic.ModuleBehavior`; and
4. Yosys and the downstream physical flow, when making a claim about their
   outputs rather than only about the Verilog bytes.

The fast compiler/printer, witness generator, certificate synthesizer, Python
orchestration, Lean's compiled evaluator, audit executable, hashes, simulators,
and cached `.olean` files are not proof assumptions. They can propose data,
schedule checks, report evidence, or find bugs; they cannot construct an
accepted declaration whose type the Lean kernel rejects. The byte-binding
program is exceptional only in its narrow role of associating a host file
with the literal byte tree already certified by Lean.

The semantic limits of the processor and platform claims—reset realization,
2-state Verilog, DMA/interrupt/SoC scope, timing channels, and physical
effects—are listed separately in `TRUST.md`. Reproduction does not silently
expand those theorem statements.
