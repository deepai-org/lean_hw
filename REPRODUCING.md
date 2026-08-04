# Reproducing the verified release

This page is operational: it explains how to recheck the release theorem. The
claim and trusted computing base are defined once in [`TCB.md`](TCB.md), and
the concrete Verilog interpretation is defined in
[`CONCRETE_SSA_BOUNDARY.md`](CONCRETE_SSA_BOUNDARY.md).

## What is rechecked

The publication-facing declaration is:

```lean
theorem Loom.Release.Theorems.verifiedReleases :
  Nonempty Loom.Release.Theorems.VerifiedReleases
```

It contains fixed Acc8 and LNP64-µ artifacts. The Lean theorem binds concrete
SSA renderings to literal byte ropes; the external binding step then compares
those literals with `rtl/acc8.v` and `rtl/lnp64u.v`. Lean does not read the
host filesystem as part of the theorem.

## Prerequisites and pinned inputs

Install Elan, Git, Python 3, and ordinary POSIX build tools. The repository
pins:

- `leanprover/lean4:v4.28.0` in `lean-toolchain` (commit
  `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`); and
- all Lake dependency revisions in `lake-manifest.json`.

After those inputs have been fetched, the Lean verification itself needs no
network. No simulator or synthesizer is required for the theorem. Yosys is
relevant only when corroborating the separate text/tool and synthesis
boundaries.

## Tier A — full theorem recheck

From a fresh clone:

```console
git clone https://github.com/deepai-org/lean_hw.git
cd lean_hw
scripts/build_verified_release.sh
```

At the current repository head this command stops at its initial package
quality gate; [`STATUS.md`](STATUS.md) lists the two missing SPDX headers.
The procedure below describes the release check, not a claim that the current
head completes it before those regressions are fixed.

An optional positive integer selects the maximum Lean process count. With no
argument, the script derives a cap from available memory and CPUs, with a hard
maximum of 32:

```console
scripts/build_verified_release.sh 8
```

The script performs these release-specific steps:

1. runs package-quality and byte-binding self-tests;
2. emits fresh `rtl/acc8.v` and `rtl/lnp64u.v`;
3. generates concrete SSA witnesses and bounded proof modules;
4. checks each witness against `Design.toProgram`;
5. exactly binds theorem byte leaves to each RTL file with `cmp -s`;
6. regenerates structural sources and rejects content drift;
7. kernel-checks the generated render and semantic declarations;
8. rejects X/Z-sensitive syntax, missing register resets, and incomplete
   memory images in the two RTL files;
9. kernel-checks `Tools/VerifiedRelease.lean`; and
10. rejects the result unless the final theorem's axiom closure is exactly
    `propext`, `Classical.choice`, and `Quot.sound`.

The script builds the precise release dependency closure. It does **not** run
the repository-wide `lake build`, `lake test`, `lake exe audit`, simulator
lockstep, or post-synthesis equivalence suite. Run those separately when
evaluating the whole repository:

```console
lake build
lake test
lake exe audit
scripts/reproduce.sh
```

Consult [`STATUS.md`](STATUS.md) before interpreting these repository-wide
commands: a release theorem can remain valid while unrelated development
tests at the current head are red.

Successful material outputs are the two RTL files and
`.lake/build/lib/lean/Tools/VerifiedRelease.olean`. The readable theorem source
is `Tools/VerifiedRelease.lean`.

### Cost, interruption, and cache

The LNP64-µ generated certificates are CPU- and memory-intensive. Historical
measurements, including the distinction between a warm resumed run and a
clean-clone run, are in [`RELEASE_COST.md`](RELEASE_COST.md). Do not quote the
recorded 88-minute warm-cache run as a clean Tier A duration.

Re-running in the same worktree resumes up-to-date generated modules. Treat
that cache only as an engineering convenience. It is invalid after changes to
the source tree, toolchain, manifest, emitted bytes, or generator parameters.
For independent evidence, use a clean clone and do not accept supplied
`.olean` files as proof.

On Linux, the wrapper records non-proof telemetry below
`.lake/release-metrics/`. `/proc` is optional; measurement failure does not
change theorem acceptance.

## Tier B — reviewer-scale substantive check

```console
scripts/review_verified_release.sh 4
```

This runs the ordinary build/test/audit commands, the complete Acc8 release
chain, and fresh LNP64-µ emission/binding plus five sampled semantic register
leaves: 0, 206, 412, 618, and 824. Because the repository-wide tests are
included, Tier B currently inherits any red development tests listed in
[`STATUS.md`](STATUS.md).

Tier B can find command drift, nondeterminism, byte drift, and representative
large-certificate failures. It does not check every LNP64-µ generated theorem
and therefore is not a substitute for Tier A.

## Tier C — identification only

Published SHA-256 values can identify a tagged source archive and RTL files.
Matching a hash does not recheck a theorem and is not a soundness step.

## Optional standing gates

`scripts/nightly_gates.sh` runs a four-hour clean release bound, the embedded
`toProgram` parity checks, the tutorial theorem and its axiom closure, and
warm-cache edit-class bounds. It is manual; the repository installs no
scheduler. Results are measurements, not premises of `verifiedReleases`.

## Interpreting success

A successful Tier A run establishes the Lean statement and exact association
with two host files, subject to the trusted list in [`TCB.md`](TCB.md). It does
not prove Yosys, place-and-route, bitstream generation, a board wrapper,
electrical reset, timing closure, or silicon physics. Those limits are not
changed by reproduction.
