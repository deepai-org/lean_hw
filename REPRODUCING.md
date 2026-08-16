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

It contains fixed Acc8, LNP64-µ, and portable two-clock System artifacts. For
the processors, the Lean theorem binds concrete SSA renderings to literal byte
ropes and the external binding step compares those literals with `rtl/acc8.v`
and `rtl/lnp64u.v`. For the System, the theorem names the literal RTL member of
the certified emitter's file list, and the release command writes that exact
value to `rtl/certified_multiclock/system.v`. Lean does not read the host
filesystem as part of the theorem.

## Prerequisites and pinned inputs

Install Elan, Git, Python 3, and ordinary POSIX build tools. The repository
pins:

- `leanprover/lean4:v4.28.0` in `lean-toolchain` (commit
  `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`); and
- all Lake dependency revisions in `lake-manifest.json`.

After those inputs have been fetched, the Lean verification itself needs no
network. No simulator or synthesizer is required for the theorem. Yosys is
relevant only when corroborating the separate text/tool and synthesis
boundaries. `scripts/test_multiclock_synthesis.sh` is the small neutral-RTL
extension-boundary sanity check: it emits the certified two-clock System and
asks an available Yosys to elaborate, check, and synthesize it. This does not
tie Loom to Yosys and is not proof that a particular FPGA or ASIC
implementation is physically safe.

Optional workflow legs print a final `RESULT PASS`, `RESULT FAIL`, or
`RESULT SKIP` line. A skip is successful workflow control, not positive
corroboration, and must remain visible in retained release logs.

## Tier A — full theorem recheck

From a fresh clone:

```console
git clone https://github.com/deepai-org/lean_hw.git
cd lean_hw
scripts/build_verified_release.sh
```

An optional positive integer selects the maximum Lean process count. With no
argument, the script derives a cap from available memory and CPUs, with a
memory-safety maximum of 8 and 16 GiB reserved outside heavy proof pools:

```console
scripts/build_verified_release.sh 8
```

On a cgroup-v2 systemd host, the final axiom collector additionally runs in a
28 GiB/no-swap unit. The measured current peak is 21.4 GiB; exceeding the cap
kills that release phase rather than pressuring the whole interactive host.
Other hosts run the same collector serially and print that containment is
unavailable.

The script performs these release-specific steps:

1. runs package-quality and byte-binding self-tests;
2. emits fresh `rtl/acc8.v`, `rtl/lnp64u.v`, and
   `rtl/certified_multiclock/system.v`;
3. generates concrete SSA witnesses and bounded proof modules;
4. checks each witness against `Design.toProgram`;
5. exactly binds theorem byte leaves to each RTL file with `cmp -s`;
6. regenerates structural sources and rejects content drift;
7. kernel-checks the generated render and semantic declarations;
8. rejects X/Z-sensitive syntax in all three RTL artifacts, plus missing
   register resets and incomplete memory images in the processor artifacts;
9. independently kernel-checks and exactly axiom-audits
   `Tools/MulticlockRelease.lean`;
10. kernel-checks `Tools/VerifiedRelease.lean`; and
11. rejects the result unless the final theorem's axiom closure is exactly
    `propext`, `Classical.choice`, and `Quot.sound`.

The script builds the precise release dependency closure. It does **not** run
the repository-wide `lake build`, `lake test`, `lake exe audit`, simulator
or lockstep suite. Run those separately when
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

Successful material outputs are the three RTL files and
`.lake/build/lib/lean/Tools/VerifiedRelease.olean`. The readable theorem source
is `Tools/VerifiedRelease.lean`.

### Cost, interruption, and cache

The LNP64-µ generated certificates are CPU- and memory-intensive. Current
planning measurements and the distinction between a warm resumed run and a
clean-clone run are in [`RELEASE_COST.md`](RELEASE_COST.md).

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

## Focused compositional multiclock proof gate

The semantic System-fragment projection and its exact axiom whitelist can be
checked independently of the large release build:

```console
lake build Tests.SystemProjection
lake build Tests.ProjectionProgress
lake build Tests.ProjectionAxioms
```

The second command prints readable dependency closures and also executes a
fail-closed kernel dependency audit. It succeeds only when every focused
projection, predicate-progress, and demonstration declaration stays within `propext`,
`Classical.choice`, and `Quot.sound`; a newly introduced axiom makes
elaboration fail. Consult [`STATUS.md`](STATUS.md) before interpreting a
repository-wide `lake test`, because an unrelated development target may abort
while this focused gate remains independently reproducible.

## Interpreting success

A successful Tier A run establishes the Lean statement and exact association
with three host RTL files, subject to the trusted list in [`TCB.md`](TCB.md). It does
not prove Yosys, place-and-route, bitstream generation, a board wrapper,
electrical reset, timing closure, or silicon physics. Those limits are not
changed by reproduction.
