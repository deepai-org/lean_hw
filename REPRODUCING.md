# Reproducing Loom

The authoritative release claim and trusted set are in [`TCB.md`](TCB.md).
Check [`STATUS.md`](STATUS.md) before interpreting a result: development gates,
the formal release, and optional external evidence are distinct.

## Prerequisites

Install Elan, Git, Python 3, and ordinary POSIX build tools. The repository pins
Lean in `lean-toolchain` and dependencies in `lake-manifest.json`. After fetching
them, kernel proof checking needs no HDL, synthesis, or network service.

Optional Yosys, Icarus, CaDiCaL, FPGA, or ASIC legs report `PASS`, `FAIL`, or
`SKIP`. A `SKIP` is not positive evidence.

## Repository check

```console
git clone https://github.com/deepai-org/lean_hw.git
cd lean_hw
lake test
scripts/quality.sh
lake exe audit
scripts/ci.sh
```

`scripts/ci.sh` includes the expensive Epoch BMC, downstream consumer smoke,
RTL-import regressions, emission, text round trips, byte binding, and optional
independent LRAT checking. The Epoch target is intentionally absent from an
ordinary build and may require substantial time and memory.

## Full verified release

From a clean clone:

```console
scripts/build_verified_release.sh
```

An optional positive argument caps Lean processes:

```console
scripts/build_verified_release.sh 8
```

The wrapper:

1. rebuilds the fixed Acc8, LNP64-µ, and portable multiclock release closure;
2. emits fresh release RTL;
3. generates and kernel-checks the concrete SSA/certificate witnesses;
4. compares theorem byte leaves with the emitted host files exactly;
5. rejects structural or generated-source drift;
6. checks reset/memory completeness and the admitted two-state RTL subset;
7. checks the multiclock artifact independently; and
8. rejects any final axiom closure other than `propext`,
   `Classical.choice`, and `Quot.sound`.

The main readable declaration is
`Loom.Release.Theorems.verifiedReleases` in `Tools/VerifiedRelease.lean`.
Successful host artifacts are `rtl/acc8.v`, `rtl/lnp64u.v`, and
`rtl/certified_multiclock/system.v`.

The full release can exceed 20 GiB resident memory. On supported systemd/cgroup
hosts, the final axiom collector runs in a bounded no-swap unit. Reusing the
worktree cache is convenient but is not independent evidence; use a clean clone
after changing source, toolchain, dependencies, generators, or emitted bytes.

## Reviewer-scale check

```console
scripts/review_verified_release.sh 4
```

This runs ordinary repository gates, the full Acc8 chain, fresh LNP64-µ
emission/binding, and sampled large semantic leaves. It catches common command,
determinism, and byte drift, but it is not a substitute for the complete
LNP64-µ theorem recheck.

## Focused checks

Multiclock composition and its exact axiom whitelist:

```console
lake build Tests.SystemProjection Tests.SiblingProjection
lake build Tests.ProjectionProgress Tests.ProjectionAxioms
```

RTL import adapters and fail-closed cases:

```console
scripts/test_import_adapters.sh
```

Complete pinned KianV conversion and equivalence:

```console
scripts/verify_kianv_conversion.sh \
  ../kianv/gf180mcu-kianv-rv32ima-sv32 \
  build/kianv-total-conversion
```

Broader host-dependent reproduction:

```console
scripts/reproduce.sh
```

## Interpreting success

A full release pass establishes the Lean theorem and its exact association with
the named RTL bytes, subject to [`TCB.md`](TCB.md). It does not establish that
Yosys, synthesis, place-and-route, a target constraint set, a bitstream, a
foundry macro, or silicon preserves those bytes or meets physical requirements.
Matching a published SHA-256 identifies an artifact; it does not recheck a
theorem.
