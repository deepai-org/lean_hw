# Release verification cost

The full release is intentionally kernel-checked without `native_decide` or a
trusted compiled evaluator. This page gives reviewers a usable resource model.
Current gate health is in [`STATUS.md`](STATUS.md); commands and cache rules
are in [`REPRODUCING.md`](REPRODUCING.md).

## Current policy

Two different budgets apply:

- **Audit tier:** a clean full release should complete within four hours on
  the documented publication-class host.
- **CI/edit tier:** each representative single-edit recheck from a valid warm
  cache should complete within 600 seconds.

`scripts/nightly_gates.sh` measures both policies on demand. It is not run by a
repository-installed scheduler.

## Latest complete clean baseline

The latest recorded complete clean gate predates the current red quality/test
state and is therefore a planning baseline, not evidence for current head.
It used:

- Lean 4.28.0, commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`;
- AArch64 Linux with 32 logical cores, 123 GiB RAM, and 14 GiB swap;
- generated sources, build objects, and RTL removed before the run; and
- pinned upstream packages already present under `.lake/packages`.

The complete release gate finished in **9,580 seconds (2 h 40 m)**, inside the
four-hour audit bound. The combined theorem and both `toProgram` parity checks
passed. A nearby authoritative clean run measured **125,683 CPU-seconds (34.9
CPU-hours)** and **10,459 seconds (2 h 54 m)** wall time; the difference is
normal pipeline evolution, not a claim that either number applies to current
head.

The measured 32-core perfect-parallelism floor for that earlier clean run was
3,928 seconds. Consequently, a ten-minute clean audit target was not credible;
the ten-minute requirement belongs to incremental edit classes instead.

## Last measured edit classes

| Gate | Wall time | Limit |
|---|---:|---:|
| Tutorial path and axiom closure | 3 s | 600 s |
| User-design edit | 1 s | 600 s |
| Hybrid register leaf | 59 s | 600 s |
| Memory-init block | 3 s | 600 s |
| Memory-port leaf | 253 s | 600 s |
| Semantic-memory aggregator | 3 s | 600 s |

These measurements also predate current head. They define regression classes,
not promised runtimes on arbitrary hardware.

## Resource guidance

- Prefer a Linux host with approximately 32 cores and 128 GiB RAM for Tier A.
- On hosts below 64 GiB, reduce the job count; generated semantic-wire and
  register families consume several GiB per worker.
- Allow up to four hours for a clean publication-scale run and retain extra
  time for dependency download and failures.
- Tier B is the laptop-oriented substantive check, but it samples five
  LNP64-µ register leaves and is not publication proof evidence.
- After an interruption, an unchanged worktree may resume from generated
  sources and `.olean`s. A supplied or stale cache is never independent
  verification.

## Why the build is expensive

The large artifact has hundreds of independently checked state obligations
and a very large concrete SSA graph. The release path decomposes proof checking
across generated modules because kernel reduction, rather than compiled
evaluation, must establish each result. The dominant cost is substantive
checking of large register/wire families plus the LNP64-µ refinement closure;
process startup and imports are real but are not the main asymptotic cost.

The implementation uses:

- whole-action/register plans to avoid traversing the source action tree once
  per register;
- bounded proof leaves and balanced composition to avoid monolithic string or
  list normalization;
- action-wide cuts and independently named register/memory obligations;
- memory-specific certificate generation rather than unused register work;
  and
- memory-aware worker caps derived from available RAM.

These choices affect cost and proof-term shape, not the public theorem.

## Measurement records

Full invocations write phase timing and Linux process telemetry below
`.lake/release-metrics/`. Metrics do not participate in theorem acceptance.
For a release tag, retain:

- the source commit and dirty-state declaration;
- `lean-toolchain` and `lake-manifest.json`;
- host architecture, cores, RAM, and swap;
- script arguments and generated-leaf parameters;
- phase CSV, environment JSON, summary JSON, and completion marker; and
- whether the run was clean, resumed, or warm-cache.

Never combine interrupted preliminary samples with final-source measurements,
and never present a warm resumed run as a clean-clone cost.
