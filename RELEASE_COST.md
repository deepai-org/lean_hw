# Release verification cost

The full verified release is kernel-checked without `native_decide` or a
trusted compiled evaluator. Current gate health belongs in
[`STATUS.md`](STATUS.md); commands and cache rules belong in
[`REPRODUCING.md`](REPRODUCING.md).

## Policy

- Allow up to four hours on a publication-class host for a clean Tier A run.
- Keep representative warm-cache edit checks within ten minutes.
- Treat these as resource budgets, not theorem premises or portable runtime
  guarantees.

The publication-class reference host is Linux with approximately 32 cores and
128 GiB RAM. On smaller hosts, reduce parallelism; large generated semantic
families consume several GiB per worker. Tier B is the approachable
development check, not independent publication evidence.

## Measurement

Run `scripts/nightly_gates.sh` explicitly. It is not installed as a scheduler.
The command records phase timing and Linux process telemetry under
`.lake/release-metrics/`; those files do not participate in acceptance.

For a release tag, retain:

- the exact source commit and dirty-state declaration;
- `lean-toolchain` and `lake-manifest.json`;
- host architecture, cores, RAM, and swap;
- script arguments and generated-leaf parameters;
- phase CSV, environment JSON, summary JSON, and completion marker; and
- whether the run was clean, resumed, or warm-cache.

Do not combine interrupted samples with final-source measurements or present a
warm resumed run as a clean-clone cost. Exact historical measurements belong
with the release artifact that produced them, not in current project docs.

## Why the clean run is expensive

The large release has hundreds of independently checked state obligations and
a large concrete SSA graph. Kernel reduction establishes each result. The
implementation uses action-wide plans, bounded leaves, balanced composition,
memory-specific certificates, and memory-aware worker caps to keep the work
tractable; these choices affect cost and proof-term shape, not the theorem.
