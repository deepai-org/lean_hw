# Verification cost

The release certificate is intentionally kernel-checked rather than accepted
through `native_decide` or an optimized evaluator. This page records what that
independence costs so artifact reviewers can plan rather than guess.

## Final acceptance environment

- Toolchain: `leanprover/lean4:v4.28.0`
- Lean commit: `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`
- Architecture: AArch64 Linux, glibc 2.39
- Host: 32 logical cores, 123 GiB RAM, 14 GiB swap
- LNP64-µ artifact: 8,754,762 bytes, 187,948 lines
- Expensive family: 825 independently named semantic register theorems
- Render proof layout: 128-item bounded leaves, four leaves per generated
  source batch, balanced rope composition
- Register proof layout: one separately kernel-checked theorem per register

## Measurement protocol

`scripts/monitor_release_build.py` observes the full release command without
participating in it. Linux `/proc` supplies each Lean process's actual start
time; RSS and system memory are sampled every two seconds. The complete
per-register CSV is retained with the release artifact, not rounded into only
one headline number. Aggregate RSS is reported both as summed per-process RSS
(which can double-count shared pages) and as host memory used from
`MemTotal - MemAvailable`.

An earlier acceptance attempt began at 2026-07-17 07:09:05 UTC with 28
workers. It was interrupted after the certificate generator changed, so its
283-row CSV is retained only as preliminary engineering data: those object
files do not establish acceptance of the final generated sources and its
timings will not be presented as the final verification measurement.

The authoritative current-source leaf acceptance began at
2026-07-17 10:26:51 UTC with eight workers. It completed all 825 independently
named register theorems. The two leaves that initially exposed a monolithic
kernel-reduction failure were rerun after the proof generator was changed to
compose small structural write certificates; both then passed. The aggregate
register, read, action, memory, module, and R-MC release theorems subsequently
passed. Because that resumed leaf run deliberately had no monitor process,
per-leaf percentiles are not reconstructed or claimed.

The final advertised command was then run from start to finish on the same
current sources and accepted leaf cache:

```console
scripts/build_verified_release.sh 8
```

It ran from 2026-07-18 14:44:25 UTC to 16:12:52 UTC: **5,306.488 seconds
(1 h 28 min 26.5 s)**. The run freshly completed all 8,192 ordinary Lake
build jobs, emitted and exactly bound both RTL files, repeated witness-source
generation, rechecked every aggregate certificate and the combined theorem,
ran the repository audit, and completed the exact axiom-closure gate. Peak
host memory used (`MemTotal - MemAvailable`) was **25,612,792 KiB
(24.43 GiB)**. The final closure walk alone was independently measured at
about 24 minutes and roughly 16 GiB process RSS; the LNP memory aggregate was
about 14 minutes and peaked near 13 GiB RSS.

The measurement record is
`.lake/release-metrics/lnp64u-20260718T144425Z/`. Its empty per-leaf CSV is
intentional: all 825 leaves were already accepted when this final wrapper run
started. A clean clone must recreate them, so the 88-minute cached run is not
presented as the clean-clone wall time. The honest clean Tier A envelope is the
resumable 825-leaf acceptance cost plus the measured 88-minute composition and
audit pass. Per-leaf percentiles remain unavailable for the final sources;
the interrupted preliminary sample is not blended into the release result.

## Interpretation

The expensive pass is embarrassingly parallel but memory-bound. A cached
`.olean` avoids repeating a leaf after interruption, but trusting a supplied
cache is not independent verification. Tier A in `REPRODUCING.md` checks all
825 leaves; Tier B checks a fixed five-leaf sample and labels itself as such;
Tier C only identifies published bytes.
