# Verification cost

The release certificate is intentionally kernel-checked rather than accepted
through `native_decide` or an optimized evaluator. This page records what that
independence costs so artifact reviewers can plan rather than guess.

## 2026-07-18 performance investigation

The original LNP64-µ release checker validated the complete source action
tree independently for every one of 825 registers.  A profiled full-size leaf
(`SemanticRegBatch0`) established that this, rather than imports or disk I/O,
was the dominant cost:

| configuration | wall time | meta interpretation | kernel checking | peak RSS |
| --- | ---: | ---: | ---: | ---: |
| explicit `NoRegWrite` proof trees | 10m 47.8s | 290s | 344s | 3.28 GiB |
| structural Boolean footprint check | 5m 09.6s | 215s | 91.4s | 3.15 GiB |

Imports took about 1.1 seconds in both runs.  The compact check also reduced
the leaf `.olean` from about 11 MiB to under 1 MiB.  This optimization is
kernel-checked and preserves the public characterization of `writesRegB` as
membership in `Act.regWrites`; it changes only the reducible implementation
and the shape of generated proof terms.

The remaining 215-second interpretation cost shows that per-register checking
is still the wrong asymptotic architecture.  The next release-checker revision
must validate a shared whole-action register-update index once, then reduce
each register theorem to an indexed lookup plus its expression-root check.
The target complexity is one action traversal plus one lookup per register,
not one action traversal per register.

A full-scale rule-level over-approximation spike ruled out a tempting but
insufficient shortcut.  The four LNP64-µ rules write 8, 800, 8, and 1 distinct
register keys respectively.  Because the large core rule writes 800 of the
825 registers, a single footprint per rule prunes almost none of the expensive
core traversal.  Its monolithic kernel coverage theorem was stopped after
168 seconds when RSS had already reached about 38 GiB.  The production path
was restored rather than accepting that memory profile.  The next index must
therefore be subtree/DAG-granular and its coverage proof must be composed from
separately named bounded leaves; a rule-level Boolean theorem is not enough.

The same spike exposed another invalidation edge: generated `Root.lean` data
imports `Loom.Release.SymbolicCertificate`, so changing checker algorithms
forced the multi-gigabyte SSA root to rebuild (roughly four minutes and a
13 GiB peak in this run).  New index experiments should live in a separate
module, and the generated data layer should ultimately import only stable
symbolic data definitions, not checker implementations.

A subsequent whole-state prototype identified the missing asymptotic
abstraction.  `Compile.nextReg` presents compilation as one complete action
traversal per register, and the original release checker copied that
presentation.  `Loom.Hw.WholeRegisterPlan` instead traverses an action once
and constructs all declaration-aligned register projections together.  Its
generic theorems prove that each projected plan denotes exactly the existing
`nextReg`; the reference compiler and its correctness proof do not change.

On the complete LNP64-µ design, compiled evaluation constructed the four
rule-plan families below the millisecond clock resolution.  The result has
180,254 relevant plan nodes across 825 registers, close to the unavoidable
concrete SSA size rather than 825 copies of the complete source action.  A
single kernel decision reduction of the full plan-node count reached its
reduced `true = true` form in 37 seconds with a 6.94 GiB peak before exposing
an auxiliary-lemma limitation in the custom `kernel_decide` wrapper.  A
monolithic direct-`rfl` variant was stopped after 99 seconds.  The production
design should therefore compose separately named bounded plan blocks, not one
180,254-node equality.  This measurement changes the target from a finer
absence index to a shared source-derived update plan plus cheap bounded SSA
root checks.

The same rebuild exposed a separate edit-loop problem in the R-MC proof graph.
After the foundational compiler module changed, individual modules including
`RMCRetireRev`, `RMCRetireGateCall`, and `RMCRetireGateCallSuccess` each took
roughly five to six minutes.  These are ordinary theorem-elaboration and
module-boundary hotspots, distinct from release byte certification; they need
targeted `lean --profile` passes and narrower import boundaries.

The first dependency repair now keeps `Act.memWrites`, `Act.regWrites`, and
their generic frame theorems in `Loom.Hw.Footprint`, below the compiler.
The R-MC development imports that stable footprint layer directly.  A change
to `Loom.Hw.Compile` therefore no longer invalidates the multi-minute R-MC
chain merely because its proofs use action frame facts.  This does not make a
clean R-MC build cheap: the observed hotspots still include `RMCHalt` (208s,
about 8.2 GiB RSS), `RMCZero` (277s), and `RMCIssue` (233s, about 5.6 GiB RSS).
It does, however, remove those costs from the normal compiler and release
certificate edit loop.  An explicit content change to `Loom.Hw.Compile`
followed by `lake build Machines.Lnp64u.Theorems.RMCRetireGateCall` completed
from cache in 0.80s; before the split, that edit invalidated the chain ending
in the 363-second `RMCRetireGateCall` module.

The timings below describe the earlier accepted implementation and remain a
baseline, not a performance claim for the in-progress optimized checker.

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

## Whole-plan diagnosis (2026-07-19)

The whole-register transpose proved that the source algorithm itself is not
intrinsically an hours-long computation.  Compiled evaluation constructs all
four LNP rule-plan families below the timer's millisecond resolution.  The
pathology occurs when generated semantic theorems repeatedly ask elaboration
and kernel reduction to reconstruct that closed data from reducible design
functions.

Two full-scale probes made the boundary precise:

- constructing and counting the 180,254 compact plan nodes reached the
  reduced `true = true` goal in 37 seconds (6.94 GiB RSS), after which the
  monolithic decision-proof wrapper failed to package the dependent result;
- a 16-register theorem that directly exposes
  `RulePlans.ofRules sources design.rules` still exceeded 90 seconds.  The
  structural proof producer had not yet reached its first register check: it
  was normalizing the shared plan argument itself.

Consequently, neither more workers, smaller register batches, nor another
leaf-size search addresses the remaining cost.  The release path needs a
materialized plan snapshot and one generic, kernel-checked bridge from that
snapshot to the mathematical `RulePlans.ofRules` specification.  All SSA
root checks must consume the already-materialized snapshot, never recompute
it.  The same rule applies to register-slice alignment: repeated
`design.regs[index]? = ...` reductions must be replaced by one certified
snapshot/slice relation.

The target cost model is therefore:

1. one source-design-to-plan snapshot certificate;
2. linear structural checking of the compact snapshot against SSA;
3. bounded composition and the existing exact artifact binding.

Only step 1 may normalize the source design, and it must do so once for the
release, not once per register or per 16-register batch.

## Why the release checker uses the module graph (2026-07-27)

This is a deliberate choice, not an accident, and it is worth stating because
it constrains every optimization below.

Rule 1 bans `native_decide` repo-wide (`TRUST.md`), and the ban is mechanically
enforced: `Tools/Audit.lean` fails the build if any declaration's axiom closure
contains `Lean.ofReduceBool` or `Lean.trustCompiler`.  So the tempting
alternative -- one verified `checkAll : Cert -> Bool`, proved sound once and
evaluated by compiled code -- is unavailable.  It would add the Lean compiler
to the TCB and break the headline claim that the closure is exactly `propext`,
`Classical.choice`, and `Quot.sound`.  Kernel reduction is the only admissible
evaluator, so certificate checking is decomposed into many named declarations
and parallelism is bought by splitting them across modules and processes.

The premise underneath that choice is only half true, and the half that is
false is expensive.  Lean elaborates and kernel-checks *independent
declarations within a single module* in parallel.  The generated tree
currently disables exactly that: `set_option Elab.async false` appears in
8,610 generated modules, and every generated module is compiled with
`lean -j 1`.  The design therefore pays a per-obligation import cost to buy
parallelism that it has switched off inside each process.  Note that
`Loom/Release/KernelDecide.lean` and `Loom/Release/SymbolicDecide.lean` both
set `Elab.async false` internally around auxiliary-lemma creation, so this is
not a free flag flip -- the custom elaborators may depend on it.  Establishing
whether they do is a prerequisite for any batching work.

### The import floor

Measured on the 2026-07-21 tree with empty modules that import the stated set
and prove nothing:

| module contents | wall | peak RSS |
| --- | ---: | ---: |
| `import Loom.Release.SymbolicDecide` | 1.28 s | 785 MiB |
| the above `+ ActionCert` | 2.67 s | 795 MiB |
| the `DagCut*Query*` import set | 5.55 s | 1.42 GiB |

That tree had 16,372 generated modules, 732 MiB of generated sources, and a
20 GiB `.olean` output.  `ActionCert.olean` alone was 209 MiB and was imported,
directly or transitively, by about 1,106 modules.  Total certificate size is
therefore multiplied by consumer count -- the same `O(consumers x artifact)`
shape that the whole-register transpose removed at the algorithm level,
reappearing in the transport layer where it does not look like an algorithm.

The Acc8 artifact shows the same floor without any large certificate to blame.
Its complete witness pipeline runs in 22 s, and *every* phase reports
parallelism near 1.0 on a 32-core host: roughly fifteen sequential Lean process
startups at about 1.6 s each.

### Budget arithmetic

A 10-minute wall target on 32 cores is 19,200 CPU-seconds.  At the ~1.3 s
fixed cost per module measured above, 16,372 modules is about 21,300
CPU-seconds of process and import overhead before any obligation is checked.
Batching is therefore a hard requirement rather than a tuning knob, and the
module count -- not the leaf size -- is the quantity to solve for.  Landing
near 2,000-4,000 modules leaves roughly 4-6 s of budget per module.

### Measuring it

`scripts/phase_timing.sh` gives every build script a shared `run_phase` that
appends `started_utc,scope,label,wall_seconds,cpu_seconds,parallelism` to one
CSV per run under `.lake/release-metrics/`.  `cpu_seconds` is reaped-children
CPU, so `parallelism = cpu/wall` separates phases that are genuinely serial
from phases that are merely badly scheduled.  A phase near 1.0 on this host
will not improve with more workers no matter how the leaves are sized; those
phases, not the aggregate CPU total, determine whether a wall-clock target is
reachable at all.
