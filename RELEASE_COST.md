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

## Measured W, and a correction (2026-07-28)

The release pipeline now completes end-to-end from clean sources. Getting
there took thirteen defects, every one of them in the build and generation
layer and none in the proof architecture; they are listed under "Why clean
runs matter" below.

`scripts/measure_check_cost.py` separates the cost that restructuring can
remove from the cost that it cannot. For each family of generated modules it
compiles a probe carrying that family's exact import block and no
declarations; the probe's CPU time is the family's per-process toll, and

    W_family = observed_family_cpu - module_count * toll_family

Measured across the runs in `.lake/release-metrics/`:

| quantity | value |
| --- | ---: |
| W, irreducible kernel checking | **95,786 CPU-s (26.6 CPU-h)** |
| per-process toll, removable by batching | 8,920 CPU-s (**9%**) |
| budget at 10 min x 32 cores | 19,200 CPU-s |
| clean-run estimate | 160 min wall, 31.3 CPU-h |

**This corrects an earlier analysis recorded in this file.** The section above
argues that per-process import cost is the dominant pathology, extrapolating
about 21,000 CPU-s of overhead from 16,372 modules at roughly 1.3 s each --
more than the entire budget. That extrapolation was wrong twice over: the
4,575 dead `DagCut*Query*` modules are gone, and the surviving families'
tolls are well below the single-module figure it was based on. The toll is
real but it is 9% of the total. Batching is worth having; it is not the
lever.

The cost is concentrated in checking, and the checking already parallelizes
close to perfectly:

| phase | wall | CPU | parallelism |
| --- | ---: | ---: | ---: |
| hybrid registers | 2,271 s | 67,646 s | 29.8 |
| semantic wire batches | 743 s | 12,181 s | 16.4 |
| wire batches | 379 s | 11,588 s | 30.6 |
| lake prerequisites (R-MC closure) | 2,317 s | 6,253 s | 2.7 |
| read register batches | 235 s | 3,819 s | 16.2 |
| action leaves and join checks | 112 s | 3,350 s | 29.9 |

`hybrid registers` alone is 70% of W at 29.8x on 32 cores. No scheduler
improves that. Against it sits a separate set of phases that use one core:

| serial phase | wall | parallelism |
| --- | ---: | ---: |
| semantic memories | 846 s | 1.00 |
| release theorem axiom closure | 698 s | 0.76 |
| port certificate generation | 504 s | 1.00 |
| semantic reads | 396 s | 1.00 |
| semantic actions | 201 s | 1.00 |
| hybrid core shape | 201 s | 1.00 |
| shared action certificate | 161 s | 1.01 |

Those exceed ten minutes of wall clock between them before any parallel work
is scheduled at all.

### What this settles

A 10-minute, 32-core target is not reachable by restructuring this pipeline:
W is 5.9x the budget and the dominant phase is already using the machine.
The number is not, however, a measurement of the trust posture's price. It is
the price of *translation validation* -- re-deriving the shipped artifact's
semantics per node -- which is what `NEXTSTEPS.md` section B retires by
relating the artifact to `compile d` once. Read the verdict as "unreachable
without B", not "unreachable".

Two smaller items are worth taking regardless. `port certificate generation`
spends 504 s synthesizing a single imported batch, because the LNP64-u path
runs all of `CertGen` for its memory-port family while its other three
families have no importers. And the R-MC prerequisite phase runs 2,317 s at
parallelism 2.7, which is a critical-path problem inside the proof modules
themselves and survives section B untouched.

### Why clean runs matter

The pipeline had never completed on these sources. Thirteen defects surfaced
in one clean-checkout sequence, none visible from a warm tree:

1. `quality.sh` required `ripgrep`, an undocumented host dependency.
2. `test_release_binding.py`'s fixture had drifted from its checker.
3. `Loom.Release.SymbolicVerified` was not a named lake prerequisite.
4. The `SysOps` opacity refactor broke three R-MC proof modules.
5. 4,575 generated `DagCut*Query*` modules were dead.
6. The prerequisite list named 7 of 18 external imports.
7. `generateHybridRules` had 33 bailouts that exited 1 with no message.
8. Six reference emitters across two languages disagreed on spelling.
9. Three of five certificate elaborators never anchored their alias names,
   so 825 modules each defined `_releaseExpr9`.
10. 32-way parallelism on a 6.65 GiB-per-module family exhausted memory and
    the kernel killed the build silently.
11. The hybrid batch modules never defined `semanticOutputBehavior`.
12. Memory-port certificates were never re-provided after the migration.
13. `VerifiedRelease.lean`'s own imports were not built.

Items 3, 6, 12 and 13 are one root cause: **anything compiled outside Lake's
module graph carries a hand-maintained dependency list, and every such list
in this repository was incomplete when written.** Items 8, 9 and 11 are a
second: a contract asserted in a comment that nothing enforced. Both are
arguments for the content-addressed, derived-dependency infrastructure in
`NEXTSTEPS.md` section D, which should be read as correctness work rather
than as an optimization.
