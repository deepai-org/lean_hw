# The intended shape of Loom

Loom's organizing goal is simple:

> A design, its executable behavior, its proofs, its tests, its emitted
> artifact, and its hardware evidence should be derived views of the same Lean
> value, with every non-derived link named as an assumption.

This is the strategic destination. The ordered implementation queue is
[`NEXTSTEPS.md`](NEXTSTEPS.md); current facts are in
[`STATUS.md`](STATUS.md).

## What the finished toolchain should feel like

A user should be able to declare state and behavior once, prove properties at
the natural abstraction level, select verified transformations, emit a small
structural artifact, and obtain a report that distinguishes theorem,
certificate, external comparison, and physical measurement without ambiguity.

The ideal workflow has six properties:

1. **One declaration per fact.** Register names, widths, reset values,
   interfaces, simulator fields, and comparison coverage are generated from
   one declaration.
2. **Local proof cost.** An invariant proof reasons only about rules that can
   touch its support; unrelated logic disappears through generic frame lemmas.
3. **Provable optimization.** Balancing, retiming, duplication, and pipelining
   are transformations with refinement theorems, not handwritten semantic
   rewrites justified by comments.
4. **Fast views remain proved views.** Specialized simulators and generators
   are derived from the design and accompanied by kernel-checked equality or
   soundness theorems.
5. **External evidence is translation validation.** Synthesis and target
   checks produce precise, certificate-backed reports with exclusions. They
   never masquerade as additions to the kernel theorem.
6. **Physical predictions are models with uncertainty.** Timing, area, memory
   mapping, and CDC assumptions are target-parameterized and empirically
   calibrated, with residual error stated.

## Non-negotiable constraints

- The publication theorem retains its three-axiom closure.
- No convenience feature silently adds the Lean compiler, solver, printer,
  parser, or synthesis flow to the theorem TCB.
- `Loom` remains machine- and target-generic. Target facts enter through data
  profiles and wrappers.
- A green result cannot be obtained by omission: new state, signals, memories,
  operators, and assumptions must be checked or explicitly excluded.
- Counterexamples improve statements and designs; they are not papered over by
  weakening prose.
- Public documentation describes the current system. Git, the changelog, and
  compact evidence records preserve history.

## Capability workstreams

### A typed, single-source design language

Typed register/memory handles and declaration notation should eliminate
stringly duplicated widths and names while elaborating to the current EDSL.
Generated state adapters and comparators should make simulation coverage
complete by construction.

### Property-directed proof automation

Footprints, support inference, frame rules, and cycle tactics should make proof
cost scale with a property's dependency cone. A future one-rule-at-a-time
reasoning layer is worthwhile only if it is verified to flatten to the current
ordered last-write-wins semantics.

### A verified transformation library

The existing tree builders and retiming seed should grow into composable
refinement-preserving optimization passes. The legible design remains the
source; the fast implementation is a proved transform chain.

### Derived simulation

A specialized evaluator generated from `Design` should replace hand-maintained
cycle mirrors. The generated equality theorem and complete state comparator
are part of the feature, not follow-up documentation.

### Translation validation and target models

The netlist checker should cover every shipped artifact it claims, grow by
explicit operator/cell instances, and keep LRAT checking independent of the
solver. Static timing/area estimators should be useful engineering predictors
without being oversold as physics theorems.

## Progress (2026-08-04)

**W1.1 — emit-time gates.** `Design.emit` enforces read-validity, duplicate
names, D19 sync-read declaration, D38 write-port shape and D39a outputs. It
caught a live bug in EXT-7 stage B on its first run.

**W2 — frame rules.** `Loom/Hw/Frame.lean`. The write side already existed;
`Expr.eval_congr_of_agree` adds the read side, so an expression provably cannot
see state outside its `readSites` footprint — the same footprint W1.1 gates on,
not a second one. `Design.cycle_regs_notin`/`cycle_mems_notin` lift the write
frame to a whole cycle. `regUnwrittenB`/`memUnwrittenB` make the side condition
a `decide`, because a frame rule whose hypothesis costs more than the property
it frames saves nothing.

**W3.1 — verified transforms.** The balanced-tree builders were already in
`Loom/Hw/Trees.lean` (D18); the work here was discovering that, not rewriting
it.

**W5 — derived simulation.** `FastEval` already generates the evaluator.
`Loom/Hw/StateCover.lean` adds the complete comparator: the design enumerates
its own state, the harness declares what it compared, and the difference is a
named failure. It found five uncompared memories in `lnp64mini` on first run
(EXT-5's gate table and continuation, EXT-6's capability inbox), meaning two
selftests had been green without ever looking at the state their increments
added. Enforced by `coverageselftest`.

Still open: W1's typed declaration notation, W2's cycle tactics, W3's pass
composition, W4's remaining eqcheck coverage, W6's timing model, and W5's
generated *equality theorem* (the evaluator is derived; the proof that it
agrees with `Design.cycle` is not yet stated in those terms).

## Success criteria

Loom reaches this shape when a substantial processor can be changed at one
declaration site; all derived views either update automatically or fail with a
named obligation; properties recheck in proportion to affected logic; the
optimized emitted implementation is connected by composed proofs; and the
release report makes every remaining trusted or empirical link obvious to an
outside reviewer.

## W5 addendum: the comparator is derived, not declared

`Loom/Hw/StateCover.lean` made a *hand-written* comparator's omissions into a
named failure. `Loom/Hw/Diff.lean` removes the hand-written comparator: the
`Design` already declares its registers and memories, so the complete set of
observable coordinates is derivable, and a comparison derived from the
declarations cannot omit a declaration.

`Design.coords` / `diffCoords` / `diffAgainst` / `diffReport` live in Loom, so
this is not per-machine scaffolding — any machine gets it. A machine supplies
only a reader from a coordinate to its reference model's value, and
coordinates the reference does not model are reported as **unmodelled**
rather than skipped. That distinction is the point: the old comparator could
only omit them, and an omission is indistinguishable from agreement.

`lnp64mini` uses it through `lockstepDerived` + `issAt`, and `opDiffSelftest`
runs *generated* programs — one per ALU opcode per boundary vector — through
it. Coverage is therefore mechanical on both axes: every opcode in the matrix,
every coordinate the design declares. That is what the six-opcode bug needed
and did not have; it survived because EDSL≡ISS was checked with hand-written
programs and nothing executed `not`, `sltu`, `bgeu`, `srli`, `srai` or `sltiu`.

**The `FastEval` path closes the cost objection.** `Design.coordPlan` resolves
every coordinate to its flat index once, and `diffFastAgainst` walks array
reads instead of the closure chain a functional `RegEnv` accumulates. The same
matrix went from *not finishing in twenty minutes* to **6 seconds** for 351
programs, so the nine-vector matrix is affordable and the gate is practical.
This is not a shortcut around the semantics: `fastCycleOpen_eq` proves the flat
evaluator agrees with `Design.cycleOpen`.

The gate was verified to **fail** on the reintroduced bug — `FAIL sltu (opcode
0x26): 20 EDSL≡ISS mismatches`, naming the opcode and printing
`rf[3]: edsl=1 iss=0`. A gate that has not been seen failing is not known to
work.

**The deeper half, first increment (2026-08-05):** matrix equality is now a
THEOREM. `lockstepPure` is `lockstepFast` with the printing removed — a pure
mismatch count — and `Machines/Lnp64mini/MatrixTheorem.lean` states

```lean
theorem matrix_agrees : matrixMismatches = 0 := by native_decide
```

so a build of the library in which the design and the ISS disagree on the ALU
matrix **does not exist**. Verified to fail: reintroducing the `sltu` inversion
makes `native_decide` refuse the build, naming the proposition false.

Honesty about what this buys: `native_decide` evaluates with the compiler, so
the trusted base is the same one the test uses. What changes is *where* the
check lives — inside the artifact the kernel accepts, so no harness has to
remember to run it, no output has to be read, no exit code wired into CI.
Strictly stronger than a test someone must run; strictly weaker than a symbolic
proof.

**Still open:** the rest of the deeper half — deriving the reference model
itself from the `Design` and proving equality symbolically, per opcode, rather
than by evaluation over a finite vector set. The load/store/branch/jump legs
also stay in the test gate for now: their cmd streams and dual-memory-path
checks are where the test form earns its keep.

## What sel_cond taught (2026-08-07): consistency is not correctness

The renumbering campaign's killer — three identical silicon panics across
three attempts — was `sel_cond` deriving SEL's condition from `op[2:0]`, an
assumption about a retired opcode layout, **duplicated by hand in the ISS**.
Design and reference were wrong *together*, so every internal gate this
document describes was green: the matrix (which could not build the 5-slot
form), the derived comparator (comparing against the co-wrong oracle), even
the matrix THEOREM. The one implementation that knew — an independent
emulator in another repo, in another language — was unreachable through
exactly the op that mattered.

Three corrections to the intended shape follow, in strength order:

**1. The reference must be derived or it is a liability.** W5's deeper half —
Loom generating the executable model from the `Design` — is no longer a
nice-to-have; it is the structural remedy for the wrong-together failure
mode. A hand-mirrored ISS is a second copy of the semantics, and a second
copy can copy the mistake. Where the hand-ISS survives in the interim, every
op family must be drivable by a differential against a genuinely independent
implementation, and an op no differential can drive is a standing risk to be
listed, not an exclusion to be filed.

**2. Oracles carry declared coverage.** `Loom.Hw.Oracle` +
`diffAgainstOracle`: a reference's unmodelled state is a CLOSED, named list,
and an unmodelled coordinate outside it fails the run. The open-ended
fall-through was the same omission-looks-like-agreement hole as the
hand comparator, one level up. Negative-control discipline applies: the
enforcement was watched failing (an undeclared `rx_mem`) before it was
believed.

**3. The real workload is a rung of the ladder, not just the board's.**
`scripts/boot_sim.sh` boots the ACTUAL guest image on the emitted RTL in
iverilog: the failure that cost three board campaigns reproduced there in
twenty seconds, with every internal signal a `$display` away. The ladder's
gap was between "generated programs on the RTL" and "the image on silicon";
simulation of the shipped artifact fills it, and runs before board
forensics, not after.

A hazard-class note for the lint mindset: the bug was **arithmetic on an
identifier** — deriving meaning from the numeric value of an opcode byte.
No literal-lint can see it, because there is no literal. The countermeasure
is structural (keyed dispatch off named constants, generated coverage per
name), not lexical.

And one physical-world constraint promoted to a design input: at ~52% LUT
utilization on the xc7z020, routing seeds became coin flips (the recorded
ceiling is ~55%; one seed burned six hours flat). Area headroom is part of
the correctness budget — a design that cannot route repeatably cannot be
iterated on — so W6's cost model earns priority alongside the deeper half
of W5.

## W6 addendum: cost is a property transformations carry (2026-08-07)

The first increment exists (`Loom/Hw/Cost.lean`, `CostTarget.lean`,
`scripts/fit_cost.py`, `lake exe costreport`). The shape it settled into is
worth stating, because it generalizes past area.

**The division of labour is the design.** Loom proves that a transformation
does not make the *abstract implementation-cost vector* worse. Calibration
maps that vector to one target's resources and to a closure-risk estimate.
Neither half is allowed to contaminate the other: the proved half needs no
weights and cannot be invalidated by a vendor tool release; the estimated
half is empirical metadata and says so at every use site. This is the same
split that already worked for memories — D19's sync-read rule is universal,
D38's port budget is a profile — generalized from one predicate to a
quantity.

**A vector, not a number.** Collapsing to a scalar requires weights, and
weights are exactly the uncertain, target-specific part. Keeping the
dimensions separate keeps the exact half exact. `macroBits` versus
`softBits` is a dimension rather than a weighting for a measured reason:
that boundary is where CapWalk's 14× (9 523 → 671 LUT, identical logic)
lived, and a model that folded memory into an operation count would have
been wrong by an order of magnitude at the one moment it mattered.

**The interesting theorem is relative, not absolute.** Nobody can prove
"this design is 44 000 LUTs" — synthesis shares, folds and retimes. What is
provable, and useful, is *non-increase*: this pass does not worsen any
dimension. That is a statement about the transformation library, it
composes (`add_le_add`), and it makes the metric trustworthy without
calibration. Cost thereby joins correctness as a property a verified
transformation carries, which is the point: a pass that preserves semantics
while quietly tripling area is not a pass anyone can afford to apply.

**Capacity and closure are different claims, on both technologies.** "Does
it fit" is physical. "Will the tools close it" is a calibrated threshold on
one part, one tool version, one design family — never a universal constant.
FPGA routability and ASIC placement density are the same shape; neither
flow targets 95 % and expects to converge.

**The honest result from day one, which is the most valuable output so
far.** The vector does *not* separate the lnp64mini design that routed from
the one that did not. They differ by ~1 % in cells and both land at 52–53 %.
So at the margin that actually cost this project nine hours, the
discriminator is congestion, not capacity. Three consequences: the report is
a risk signal rather than a verdict; `maxFanout` is a placeholder for
congestion modelling that does not exist yet; and no gate is wired into
`Design.emit` until a fit exists with more designs than weights behind it.
A model that would have been *wrong* about the case that motivated it should
not be handed refusal authority.

**A principle now visible three times.** Every empirical number in Loom
carries how it was obtained: `MemTarget`'s ECP5 profile is labelled a
datasheet reading, `Oracle` names the coordinates it does not model, and
`CostTarget` carries tool version, design family, and an underdetermined-fit
warning. The recurring failure this defends against is uniform — an
unlabelled estimate becomes a fact by being repeated, and an omission looks
exactly like agreement. The rule generalizes: *a number without provenance
is not admissible evidence*, and the place to enforce it is the type, not
the reviewer's memory.
