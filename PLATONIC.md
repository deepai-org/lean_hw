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

## The first feature the toolchain carried (2026-08-07)

EXT-9 rung 1 — a 32 KB instruction cache — is the first substantial feature
built *after* the disciplines existed rather than before them, so it is the
first honest test of whether they help while you work or only explain
afterwards. Three of them fired, at three different moments:

**Before any RTL existed**, W1.1's emit gate refused the design: the cache's
sync-read latches were read but never declared. The failure named the
register and the width. Without it, an undeclared read evaluates to zero
forever — a design that simulates, emits, and is simply wrong.

**During the first lockstep run**, the EDSL/ISS comparison found a real bug
in the fill: the tag was shifted into the valid-bit position, so every fill
stored `(tag&1) << 17`. It surfaced as `st: edsl=S_FW iss=S_RD` — one model
hitting where the other missed. That is exactly the shape a cache defect
takes, and exactly why the plan has the ISS *model* the cache instead of
abstracting it. An "abstract, transparent cache" in the reference would have
compared equal to a broken one.

**On the first matrix run**, the `Oracle` closed-list check — added days
earlier for a different reason — made teaching the oracle about the new banks
mandatory, reporting `UNDECLARED-UNMODELLED ic_tag[...]` rather than quietly
comparing less state than before. A gate written for one omission caught a
different one, which is the sign it was aimed at the class and not the
instance.

Two observations worth generalizing.

**The disciplines are load-bearing at design time, not just at review time.**
D19 (sync-read shape) and D38 (one write port) did not *check* the cache — they
*determined* it. "One latch site per bank, one write funnel per bank" is not
an audit rule the design happens to satisfy; it is the reason the banks land
in block RAM rather than becoming 4096-deep read muxes, and it is why the same
design is `realizableOnB` on `asicSram` without a second thought. A rule that
shapes the artifact is worth more than a rule that grades it.

**The cost model changed a decision before any code was written.** Projecting
the rungs put the epoch top at ~54.8 %, past the closure threshold it had just
needed four routing seeds to beat, so the cache went onto the dual top (48 %,
first-try routes) instead. That is the first time an area number moved work
rather than merely describing it afterwards — and it is the right use of a
model that, by its own admission, cannot tell a routable design from an
unroutable one at this margin. Predicting *risk* is enough to sequence work;
it is not enough to grant permission, and the distinction is the whole
discipline.

What this does not yet demonstrate: the cache is transparent by *test*
(lockstep, 596 RTL programs), not yet by the ISS-vs-ISS theorem the plan
calls for. Until that exists, "the cache changes no architectural result" is a
claim backed by the generated matrix rather than by a proof over it — which is
precisely the W5-deeper-half gap, met again from a new direction.

### Addendum: the cache measured the model back — and I misread it first

**The correction first, because it is the more useful half.** The initial
reading of this experiment was that the I-cache cost +3.8 points of the part
while synthesizer cells fell, "proving" that packing is not a constant and
calling that the cost model's biggest weakness. That was wrong, and wrong in
a specific, avoidable way: the new build was compared against a *utilization
figure recorded in the journal for a different build* rather than against a
rebuilt baseline. A controlled A/B — same wrapper, same seed, cache present
versus absent — says:

| | cells | sites | expansion | BRAM |
|---|---|---|---|---|
| no cache | 44 112 | 55 234 | 1.252× | 26 |
| with I$ | 43 999 | 55 129 | 1.253× | 46 |

The cache costs **essentially nothing in LUTs** (105 sites fewer, i.e. noise)
and 20 BRAMs. The W6 projection of roughly zero was *correct*. Packing is
near-constant across the pair. Both of the original conclusions evaporated
when the baseline was actually built.

The lesson is not about caches or packing. Hours earlier, this same session
wrote into `scripts/boot_sim.sh`'s header: *always run the known-good image
alongside; a result is evidence only when the baseline does not produce it* —
having just learned it from a simulation that "reproduced" a panic the
passing image also produced. Then the identical error was committed in the
area domain, against a number that merely *looked* authoritative because it
was written down in a journal. **A recorded number is not a baseline.** The
rule generalizes past simulation: any A/B needs both legs built, in area
exactly as in behaviour, and a measurement inherited from a different
configuration is a hypothesis wearing a measurement's clothes.

What survives from the original entry, and is worth keeping:

*A model earns trust by being wrong legibly* — and by being **checkable**.
The reason this correction took twenty minutes rather than shipping as
received wisdom is that capacity, closure, and the unit bridge are separate
fields with their own provenance: the claim "packing is not a constant" was
falsifiable by one controlled build, and it was falsified. Had it been folded
into a single fitted scalar, it would have been re-fitted into invisibility
and become a fact by repetition — which is precisely the failure the
provenance discipline exists to prevent, arriving from the inside this time.

*The rung still landed right.* The cache went onto the top the model said had
headroom, that top routed first try at 29.34 MHz, and all 20 banks landed in
block RAM (46 RAMB36, exactly 10 per core). The decision was right for the
right reason; only the post-hoc story about *why* was wrong, and stayed wrong
exactly as long as it took to build the other leg.

## The host was the capability system

The mini has had gates for months, and a selftest proving that a gate is the
only way a thread changes domain. It was true, and it was not §17. The gate
table was two 16-entry banks the host filled over BSCAN before the core
started; `MINI_GATE_CALL` indexed them combinationally. Nothing in the
guest's address space described a gate. If you had asked the machine "what
authority does gate 3 confer", the honest answer was "whatever the debugger
told me at boot, and I have no way to check".

That is the shape of the failure worth naming. The selftest was not weak —
it tested activation, restoration, depth-1 refusal, and the negative case
where a handle addressed to one domain must be unreachable from another.
Every one of those passed against state the host had installed. A test can
be rigorous about the *mechanism* and completely blind to *where the
mechanism's inputs came from*, and the second question is the whole of §17.
"Spec-encoded" is not a property of the instruction encoding alone; a machine
that executes the spec's opcodes over the host's private tables is running
half a specification.

The fix was small in the datapath — two states, a 16-byte descriptor, a root
pointer — and the interesting part was elsewhere. The activation funnels
(`tdom`, `tcont`, `tcdom`, `in_gate`) were all guarded by "in the execute
cycle", which was the right predicate as long as the answer was a
combinational bank read. With the descriptor two cycles away in DDR, that
predicate quietly became "record an activation whose target domain is not
yet known". Reading a structure instead of being handed one is not a local
change to the read: it moves the commit point, and every piece of state that
was implicitly timed to the old commit has to be re-timed with it. The
deletion is the part that makes the claim checkable — the banks, the two
commands, the selector register and both read helpers are gone, so there is
no longer a path by which an activation's domain can come from anywhere but
guest memory. A capability system you can still poke is one you have to be
trusted not to poke.

## What NT taught (2026-08-08): a parameter can be self-consistently wrong, and the real-workload rung has a hole exactly where scheduling lives

`NT` (the thread-slot count) was declared a parameter in §71g and dropped to
8 for a −17.8% area win. Every selftest passed at NT=8 — smp, preempt,
failstop, the lockstep, all green — and then the first real NetBSD boot on an
NT=8 bitstream panicked at the first kthread create it could not satisfy.
Two lessons for the intended shape, both about coverage rather than
derivation:

**1. Boundary behavior needs a property, not an example.** The selftests
spawn one or two threads; none fills the slot table to `NT-1` and checks that
the `NT`-th allocation is refused *and that the first `NT-1` all succeed*.
NT=8's failure (slot exhaustion — the boot needs a ~9th live thread and slot
8 does not exist) is invisible to any test that never approaches the
boundary, and §71g's own note that "at least one more constant is coupled"
is the same shape one level up: a `mod NT` that a 5-bit add did for free at
NT=32 is silently wrong at any smaller power of two, and no example test at
low occupancy exercises the wrap. The remedy is a generated property —
*for the design's `NT`, allocation is a bijection onto `[0,NT)` and refuses at
`NT`* — checked at every `NT` the design is emitted at, not a hand-written
spawn-a-thread example. A parameter whose only evidence is examples at one
value is a parameter in name only (the §71g reversion proved it the hard way;
this session proved the residue is a coverage hole, not a live datapath bug).

**2. The actual-image rung dies before the interesting phase.**
`boot_sim.sh` — the rung added after sel_cond to run the shipped image on the
emitted RTL — diverges at ~181k retires on the tb's fixed-latency DDR model
(the `subr_vmem` quantum assertion the real board does not hit). The rump
kernel creates its softint/housekeeping threads *after* that point, so the
one phase where an `NT`/scheduler bug manifests is unreachable in the faithful
simulator: `t_hw` (highest slot used) reads 0 because no thread is ever born
before the divergence. The ladder's real-workload rung is not just "shorter
than silicon" — it is missing a specific, load-bearing region (multi-thread
scheduling under a booting OS), and that region is exactly where this class of
bug lives. Closing it means a tb DDR model faithful enough to cross ~180k
retires, or a scheduling-stress workload that reaches high slot occupancy in
the faithful window — either way, the rung has to reach the phase before it can
witness the phase's bugs.

The operational upshot, in the same spirit as the ~55% routing ceiling being
promoted to a correctness input: `NT` is bounded below by the workload's peak
live-thread count (a *measured* quantity the ladder currently cannot produce
off-board) and above by the routing ceiling. Picking it is a
model-with-uncertainty decision (property 6), and the missing measurement is
the uncertainty. NT=16 is this session's choice — a power of two (the wrap
needs it) that gives ~16 slots for a boot that needs ~10, and routes the dual
at ~47% instead of NT=32's barely-closing 53%.

### The NT=32 fit (2026-08-08, later): the boot needs >16, so pay for it by deleting the one 64-bit-wide NT structure

NT=16 turned out to need MORE than ~16 slots: the dual boots at NT=32 but at
NT=16 it panics `pool->tp_refcnt == 0` (kern_threadpool.c:428) right after
`entropy: ready`. This was first suspected to be the §17 domain layer, but a
**non-domain image** (`LNP64_NO_DOMAINS=1`) hits the identical panic at NT=16 —
so it is the scheduler, not the guest: the boot's threadpool phase needs >16
concurrent workers, and NT=16 has no slot for them. The uncertainty the section
above named ("NT is bounded below by the workload's peak live-thread count, a
measured quantity the ladder cannot produce off-board") resolved on silicon:
the lower bound is >16, i.e. NT=32.

But NT=32 with the keyed futex-wake bank does not route (the wl variant hit
100% and failed to expand). The fix is not a smaller NT (too few slots) nor a
reseed gamble (the wrong strategy) — it is to REMOVE the one structure that
scales with NT at 64-bit width: `tfutex` (the per-slot wait key) and the
NT-parallel 64-bit comparator bank it feeds (the keyed EXT-4 wake). Everything
else per slot is 2-bit (`tstate`) or already a BRAM memory (`tpc`, `tdom`,
`tp_arr`, …), so it barely scales. Deleting `tfutex` reverts EXT-4 to an
**unkeyed** wake — every parked (FUTEX) thread wakes on any `FUTEX_WAKE`/
doorbell — which is spec-legal (a futex wake may be spurious but never missed;
every waiter re-checks and re-parks). The cost is a thundering herd per wake, a
performance trade the boot absorbs; the win is that 32 slots now cost ~like 16.
This is the same move as every other in this file — take the expensive thing
out of the wide/parallel part of the design — applied to the scheduler, and it
is the feature-abort the "most realistic dual we can FIT" brief authorised:
keyed-wake precision (an optimisation) traded for the slot count the boot
actually needs. `tstate` stays a register file (2-bit, cheap, read at every
index by the ready/free encoders and the unkeyed wake); it did not need to move
to memory. The thread CONTEXT was never the problem — it was already in BRAM.
