# NEXT STEPS — active plan as of 2026-07-28

Current state: T1–T9 are CLEAN, the generic emission theorem is proved, RTL
is externally corroborated, and R-MC is complete (sorry-free unbounded
whole-state lockstep from reset; all 25 retirement opcodes; closure is
exactly `propext`, `Classical.choice`, `Quot.sound`). The proof layer is not
the constraint. **Reproduction cost is**, and the active track is bounding it
per tier.

## The goal, re-set 2026-07-29 — dual-community acceptance

The session goal is now: **get the project to an overall shape that would be
simultaneously accepted by the Lean mathematical community and the hardware
community.** This is the Publication Readiness TODO (P1–P6, end of this
file) promoted from appendix to driver. The two communities' non-negotiables
are different and both are already itemized there:

- **Lean side (P1):** a sorry-free flagship theorem, an axiom closure of
  exactly `propext`/`Classical.choice`/`Quot.sound`, and an honest written
  trust story for the `implemented_by` twins and the release checkers. The
  single biggest gap is the four `Wip` sorries under `toProgram_denotes`
  (task #9). Everything else on the Lean side is hygiene, not mathematics.
- **Hardware side (P2/P3):** tool-validated output (iverilog + yosys already
  corroborate the three-port commit order), a credible second design through
  the documented path (tutorial run 1 done; stranger test pending), and
  honest cost/benchmark reporting (RELEASE_COST.md already is this).

Consequence: task #9 is the critical path and is active. The GateCall
campaign (#3) and serial-phase work (#4) improve the loop but block nobody's
acceptance; they proceed opportunistically.

### Task #9 findings, 2026-07-29 (before any proof text)

Empirical facts established by exhaustive testing (scratchpad scripts):

1. `balancedRope ((listChunks c leaves).map balancedRope) = balancedRope
   leaves` — **literal tree equality** — holds exactly when `c` is a power
   of two (tested c ∈ {1,2,4,8,16,32}, hundreds of lengths) and fails
   otherwise (c ∈ {3,5} fail from the second chunk on). The shipped
   `chunkLeaves = 16` qualifies, so the layout half of
   `toProgram_wireWellFormed` decomposes into: collapse lemma (needs the
   2^k hypothesis) + `balancedPath?`-vs-`balancedRope` path correctness
   (no restriction) + chunk-index arithmetic.
2. `toProgram_wireWellFormed` as stated is likely **unprovable without the
   `hreads` hypothesis**: `indexedRhsWellFormed`'s register branch requires
   every `.reg` operand to resolve in `program.regs` at the operand's
   intrinsic width — exactly `designReadsValidB`'s content, and not implied
   by `Compile.DesignWF` (which constrains writes only). Adding `hreads` to
   the statement is harmless; `toProgram_denotes` already carries it.
3. Wire numbering is free: `toIndexedWires` sets `number := index` via
   `zipIdx`, so the numbering premise of the layout lemma is by
   construction.

Proof order: layout lemmas (delegated, `Loom/Release/RopeLayout.lean`) →
`FlattenSt` consistency invariant → `wireWellFormed` → `wireMatches` →
`registerBehavior`/`memoryBehavior` (invariant + semantic layer).

### Task #9 progress, same day: wire graph DONE (commits 92e4827…93d9c1a)

`toProgram_wireMatches` and `toProgram_wireWellFormed` are **proved** —
out of `Wip`, sorry-free, closure exactly
propext/Classical.choice/Quot.sound — each under one kernel-reducible
Boolean hypothesis `moduleEmitOkB (Compile.compile d) = true` (decision
**D13**, `Loom/Hw/DESIGN.md`: the register/memory-read and
positive-width obligations no prior hypothesis implied). Acc8 passes the
Boolean by `#eval` in under a second; LNP64-µ needs a pointer-memoized
twin first (tree-walk DAG blowup, D12/D13 caveat). The proof stack:
`RopeLayout.lean` (balancedPath?/balancedRope correctness + the 2^k
collapse + evidence introducers), `FlattenWF.lean` (`FlattenSt.WF`
invariant, `flatten_spec`, `flattenModule_wf`, and a from-scratch
byte-level String bridge for `wireNumber? (wireName m) = some m`),
`ToProgramWellFormed.lean` (state equality with `toIndexedWires`,
shaped lookups, find? metadata transfer, the `indexedRhsWellFormed` and
`matchesRaw` bridges, final assembly).

**`toProgram_denotes` now has two open conjuncts, both semantic:**
`toProgram_registerBehavior` (the hard lemma) and
`toProgram_memoryBehavior`.

### Semantic-half design (worked out 2026-07-29, before proof text)

The conjuncts are *structural*, not evaluative: `RegisterBehaviorAt`'s
heart is `RawExprMatches program table (rules.foldl nextReg (.reg w
name)) root`, and `Compile.compile` builds each register's `next` as
exactly that fold — so the needed spec is `flatten_matches`: flatten
returns a name with `indexedExprMatches allWires table e (operandRef
name) = true` (the Boolean structural matcher), transported to
`RawExprMatches` by the already-proved `indexedExprMatches_raw` +
`toProgram_wireMatches`. Metadata conjuncts come from
`flattenRegs_meta`; `concrete.next = root.render` from operand
canonicality.

**The one real obstacle: CSE-hit soundness = single-node key
injectivity.** On a hit, the stored node must have the rhs the current
expression would have emitted; equal rendered keys must imply equal
structural `Rhs`. False for adversarial register names (`.ident "a + b"`
collides with `.bin .add "a" "b"`). Resolution, per the D12/D13 rule: a
**D14 identifier-discipline decidable check** (names used in `.reg`
leaves and memory names match `[A-Za-z_][A-Za-z0-9_]*`); under it,
`keyOf : Rhs → String` (the mirror of flatten's key construction) is
injective per node — canonical `n<k>` operand names are already
ident-shaped, so injectivity is over atomic tokens vs the 9 rendering
shapes (`x + y`, `m[a]`, `~x`, `$signed(x) < $signed(y)`, `x ? t : f`,
`x[hi:lo]`, `{{k{x[b]}}, x}`, `w'd v`, bare ident).

**RESOLVED 2026-07-29, same day (commits 903d740…67c75a2):
`toProgram_denotes` is PROVED — zero sorries in the Loom library, the
`Wip` namespace is gone, closure exactly
propext/Classical.choice/Quot.sound, `lake build Loom` clean.** Final
signature: four kernel-reducible Booleans (`moduleEmitOkB`,
`moduleMatchOkB`, `moduleNamesOkB`, `designReadsValidB`); `DesignWF`
turned out unneeded and was dropped. D14 recorded in
`Loom/Hw/DESIGN.md`. Acc8 passes all four Booleans by `#eval` in
seconds. What remains to *use* the theorem on LNP64-µ and retire the
68,028 CPU-s hybrid-registers phase (task #10): (1) kernel-reducible
checkers — measured 2026-07-29: `Symbolic.wireNumber?` does NOT
kernel-reduce (byte-String `drop`/`toNat?` get stuck under `decide`),
which blocks `moduleEmitOkB` AND quietly breaks D12's stated plan of
kernel-discharging `designReadsValidB`; `identTokenB`
(`String.toList`-recursive) DOES reduce, as do `designWFCheck`,
`moduleNamesOkB`, and `Compile.compile` itself on Acc8 (~1 s). Fix in
flight: `isWireLikeB` (toList-based) + one-direction soundness swapped
into `exprEmitOkB`'s reg arm; the same fix inside `SymbolicElaborate`
(for designReadsValidB) is deferred to an audit-tier rebuild window
since that file is imported by every generated certificate. (2) Measure
kernel discharge on LNP64-µ (DAG-blowup risk — kernel reduction may not
share let-bound subterm reductions; measure, don't assume).
MEASURED 2026-07-29: with `maxRecDepth 4000000`, **`moduleNamesOkB`
kernel-discharges on LNP64-µ** (within a 45 s file — no exponential
wall); `moduleEmitOkB` hit the default 200k-heartbeat elaboration
budget and `moduleMatchOkB` reported stuck — re-running isolated with
`maxHeartbeats 0` under a wall-clock cap to get true costs.
DIAGNOSED 2026-07-29 (bisection): the stuck constant is
`List.mergeSort` inside `Machines.Lnp64u.Hw.schedOrder`
(Core.lean:100) — well-founded recursion, kernel cannot whnf
`WellFounded.fix`/`Acc.rec` (minimal repro:
`[2,1,3].mergeSort (· ≤ ·) = [1,2,3]` fails `by decide`). Every
rule-body traversal sticks (`nextReg` folds, even
`numPorts → designTrace → portTrace`); names/outs pass since they
avoid rule bodies. VERIFIED discharge route: transport along the
existing `schedOrderRelease` — define `coreActR` with the concrete
schedule `[0,1,2,3]` inlined, prove `core Demo.sysManifest = coreR` by
`rw`, then `decide`; the previously-stuck mems section discharges in
31 s this way. Do NOT swap mergeSort for a structural sort design-side:
`RMCSched.lean` depends on `List.pairwise_mergeSort`/`mergeSort_perm`
at the general-manifest level.

Full-module measurement (post-transport): the checks are genuinely
compute-bound, not stuck — every sampled register chunk (0–4, 200–202,
500–502, 820–825) discharges; the full-module runs tree-walk the
DAG-shaped design like every reference walk does, extrapolating to
≈2 h wall and ~23 GB per Boolean on LNP64-µ. Strategic conclusion for
the release-path swap: **two tiers.** (i) Small designs (tutorial/Acc8
scale): `toProgram_denotes` + four `decide`s replaces the entire
certificate pipeline TODAY (seconds); this should become the documented
artifact path for new designs. **DONE 2026-07-29 (commit 8502557):**
`designReadsOkB` (kernel-reducible D12 form, `ReadsValidKernel.lean`)
became `toProgram_denotes`'s read hypothesis, and
`Machines/Tutorial/SatCounterArtifact.lean` proves the tutorial
design's full `ModuleBehavior` in 18 s by four `decide`s — closure
exactly the classical trio, zero certificates; TUTORIAL.md §6 points at
it as the copyable path. (ii) LNP64-µ: direct kernel discharge is
possible via the `coreR_eq` transport but at ~2 h × 23 GB per Boolean
it does not clearly beat the existing per-node pipeline (bounded
per-node kernel work exists precisely to avoid whole-design tree
walks); keep the pipeline for LNP64-µ until witness-based checking of
the Booleans (emit the flatten state as data, check per node — the
generic theorem's hypotheses restated as bounded certificates) is
built. FINAL MEASUREMENT 2026-07-29: full-module `by decide` on LNP64-µ is
**impractical even once unstuck** — under the `coreR_eq` transport,
`moduleMatchOkB` and `moduleEmitOkB` each ran 3 h 24 m CPU without
finishing (match ~80 GB RSS, emit ~36 GB; terminated before OOM). The
reference `compile` tree-walks the DAG-shaped design and the
issue-chain duplication (`payerE`/`eligE`) makes the trees enormous —
the same blowup that forced every `implemented_by` twin. Verdict
confirmed and hardened: LNP64-µ keeps the per-node certificate
pipeline; the future witness-based route should discharge the Boolean
hypotheses against the flattened-wire representation (which the release
machinery already rechecks per node) rather than kernel-normalizing
`compile`'s tree. The `coreR_eq` transport (rw [schedOrderRelease])
remains the necessary unsticking prefix for ANY lnp64u kernel goal that
touches rule bodies — record it wherever such a goal is first stated. Also
measured: all three Booleans discharge on Acc8 in 1.5 s total.
Hardware-side: new repeatable gate `scripts/corroborate_yosys.sh`
(wired into reproduce.sh) — all three shipped designs synthesize under
yosys 0.33: acc8 584 cells, lnp64u 181,055 cells, satcounter 4 cells,
2m45 total. (3) The
release-path phase swapping per-node certificates for parity + the four
Boolean facts, then re-measure the audit tier. The executed work plan, kept for the record:
(a) `keyOf` + `identOkB`/D14 + single-node injectivity (String-heavy,
    self-contained);
(b) shaped-evidence introducers for `RegisterBehaviorRopeFrom` (2-level
    shape: `balancedRope ((listChunks 128 entries).map .leaf)`) and the
    `MemoryBehaviorsFrom` analog — same pairStep machinery as E/F in
    RopeLayout.lean;
(c) `flatten_matches` — a KeyWF side invariant (cse entry ↦ stored rhs
    renders to that key AND is token-disciplined; separate structure, do
    NOT extend `FlattenSt.WF` and break its finished proofs) + induction
    like `flatten_spec`, parameterized by lookup-faithfulness of the
    FINAL rope (intermediate wires persist by Extends). ADDITIONAL
    hypothesis discovered 2026-07-29: `indexedExprMatches` accepts ONLY
    strictly-widening `sext` (stored `.sext` node, `inputWidth < w`) and
    non-narrowing `zext` — flatten's `.ident`/`.slice` normalizations
    for degenerate sext have no matcher case — so (c) carries a
    width-discipline Boolean (all sext strictly widening, all zext
    non-narrowing in the compiled module); both shipped machines
    evidently satisfy it (their per-node certificates use this matcher).
(d) assembly: registerBehavior (fold facts + RopeFrom introducer) and
    memoryBehavior (ports analogous via compile's mems; init images are
    pure data — `MemoryInitBlockBehavior` by construction + rope
    layout). Statements gain `hemit` + the D14 Boolean.

## The target, rebound 2026-07-28

The previous target was "a clean checkout builds the full end-to-end proof in
under 10 minutes on 32 cores". **That target was proved infeasible and has
been deliberately rebound.** It is recorded here rather than deleted so the
history reads as what it was.

The infeasibility argument is one line. Total CPU for a clean run is 125,683
CPU-s; at *perfect* 32x parallelism that is 3,928 s (65.5 min), still 6.5x a
600 s target, with every scheduling question assumed away. Retiring the whole
`hybrid registers` phase via section B leaves 1,814 s (30 min), still 3.0x
over, before R-MC's 200-360 s modules are counted. It is a statement about
total work, not about how work is arranged, so no batching, sharding, worker
count, or scheduler can cross it. Full derivation in `RELEASE_COST.md`.

The replacement target:

> From a warm cache, any single-edit re-verification completes in under 10
> minutes; a clean-checkout audit run completes overnight with kernel-only
> checking and its full cost recorded per release; and the end-to-end theorem
> is stated verbatim with its hard lemma as a named `sorry`.

This is not a lowered bar; it is the bar attached to the thing it was always
measuring. A wall-clock budget is a promise about *someone waiting*, and
nobody waits on the audit tier -- it is bounded by the trust posture
(kernel-only reduction is the point, not an inefficiency) and runs offline.
The 10-minute number was always implicitly a promise about the edit-verify
loop, and section D's CI tier is where that loop lives.

Two conditions keep the rebinding honest rather than convenient:

1. **The audit tier gets a tracked cost, not no cost.** Report total
   CPU-seconds and wall per release under `.lake/release-metrics/`, against a
   soft practicality bound of **<= 4 h wall on a 32-core host**. An auditor
   re-running the certificate on their own hardware is still a user, just a
   patient one. Unbounded is not the same as untargeted.
2. **The redefinition lives where the old target was** -- this section --
   with the floor argument beside it.

### The CI-tier gate, stated precisely

    max over single-edit classes of (recheck cost from a warm cache) <= 600 s

That is the worst-case cost of one leaf plus its join path to the root. It is
a *max*, not a mean: a single edit class that busts it busts the gate. Running
today's measured numbers against that definition produces the work list
below mechanically.

| item | measured | verdict against the gate |
| --- | ---: | --- |
| `SemanticMems` | 832 s, parallelism 1.0 | **violates on its own** |
| R-MC modules | 200-360 s each | any chain of two busts it |
| `hybrid registers` leaf | ~3 s/leaf at 29.4x | passes; joins are the risk |

Note what the rebinding does *not* license. Pipeline-wide batching is still
dead -- the floor analysis killed it and rebinding does not revive it. What
comes back into scope is decomposition **along worst-case single-edit paths
only**, which is a much smaller and better-targeted programme.

## The goal fork — decided as sequenced, 2026-07-28

The project's stated goal is a Lean language/library that makes it easy to
describe hardware, compile it to Verilog, and write your own proofs about
your own designs. A 2026-07-28 assessment found the center of gravity has
drifted from that library goal toward one deeply-verified artifact (LNP64-µ
and its publication path). **That drift is a fork, not a footnote: it is a
strategic decision being made by default, and the two goals order the work
differently.**

- **Artifact-first** (LNP64-µ, publication): Task 0 dominates everything;
  the tutorial is marketing; R-MC recipe promotion is optional; the
  credibility of one deeply-verified core is the product.
- **Library-first**: the tutorial and a second user are upstream of further
  investment, because they test whether the foundation is right before more
  is built on it.

**Decision: sequenced, with a written trigger.** LNP64-µ is what makes
anyone believe the library matters — no one adopts a hardware verification
framework on the strength of Acc8. So artifact-first now, *and*:

> **Trigger: when Task 0's end-to-end statement lands (all three done
> criteria in §Sequencing below), or at publication submission, whichever
> comes first, the next quarter's priority flips to user-facing work** —
> tutorial, docs, and the user test below — before further artifact
> optimization is taken up.

The trigger is the load-bearing part. Sequencing without a trigger is how
the artifact absorbs everything forever, which is what gravity does.

### Leg 3 scoped: two promises, not one

"Relatively easy to write your own proofs" currently covers two products
with a ~100x difficulty gap. Scope the claim instead of treating the gap as
a deficiency to close:

- **v1 promise — invariant transport.** "State a spec invariant, get it on
  every reachable RTL state for free." This is real, generic, already
  proved (`VerifiedSymbolicArtifact.invariants`), and is the 80% case.
  Deliverable *now*; the tutorial and README should promise exactly this.
- **v2 goal, gated on the fork — refinement to an ISS.** The R-MC
  development proves it is *possible*; nothing yet makes it *easy*. Document
  it as expert territory, with the R-MC recipes (§1) as the evidence base.
  **Recipe promotion into library abstractions is expensive and only worth
  it if refinement enters the promise** — that call is exactly the fork
  decision above, so recipe promotion waits on the post-trigger review
  rather than being open-ended debt.

### "Easy" gets a falsification protocol, not just a tutorial

A tutorial written by the author is still n=1 — it tests whether the author
can explain, not whether a stranger can succeed. The experiment is cheap and
is specified like one:

> One person who has never seen the repo, given the tutorial and a clean
> checkout, builds a two-register machine with one invariant, down to
> emitted Verilog with the invariant transported — recording wall-time and
> every point at which they needed help.

Run it two or three times, different people. **Every intervention is a bug
report against the library or the docs.** Until this has run once, every
"easy" in the goal statement is an unfalsified hypothesis. Cost: about a
day of someone else's time; highest information-per-hour item on the list.

### Adjusted ordering

1. **Task 0 — unchanged, the main event**, now upgraded from *planned* to
   **confirmed feasible**: the 2026-07-28 architecture mapping established
   that the printer's SSA flattening is deterministic hash-consing on pure
   data — `n<k>` names are allocation-order indices, CSE keys on
   `(width, rendered RHS)`, traversal order is fixed (all `reg.next`, then
   memory ports in order, then outputs) — so the Python witness layer is
   reproducible, and therefore replaceable, inside Lean.
2. **Tutorial + user test run in parallel with Task 0, not after it.** They
   compete for neither the same skills nor the same part of the codebase,
   and the user test may surface EDSL problems that are cheaper to fix
   before the compiler-through-rendering proof calcifies interfaces.
3. **CI-tier cache** stays where the ratified CI-tier target put it (above).
4. **Recipe promotion waits on the fork's post-trigger scope decision.**

## 0. The target statement — write this before anything else

Everything below is scoped by one sentence, so the sentence goes first. What
`verifiedReleases` proves today, per artifact, is `VerifiedSymbolicArtifact`
(`Loom/Release/SymbolicVerified.lean:24`), which bundles exactly four fields:

```lean
exactBytes  : program.renderTree.flattenBytes = disk.flattenBytes
denotation  : Symbolic.ModuleBehavior design program indexeds table
                registers memories outputs
refinement  : Simulation spec (Compile.compile design).toTSys.reachablePart
invariants  : ∀ {P}, spec.Invariant P →
                (Compile.compile design).toTSys.Invariant (P ∘ refinement.abs)
```

Read those four fields carefully and the architecture becomes legible.
**There are two independent routes out of `design`, and they never meet.**

- `refinement` and `invariants` go through `Compile.compile design`, the
  *verified* compiler, discharged generically by `compile_cycle` and
  `simulation_of_tsys_eq`.
- `denotation` relates the concrete `program` to `design` **directly**. Not
  to `Compile.compile design`. It is a second, independent semantic account
  of the shipped artifact.

The two routes share only the word `design`. Consequently there is today
**no theorem anywhere in the repo of the form `program = render (compile
design)`**, and no function to state it with: `Loom/Release/SSA.lean` has
`Program.elaborate : Program → Option Module` — which runs the *opposite*
direction — and no `Design → SSA.Program` exists at all. The concrete
`Program` is produced outside Lean by `scripts/gen_release_witness.py` and
then validated after the fact.

So the honest answer to "if the compiler is verified, why do the certificates
exist?" is neither pure historical accident nor a gap in the compiler proof.
It is: **the shipped artifact is not defined as the compiler's output, so its
semantics must be re-established from scratch.** That re-establishment is the
per-node `ModuleBehavior` obligation, and it is the expensive thing.

### The target

```lean
-- does not exist yet; writing it is task 0
def Design.toProgram (d : Design) : SSA.Program

theorem toProgram_denotes (d : Design) (wf : DesignWF d) :
    Symbolic.ModuleBehavior d (d.toProgram) (indexedsOf d) (tableOf d)
      (registersOf d) (memoriesOf d) (outputsOf d)
```

With that, per-design work collapses from a per-node re-derivation to a
single data equality `program = d.toProgram`, checkable reflectively, plus
the existing `exactBytes`. **Every section below should name which field of
`VerifiedSymbolicArtifact` it discharges.**

### What this statement deliberately does not say

It says nothing about Verilog. There is no `⟦_⟧_verilog` in this repo and
there should be no pretence of one: `CONCRETE_SSA_BOUNDARY.md` states the
Yosys adequacy assumption explicitly, and the Lean theorem ends at exact
bytes plus the formal denotation. Any "end-to-end" statement that quantifies
over Verilog semantics would be claiming a theorem the project does not have.

### Which obligations survive B

| field | expensive today | retired by B? |
| --- | --- | --- |
| `denotation` | **yes** — the per-node certificate pipeline | **retired**: becomes `program = d.toProgram` |
| `exactBytes` | no — a rope/byte equality | survives, already cheap |
| `refinement` | **yes** — R-MC, 200–360 s modules | **survives**: per-machine proof, untouched by B |
| `invariants` | no — generic transport | survives, already generic |

This table is the B-versus-C decision. B retires the certificate pipeline;
it does not touch R-MC. So C's batching and log-depth work is optimization of
infrastructure headed for deletion *except* where it applies to R-MC, which
survives B regardless.

## Sequencing: B and C are alternatives, not siblings

1. **Task 0** — write `Design.toProgram` and the `toProgram_denotes`
   statement, and identify the hard lemma. If nobody can write that
   signature, nothing below is well-posed.

   *Done* means all three of these, not a prose account of any of them:

   1. the `Design.toProgram` signature typechecks;
   2. the end-to-end theorem statement typechecks with `sorry`;
   3. the hard lemma is a **named, stated `sorry`** in the file — a
      declaration with a full type, not a comment describing one.

   Timebox it to two weeks. The failure mode is an open-ended formalisation
   wander, and "the statement could not be written inside the box" is itself
   a finding worth having: it would mean the artifact/compiler gap is not
   expressible without first changing one of the two representations.

   *Feasibility confirmed 2026-07-28* (see "Adjusted ordering" above): the
   printer's SSA flattening is deterministic hash-consing on pure data, so
   `Design.toProgram` can reproduce the shipped program exactly — including
   the `n<k>` wire numbering — with no pointer identity or IO involved. The
   two-week box now bounds the *proof statement* risk, not representation
   risk. Landing it also fires the goal-fork trigger above.

   *Proof progress 2026-07-29 (commit `2724308`):* 7 of the 12
   `ModuleBehavior` conjuncts are proved outright (name, all five counts,
   and the complete output conjunct, on sorry-free rope/flattener
   infrastructure in `ToProgramLemmas.lean`). Five named `Wip` sorries
   remain: the two hard ones (register/memory behavior — the actual
   Section B content), the wire-table pair (needs a `FlattenSt`
   numbering/CSE invariant), and `toProgram_readsValid`, which the work
   revealed is **not derivable from `Compile.DesignWF`** — `DesignWF`
   constrains writes only, while `DesignReadsValid` needs read-side
   declaration discipline plus `wireNumber?`-freeness of register names.
   The theorem hypothesis must be strengthened (a decidable
   `designReadsValidB` alongside `designWFCheck`); decide this before
   attacking the hard pair, because it changes their statements too.

   **DONE 2026-07-28, same day (commit `82e0081`).** All three criteria met
   and exceeded: `Design.toProgram` exists (`Loom/Release/ToProgram.lean`)
   and does not merely typecheck — `d.toProgram == program` was *measured
   true on both artifacts*, every field, including all 179,711 LNP64-µ
   wires, and the comparison is now a release phase (`toProgram parity
   gate`) so drift fails the build. `toProgram_denotes` typechecks with
   `sorry` (`Loom/Release/ToProgramDenotes.lean`), and the hard lemma is
   the named, fully-typed `toProgram_registerBehavior`: every register root
   of the constructed witness denotes the verified compilation — the
   once-for-all form of the 825 generated register theorems. The underlying
   induction (a flatten-soundness invariant over the CSE environment) is
   described in that file's header. **The goal-fork trigger has fired**:
   user-facing work (tutorial + user test) is now co-priority with proving
   the stated lemmas.
2. **A** (an afternoon) and a **timeboxed B feasibility spike** (two weeks:
   a rendering-correctness skeleton with the hard lemma isolated and its
   difficulty assessed) run together.
3. **C proceeds only if** B stalls, B's timeline exceeds a release deadline,
   or for the obligation families the table above marks as surviving B. The
   R-MC half of C is unconditional — those costs exist either way.

### B's fallback ladder

B needs a kill condition and a degraded mode, not just a target.

- **Best** — generic rendering correctness (`toProgram_denotes` above). Zero
  per-design denotation cost, forever.
- **Fallback** — per-design reflective equality: ship `program`, check
  `program = d.toProgram` by kernel reduction over compact data. Still
  per-design, but constant-size proof terms and one reduction instead of a
  per-node tree. The in-repo footprint-check precedent (10m48s → 5m10s,
  ~11 MiB → <1 MiB) suggests this is tractable; the whole-plan
  counter-example (37 s but 6.94 GiB RSS; monolithic `rfl` killed at 99 s)
  says profile the decoder's reduction behaviour before committing.
- **Floor** — today's certificate pipeline, made survivable by C.

Descending the ladder is a legitimate outcome, and each rung is strictly
cheaper than the one below it.

## The reframe that drives this plan

The project already owns a CompCert-shaped compiler correctness theorem.
`Loom/Hw/CompileCorrect.lean` proves

```lean
theorem compile_cycle (d : Design) (wf : DesignWF d) (state : Loom.Hw.St) :
    forgetSt ((compile d).cycle (convSt state)) = d.cycle state
```

universally quantified over every design and state, sorry-free, with
`simulation_of_tsys_eq` lifting it to trace simulation and
`designWFCheck_sound` reducing the side condition to a Boolean check.

Yet every release run still pays a large per-design proof cost, because — as
§0 establishes from the four fields of `VerifiedSymbolicArtifact` — the
shipped artifact is not defined as that compiler's output. The design is
compiled by a verified function *and*, separately, a concrete program is
produced outside Lean and validated against the same design. Two routes, one
verified and one validated, meeting only at `design`.

So the status quo is *translation validation running alongside an
already-verified compiler* — paying the per-run cost of an unverified-compiler
architecture while holding the verified-compiler theorem. That is the most
expensive available position, and closing it needs a definition
(`Design.toProgram`) that does not exist yet rather than a new research
result.

Everything below follows from joining those two routes and from decoupling
*compiling* (milliseconds) from *auditing* (offline, incremental).

## A. Feasibility — MEASURED 2026-07-28

**W = 95,786 CPU-s (26.6 CPU-h) against a 19,200 CPU-s budget: 5.9x over.**
A clean run is about 160 minutes wall on 32 cores. The pipeline completes;
the target is not reachable by restructuring it. Full numbers, the serial
inventory, and the defect list are in `RELEASE_COST.md`.

Three consequences, in order of how much they change the plan:

1. **Section C's batching is a 9% item, not the lever.** Measured
   per-process toll is 8,920 CPU-s of 104,706 observed. The earlier estimate
   in this file and in `RELEASE_COST.md` -- roughly 21,000 CPU-s, more than
   the whole budget -- was wrong: it extrapolated from a single module's
   import cost and counted 4,575 modules that are now deleted. Batch where
   it is cheap; do not build a programme around it.
2. **Section B is the only route.** 70% of W is `hybrid registers`
   (67,646 CPU-s), which is exactly the per-node `denotation` re-derivation
   that `Design.toProgram` + `toProgram_denotes` replaces with one data
   equality. This is the "unreachable *without B*" case the footnote below
   anticipated, not "unreachable".
3. **The serial phases are a separate, smaller problem.** About 3,000 s of
   wall clock runs at parallelism ~1.0 (semantic memories 846 s, axiom
   closure 698 s, port certificate generation 504 s, semantic reads 396 s,
   semantic actions and hybrid core shape 201 s each, ActionCert 161 s).
   That alone exceeds ten minutes. Section C's log-depth-tree work applies
   here and is worth doing even after B, because these survive it.

### The floor calculation (2026-07-28) — read this one first

Total CPU for the authoritative clean run is 125,683 CPU-s. At *perfect* 32x
parallelism — no serial phases, no process toll, optimal scheduler — that is
**3,928 s (65.5 min), still 6.5x the 600 s target**. Retiring the whole
`hybrid registers` phase via B leaves 58,037 CPU-s, i.e. **1,814 s (30 min),
still 3.0x over**, before R-MC's 200-360 s modules are considered.

This subsumes the `W` argument below and is harder to argue with, because it
assumes away every scheduling question. The target is unreachable for the
audit tier **with B as well as without it**. See `RELEASE_COST.md`, "The
perfect-parallelism floor settles the 10-minute question". Attach the budget
to the CI tier (§D) or it is measuring the wrong thing.

### B is necessary but arithmetically insufficient

Run the residual before starting, so this is not rediscovered afterwards.
B retires about 70% of W, so what remains is

    0.30 x 95,786 = 28,700 CPU-s  ~ 1.5x the 19,200 CPU-s budget

at *perfect* parallelism, and that ignores the R-MC critical path, whose
2,308 s of wall clock is by itself 3.8x the ten-minute target. **No
combination of B and C reaches ten minutes for the whole pipeline.**

### Which tier owns the budget — DECIDED 2026-07-28

The CI tier does. The tiered model in section D always answered this; the
floor analysis removed the last excuse not to apply it.

- **tool path** (compile, inherit correctness from the once-proved theorem):
  seconds. `lake exe emit` is already 11-15 s. Needs no budget.
- **CI tier** (incremental checking against a content-addressed cache):
  **owns the 600 s budget**, under the max-over-single-edit-classes gate
  stated at the top of this file.
- **audit tier** (full cold re-derivation): the residual CPU plus R-MC.
  Bounded by the trust posture, run offline, and tracked against a soft
  <= 4 h wall practicality bound rather than left unmeasured.

A "17.4x miss" was only ever a miss because the budget was attached to the
audit tier, which is the one tier where a wall-clock target was never the
right instrument.

Two cheap wins are available now and independent of B:

- **DONE 2026-07-28.** `port certificate generation` spent 504 s to produce
  one imported batch, because the LNP64-u path ran all of `CertGen` for its
  memory-port family while the other three families it synthesises have no
  importers. `synthesizeMemsCertRuntime` +
  `indexedPortDeclarationBatchesOfMems` synthesize `cert.mems` alone:
  **506 s -> 18.1 s**, with a byte-identical compiled batch.
- The R-MC prerequisite phase runs 2,317 s at parallelism 2.7. That is a
  critical-path problem inside the proof modules, it is untouched by B, and
  it is the reason a sub-10-minute target would still be hard even if every
  certificate obligation vanished.

### Method, retained for the next measurement

Compute `W`: total CPU-seconds of actual kernel checking, with per-process
overhead removed. `scripts/measure_check_cost.py` does this from a run's
phase CSV by compiling, for each module family, a probe with that family's
exact import block and no declarations; the probe's CPU time is that family's
toll, and `W_family = observed_cpu - count * toll`.

- `W` comfortably under budget → the wall-clock target is engineering, and
  sections B–D are the work.
- `W` above budget → no batching or scheduling change reaches the target.
  Either the budget or the trust posture has to move; decide deliberately
  rather than after months of sharding.

`W` measures the cost of the *translation validation*, not of the trust
posture. Section B is what reduces it.

**Interpret `W` per tier.** `W` is defined over today's pipeline, so it is
the feasibility number for *the pipeline as it stands*. If B succeeds, the
`denotation` obligations that dominate `W` are retired outright, and the
residual `W` describes only the audit tier (§D) plus the R-MC cost that
survives B. Measure it anyway — it is an afternoon, and it is the only way to
know whether the floor is already above budget — but do not read a
`W`-exceeds-budget verdict as "the target is impossible". Read it as "the
target is impossible *without B*".

## B. Close the compiler proof through the rendering stage

The main event. Replace per-node re-derivation with one certified bridge from
the materialized program to `compile d`, so per-run work becomes a single
reflective equality over compact data.

1. one source-design-to-plan snapshot certificate — the only step permitted
   to normalize the source design, once per release, never per register or
   per batch;
2. linear structural checking of the compact snapshot against SSA;
3. bounded composition plus the existing exact artifact binding.

Make every obligation reflective (`check cert = true` by kernel reduction) so
the stored proof term is constant-size and cost moves from term construction
and serialization into reduction. Encode certificate data as compact literals
with a verified decoder rather than as constructor applications.

Precedent, in-repo: switching from explicit `NoRegWrite` proof trees to a
structural Boolean footprint check cut a full-size leaf from 10m48s to
5m10s and its `.olean` from ~11 MiB to under 1 MiB. Counter-precedent, also
in-repo: the whole-plan probe reduced to `true = true` in 37 s but at
6.94 GiB RSS, and a monolithic `rfl` variant was killed at 99 s. **Profile
the decoder's reduction behaviour before committing**, or serialization cost
is merely traded for kernel-reduction cost.

## C. Stop using the module system as the scheduler

Measured on the 2026-07-27 clean run: leaf checking parallelizes at 25–30x
on 32 cores, so the batch phases are healthy. The cost has concentrated in
per-process overhead and in serial singletons.

1. **Batch obligations into memory-sized modules.** Thousands of tiny
   modules, each `lean -j 1` with `set_option Elab.async false`, buy across
   processes the parallelism Lean would give for free within one. At ~1.3 s
   toll per process, 16k modules is ~21,000 CPU-s of pure overhead — more
   than a 10-minute/32-core budget before any obligation is checked.
   Batching to ~300 modules would cut that to ~400 CPU-s.
   **Constraint that shapes the whole design:** async declarations share a
   process, and R-MC modules already peak at 8–16 GiB alone. Batch size must
   be set per family by memory profile, not globally. Note also that
   `KernelDecide.lean` and `SymbolicDecide.lean` set `Elab.async false`
   internally around auxiliary-lemma creation — establish whether the custom
   elaborators depend on it before re-enabling anything.

2. **Make every composition point a log-depth tree.** No single declaration
   may do work proportional to the whole design. Current violations, from the
   2026-07-27 run: `ActionCert` at 161 s on one core with 31 idle; the render
   and indexed roots at ~39 s and ~37 s each; R-MC modules at 200–360 s. Each
   combiner should merge exactly two children so the critical path is
   `log2(n) * max-node`, not `n * node`. Where a join must genuinely traverse
   everything, restructure the *statement* into an associative fold whose
   intermediate lemmas are the tree nodes.

3. **Schedule and track the critical path.** Once joins are trees, wall-clock
   is set by the longest chain, not average parallelism. Emit the dependency
   DAG with per-node costs from the previous run and schedule longest-path
   first. Report **critical-path seconds** as the headline metric.

## C2. R-MC — independent of B, and it busts any budget on its own

Measured cold: **2,308 s wall at parallelism 2.7** on 32 cores, with
individual modules at 200-360 s. That is 3.8x the ten-minute target from one
phase, and section B does not touch it: B retires `denotation`, while R-MC
discharges `refinement`.

**Classification (proposed, confirm before spending on it).** R-MC is
*audit-tier and development-tier, not tool-path*. The tool path is
`lake exe emit` plus the generic `compile_cycle`; it never needs R-MC.
`verifiedReleases` does, because the bundle asserts refinement of the
shipped artifact, so a release re-derivation pays it. It is also a
development cost: any edit under `Machines/` re-triggers the chain, which is
what makes 2,308 s at 2.7x painful day to day rather than merely offline.

**First measured cut (2026-07-29).** The phase's wall clock IS its critical
path: 2,267 s of the 2,308 s, computed from clean-run module times over the
import DAG (`scripts/`-free one-off; method: longest path with per-module
weights from the `audit-clean-release` log). One decoupling landed:
`RMCRetireGateReturn` imported `RMCRetireGateCallSuccess` while using
nothing from the call side, serializing the 180 s return chain behind the
880 s call chain — re-pointed to its real dependency, path 2,267 → 2,152 s.
Two further hoists landed the same day: `RMCRetireGateShared` (the
retirement-base transfer glue out of `RMCRetireGateCallSuccess`, freeing
the gate-return chain and the revoke arm) and `RMCRetireCapShared` (the
capability-install datapath out of `RMCRetireDup`/`Move`/`Map`, taking all
three off the spine). **Measured path: 2,267 → 1,764 s (−22%)**, with the
audit-tier phase wall expected to follow at the next clean run. The spine
is now `...Alu→Branch→Sw→Rgn→CapShared→Drop→gate chain`, and the remaining
concentration is the GateCall sub-chain — `RMCRetireGateCall` 371 s +
`RMCRetireGateCallSuccess` 338 s + `RMCRetireGateCallArm` 147 s = 856 s of
the remaining 1,764 — plus `RMCIssue` 256 s and `RMCHalt` 230 s on the
trunk. Those are intra-module costs, which is where the splitting
prescriptions below take over; the cheap import-graph cuts are exhausted.

**GateCall campaign done-condition (set 2026-07-29, before starting):**
the worst single-edit warm-cache path through the GateCall sub-chain must
come under the 600 s CI-tier gate, which given the rest of its path means
**the GateCall+GateCallArm+GateCallSuccess chain lands at ~300–400 s**
(from 856 s). Sequencing: run the `Elab.async` probe on the real modules
*first* — if `kernel_decide`'s async-disable (or a chain of intra-file
dependencies) is why these files elaborate serially, the campaign is
"split into declarations" (cheap); only if parallel elaboration is
unrecoverable is it "split into files" (expensive). Measure
wall-vs-CPU on `RMCRetireGateCall` before touching anything.

*Probe result (measured 2026-07-29):* `RMCRetireGateCall` compiles at
**146% parallelism** (370 s wall, 536 s CPU). Async elaboration is already
active; the file is bound by its internal proof-dependency chain, not by a
disabled flag. Consequence: declaration-level or file-level splitting alone
cannot beat the chain — the campaign must reduce the chain itself.

*Profile result (same day, `lean --profile`):* the cost is **not** kernel
checking. Of 536 CPU-s: **375 s is `exact` tactic elaboration across 45
uses**, 49.5 s type checking, 37.9 s `change` (defeq conversion on large
goals), everything else noise. This is the RELEASE_COST "elaboration
re-reduces large concrete terms" pathology inside tactic blocks:
instantiating shared datapath lemmas at concrete domains forces whnf of
design-sized implicit arguments. The campaign's first step is therefore
**name attribution** (which declarations own the heavy `exact`s — the
category profile does not say), then per-site treatment: hoist the
repeated concrete instantiations into named intermediate lemmas (stated
once, elaborated once) or replace `exact`-with-huge-unification by `refine`
with explicit arguments. Expect the same shape in `GateCallSuccess`
(338 s), `RMCIssue` (256 s), `RMCHalt` (230 s); re-profile each before
working on it.

The remedy is the section C prescriptions applied *here*, where they are
alive even though they are a 9% item for the certificate pipeline:

1. split the 200-360 s declarations into independently checkable lemmas;
2. make the composition points log-depth rather than linear folds;
3. establish whether `Elab.async` can be enabled for these modules --
   `KernelDecide.lean` and `SymbolicDecide.lean` disable it around
   auxiliary-lemma creation, so this needs checking before it is assumed.

Parallelism 2.7 on a 32-core host means roughly 90% of the machine is idle
through the longest phase of the build. That is the largest purely
structural inefficiency measured anywhere in this project.

## D. Tier by who is waiting

None of the existing kernel-checked work is wasted; it stops being *the tool*
and becomes *the tool's audit trail*.

- **Dev loop (seconds).** Compile only, plus cheap structural checks. No
  proofs. `lake exe emit` already does this — 11 s on a clean tree. Ship
  `compile` and `certify` as separate commands; this is packaging, not
  architecture. Determinism is what makes tiering honest: the RTL from this
  mode must be byte-identical to the proved mode's.
- **CI (minutes).** Incremental certificate checking against a
  content-addressed proof cache. The DAG-cut structure already delineates
  dependencies; `compile_batch` is already a staleness checker keyed on
  mtime. Re-keying it on input content hashes is a smaller change than it
  sounds and also removes the "clean run silently depended on stale objects"
  class of bug.
- **Release/audit (offline).** The full kernel-checked run, asynchronous to
  use: ship the Verilog with a certificate hash and let the proof publish
  behind it, like a reproducible-build attestation.

## E. Decide the TCB question per tier, in writing

Rule 1 bans `native_decide` repo-wide and `Tools/Audit.lean` enforces it
mechanically (any closure containing `Lean.ofReduceBool` or
`Lean.trustCompiler` fails the build). That is an all-or-nothing policy.
Tiering makes the question newly answerable per tier — is Lean's compiler
acceptable in the trust base for the dev tier, for CI, never? Write the
answer as an amendment to `TRUST.md` so the ban and its scope stay in one
place. If the answer is "never, at any tier", then accept that verification
is an offline audit product and say so plainly in `REPRODUCING.md`.

## F. Accounting that survives relocation

Every optimization so far has moved cost across a layer boundary where it
stopped resembling the same problem: per-register traversal became
per-consumer deserialization; an elaboration-sharing refactor in `SysOps`
became broken R-MC proofs. Per commit, record **total CPU-seconds**, **total
bytes serialized**, and **critical-path seconds**. A change that improves
wall-clock while increasing total CPU or bytes is relocating cost, and CI
should say so out loud.

`scripts/phase_timing.sh` supplies the first and third today: every phase
appends `started_utc,scope,label,wall_seconds,cpu_seconds,parallelism`, and
`parallelism = cpu/wall` separates genuinely serial phases from badly
scheduled ones.

### Working rules earned the hard way on 2026-07-28

Each of these is a guard against a failure that actually happened, with its
cost attached. They are cheap to follow and were expensive to omit.

- **Trace to the data source on the second occurrence.** The first time a
  symptom appears, fixing it locally is reasonable. The *second* time the
  same symptom appears, stop and find the source that generates the
  disagreeing values before committing anything further. The
  `namedWire`/`wire` spelling took eight commits, two of which were
  self-inflicted regressions, because each fix addressed the consumer in
  front of it; the actual fault was one line in `gen_release_witness.py`
  emitting the root wire table in the other spelling.
- **Liveness means artifact progress, never process names.** A `pgrep -f`
  pattern matched the monitoring command's own arguments and reported a
  build that had been dead for five hours as running. Check log growth,
  `.olean` mtimes, or a recorded PID with `kill -0` -- never a name match
  that can find itself.
- **Every number in a planning document carries provenance.** Tag figures
  `measured @ <date/commit>` or `estimated`. Two numbers in these documents
  were quoted as evidence for architectural decisions and were both wrong
  when finally measured: the import toll (~21,000 CPU-s claimed, 8,920
  measured) and the axiom-closure walk (~24 min recorded, 649 s measured).
  Provenance tagging catches that at citation time rather than after a
  conclusion has been built on it.

## G. Standing hygiene

Reproducibility defects hide in warm trees. Four surfaced in one clean run on
2026-07-27 — an undocumented `ripgrep` dependency, a self-test fixture that
had drifted from its checker, an unnamed lake prerequisite, and R-MC proofs
broken by a semantics refactor. `scripts/ci.sh` does build R-MC transitively
(`Machines.lean` → `Ledger`/`DemoWitness` → `RMC`), so running it before
committing would have caught the last one. Run a wiped-tree build on a
schedule, not only before a release.

The remaining publication gates in §P1–§P6 below are unchanged and still
apply. Section 1 is retained as the completed proof-engineering record. See
`STATUS.md` for the audited current state and chronological history.

## Historical stopping point — 2026-07-04

The recovery loop is over. The active R-MC file now builds from current
source with the generated reset helpers wired in:

- `NEXTSTEPS.md` was reframed and committed as `83d09cc`.
- The source/docs/scripts checkpoint after the reset work was committed as
  `47762aa`.
- `Machines/Lnp64u/Theorems/RMC.lean` imports
  `RMCResetDom.lean` and proves `absDom_reset`, `abs_reset`, and
  `coupled_reset` without sorries.
- The generated helper targets `Machines.Lnp64u.Theorems.RMCResetCanon`
  and `Machines.Lnp64u.Theorems.RMCResetDom` build.
- `lake build Machines.Lnp64u.Theorems.RMC` succeeds; the only remaining
  declaration using `sorry` is `square` (2026-07-05: `coupled_step`
  proved via the new frame layer `RMCFrames.lean` and the kind-canon
  checker `RMCCanon.lean`).
- `lake exe audit` passes; `absDom_reset`, `abs_reset`, and
  `coupled_reset` are CLEAN, while downstream R-MC transport theorems are
  STATED only through `square`/`coupled_step`.

Immediate next step (2026-07-14, evening): **15 of 25 retirement op
arms are proven.** The retirement infrastructure is complete and landed:

- Dispatch skeleton (`RMCRetire.lean`): branch selection, register and
  memory faces, first-match per-op fold selection + illegal fallthrough.
- Proof-forced `Coupled` clause `r0_zero` (`RMCZero.lean`): the spec
  hardwires architectural `r0` reads to 0; a `ZeroWritesAll` kernel
  checker pins `dreg d 0`/`gsreg g 0` at zero across every rule
  (gate_call save and gate_return restore stay inside the zero family).
  `coupled_reset`/`coupled_step` extended; `readReg_eval` bridges the
  register-file mux to the spec's architectural read.
- Mover quiescence generalized to `Inert σ` (`RMCMover.lean`):
  derivable from non-retiring cycles (old arms unchanged) or from
  retiring a Mover-benign op (`Inert.of_benign`, opcode-driven).
- Shared glue: `square_retire_benign` (full refill/Mover/tick assembly,
  `RMCRetireBase.lean`; the muxed port-0 commit proven disabled via a
  memInert kernel walk), `square_retire_setReg` + the general
  `square_retire_domShape` (`RMCRetireAlu.lean`), and the retiring-fault
  glue `square_retire_fault` (`RMCRetireBranch.lean`).
- Proven arms: add sub and or xor shl shr addi lui (setReg shape), beq
  blt (branch shape), jalr, lw (both authority branches), halt (T6
  unwind via the halt bridge over the pc-advance correspondence), yield
  (budget-footprint variant), plus the decode-failure fallback
  (`square_retire_illegal` — closed without a reachability argument).
- Spec-side technique for the remaining system ops: expose the do-term
  by `show`, then `simp only [specM_bind, SpecM.<defs>, specM_pure]`
  and case the guards (hand-written match trees do NOT defeq-check
  against the monad's matchers — see the lw arm).

16/25 as of the same evening: `sw` landed (port-0 commit selection,
moverAct_mem_core generalization, swHit forwarding = post-core memory;
Inert.of_benign7 + square_retire_store / square_retire_fault_of glues).


### DONE (2026-07-14): the `map` arm landed (18/25)

`square_retire_map` proven in `RMCRetireMap.lean` and wired into the
dispatcher (opcode-20 stub deleted from `RMC.lean`). Shape that worked:

- One shared `hcore0`/`hDO` pair exposes the verified exec do-term as an
  *equation* (`retire T1 E W = match (do-term applied) with ...`), then
  each of the three outcomes rewrites its own liveCap scrutinee into it
  (`rw [hRD, hlc*]`). Per-case reductions beat a single three-outcome
  match statement: `rw` cannot touch patterns under unreduced matchers.
- The `some`-case needs `obtain ⟨ce, hlcS', hcek⟩ := ⟨_, hlcS, rfl⟩` so
  the entry is a *variable*: `simp only [hcek]` after the scrutinee
  rewrite, and again after `simp only [reduceIte, specM_bind,
  specM_pure]` exposes the bound tuple's `.kind` projection.
- STALE/BADCAP → `map_err_common` (mapOkE-off quiescence + ladder
  if_pos); OK → `square_retire_rgnop` with the two-write region fold
  (`seqAll_append_run` + `seqAll_ite_run_unique`), `sAuth_map_eval`,
  and the value bridge `hMV : decRegion (mapValE eval) = mapRgn E S G B
  L P` (`hkc E S` + `decKind_mem_iff` → `mapVal_pack` → `decRef_encRef`
  → `decRegion_encRegion`; `hrf` via toNat lemmas + `BitVec.or_assoc`).
- `RegEnv.set` if-conditions orient as `readName = writtenName`; the
  name-disjointness `decide +kernel` facts must match that order.

### DONE (2026-07-14): the `move` arm landed (19/25)

`square_retire_move` proven in `RMCRetireMove.lean` (the biggest arm:
15 outcomes) and wired into the dispatcher. What made it tractable:

- The map-arm spec-reduction pattern scales: one `hcore0`/`hDO` do-term
  equation, a 14-level ladder-tower fact (`hladder` + per-case if_neg
  chains), and per-outcome scrutinee rewrites. The reduction stalls at
  each unresolved guard — re-run the SpecM simp set after each `rw`
  (the require/demand ite blocks bind-reduction of the continuation).
- The two Mover bridges were refactored into value-parameterized run
  lemmas (`absMover_moverAct_run` / `moverAct_mem_run`): the seven
  postJ field trees evaluate to abstract values + a decoded-job
  equation. Quiescent wrappers instantiate at the `mov_*` registers;
  the install instantiates at `moveJob E` evals (`postJ_install`,
  `encRefE_sel_eval`, `finOfBv_dLit`), with `remaining` needing the
  outOfRange bound to collapse the 13-bit truncation.
- `square_retire_movejob` = `square_retire_rgnop` with the mover faces
  swapped for the run bridges and `Inert` weakened to kill-chains-off
  (`killedByCore_of_nokill`; `sAuth_quiescent_eval` relaxed likewise).

### DONE (2026-07-14): the `cap_dup` arm landed (20/25)

`RMCRetireDup.lean` is sorry-free and wired into `RMC.lean`. The free-slot and
free-cell encoder bridges, watched-ref Mover wrappers, generic
`square_retire_install` glue, `dupFull` write-set frames, and the complete
cap/lineage register walks are in place. The `cap_dup` control proof covers
stale/class errors, every memory-narrowing error, both allocation errors,
and both successful installs (gate and narrowed-memory kinds).

The install-vs-watched-refs argument turned out cleaner than the earlier
`RefFate` contingency: current `Tombstone.lean` already proves both
`MoverLiveSrc` and `MoverLiveMem` invariants. Thus each active watched ref
is live, its slot is occupied, and it cannot be the free install slot.
`installDerived_caps_at_live` packages exactly that fact; slot generations
are unchanged by `installDerived`. No new `Coupled` clause was needed.

The successful cases use `absDom_dupFull_install`: six final register walks
collapse the cap and lineage tables to functional updates, while the result
register and pc faces match `setReg` and retirement advance. The same
infrastructure is intended for `mem_grant` next.

### DONE (2026-07-15): the `mem_grant` arm landed (21/25)

`RMCRetireGrant.lean` contains the shared sorry-free `mem_grant` slice:
descriptor-target mux/free-encoder bridges, a proof that the four-way domain
fold selects exactly `descDom dw`, reductions from the fired grant action to
one selected `installA` and then to six fixed table writes, and the decoded
target-domain cap/lineage functional updates. Both `RMCRetireDup` and this
grant slice build from source. The issuer `rd`/pc face and both two-domain
compositions are now proved: `E = T` merges all four updates in one domain;
`E ≠ T` gives separate issuer-only and target-only records. The full-arm
scaffold also has a source-checked decode/spec bridge and the exact
eight-check hardware ladder. `RMCRetireGrantArm.lean` now proves every error
outcome, including the two target-muxed allocation failures, and the success
path for both `E = T` and `E ≠ T`. `RMCRetireGrantFrame.lean` supplies the
unchanged-domain/gate frames; the arm closes through
`square_retire_install` and is wired into `RMC.lean`.

### DONE (2026-07-15): the `cap_drop` arm landed (22/25)

`RMCRetireDrop.lean` and `RMCRetireDropArm.lean` are sorry-free and the arm is
wired into `RMC.lean`. The proof covers stale-handle and bad-class failures,
the reparent-or-orphan structural split, selected-slot clearing, region and
Mover sweeps, the optional authorized stale-status write, and absent, killed,
and surviving active Mover jobs. The shared Mover run bridge now depends only
on endpoint kind, so orphaning a surviving capability's lineage does not
overconstrain the datapath proof. `lake build Machines.Lnp64u.Theorems.RMC`
rebuilt all 983 dependent jobs successfully.

Remaining (the deep tail): `gate_call`, `gate_return`, and `cap_revoke`. The
25-way dispatcher and illegal fallback are already wired; these are exactly
the three audit-legal leaf sorries in `RMC.lean`.

## 0. Working rule: write forward from source

Stop treating `RMC.lean` as a recovery job. The goal is a clean, compiling
implementation rebuilt from the current source files, not a splice of old
fragments.

- Source of truth: `Machines/Lnp64u/Hw/*.lean`,
  `Machines/Lnp64u/Step.lean`, `Machines/Lnp64u/Logic/*.lean`, and the
  current public theorem API needed by downstream files.
- Historical recovery material was deleted 2026-07-04 (user decision); all
  statements and proofs are re-derived against today's code.
- Do not run `git checkout`, `git restore`, or other path-reverting commands
  in this dirty worktree. Remove experiments with edits, and preserve user
  work before risky changes.
- Work in compiling slices. After each slice, run the smallest useful Lean
  command, then the full target once the slice is structurally complete.

## 1. DONE 2026-07-16 — R-MC retirement tail and unbounded assembly

All three final leaves (`gate_call`, `gate_return`, `cap_revoke`) are proved
and wired. `Coupled.rv_sync` carries the bounded revoke-engine invariant;
`rvSync_cycle` proves preservation across countdown, retirement, idle, and
issue cycles; `square_retire_rev` closes the final retirement behavior.
The resulting `square`/`abs_run`/`refines`/`invariant_transport` chain is
sorry-free and audit-CLEAN. The work order below is retained to document how
the proof was decomposed.

1. **DONE 2026-07-15.** (dispatcher wired; now 5 leaf sorries.) Rewrite `square_retire` as a
   `by_cases` chain on `(σ.regs "if_word" 32).extractLsb' 0 6` over the
   25 declared opcodes: 16 branches call the proven arms
   (`RMCRetireAlu`/`RMCRetireBranch`/`RMCRetireSw`), the not-in-table
   branch derives `decode = none` and calls `square_retire_illegal`,
   and the 9 unproven ops become independent leaf sorries (stub
   theorems, one per op, in a single file so the ledger stays honest).
   This retires final-assembly risk early and validates the 16 arm
   signatures against the real call site.
2. **DONE 2026-07-15** (`RMCRv.lean`: `RvSync` triple over `reachRootN`/`liveChainN`/`chainEndN`, guard vacuity analysis, deferred-obligation list). Read `rvInit`/`rvStep`
   against the spec's `cap_revoke` exec and *state* the rv-coupling
   `Coupled` clause (hidden `rv_*` registers = the spec mark-set after
   `revokeCost - if_cl` doubling rounds). Do not prove preservation
   yet. The countdown arm already runs `rvStep` rounds — check the
   clause coexists with `square_countdown` as proven. Revoke is the
   largest remaining unknown; surface its shape before grinding.
3. **DONE 2026-07-14 — Tier 1 pattern extensions.** `map`/`unmap` and
   `move` are proved and wired. Original recipe (one session each, from `sw`):
   arm): `map`/`unmap` (region-edit face: `mapSet`/`unmapSet` fire, so
   an Inert-minus-map variant plus `rgnVPostE`/`rgnValPostE` selected
   forms; region-face `absDom` variant like `absDom_regpcbud`), then
   `move` (job install: `newJobSet` fires; `postJ` selected forms; the
   mover-field face shows the installed job).
4. **DONE 2026-07-15 — Tier 2 install invariant.** (`cap_dup` and
   `mem_grant`): an
   install must not flip a Mover-watched ref dead→live. First check
   whether T3's Mover liveness invariants (available through the arm's
   `hsr` reachability hypothesis) already give it. **Resolved:** both
   `MoverLiveSrc` and `MoverLiveMem` do; no `Coupled` clause required.
   Reuse `RMCRetireDup`'s cap-table/install face for `mem_grant`.
5. **DONE 2026-07-16 — Tier 3 kill machinery** (`cap_drop`, `gate_call`,
   `gate_return`): `killedByCoreE` fires for real. Shared kill-variant
   of the Mover faces (watched-ref liveness *after* the kill sweep =
   spec `moverPhase` on the post-kill state), plus the gate
   save/restore faces for call/return (`absGate` variant exposing the
   activation fields).
   **Completion update:** the shared whole-state `transferA` abstraction,
   complete call activation/transfer square, and return restore/transfer
   square all landed and are wired into the dispatcher. The detailed notes
   that follow capture the earlier drop-first construction sequence.
   **Started 2026-07-15:** `RMCRetireDrop.lean` now proves the unique
   retiring-domain selector pointwise, decodes the selected slot kill
   predicate, reduces the global `killedByCoreE` tree to the successful
   drop kill set, and proves failed drops Mover-inert because `dropOkE`
   gates that tree. The spec-side clear/sweep equations are now exact for
   every region, the Mover job, and the Mover status-memory write; the
   hardware region-valid update is proved equal to the swept spec region
   table, and `movKilledE` is proved to fire exactly when the decoded active
   job has a source or destination in the dropped slot. The remaining Mover
   execution bridge now has the required refinement on both shared active-job
   faces: the mover-field and memory run theorems use endpoint-local kill
   assumptions, with all existing callers rebuilt, and `RMCRetireDrop`
   supplies the corresponding outside-the-slot silence lemma. The fired-kill
   branch is also closed at the Mover layer: with no new job installation,
   `moverAct` decodes to `none` and leaves memory unchanged (the sweeping core
   owns the stale-status write). Next finish the drop status-authority bridge
   and the cap/lineage reparent-or-orphan register face. **Status authority is
   now closed:** the hardware post-region OR-tree is equivalent to
   `domCovers` on the exact swept option-valued region table. Structural work
   has started with `bumpE_eval` and the exact selected-slot `clearSlotA`
   capability-valid projection. Its generation and both lineage cases are now
   exact as well (derived entries free one cell; roots preserve all cells).
   A reusable injective guarded-write walk theorem now supports the global
   lineage scans, and `reparentA`'s pointwise parent update plus complete
   non-parent register frame are proved. The two-part `orphanA` walk is now
   exact on both affected valid-bit banks and frames everything else. Both
   reparent/orphan branches have been lifted to decoded capability and
   lineage-table equations, and `clearSlotA` now has decoded capability,
   generation, and lineage equations for arbitrary domains. Those faces are
   now composed into whole-domain theorems for each primitive and for both
   reparent+clear/orphan+clear branches. The actual `dropSel` lineage bits,
   dynamic cell lookup, parent word, and packed old reference are connected
   to the selected abstract entry: under `Wf`, the hardware parent guard is
   exactly the spec `parentOf` split. Consequently the first two successful
   `dropCirc` actions now decode, for every domain, to the full structural
   spec branch followed by `clearSlot`. The surrounding `sweepRegionsA` walk
   now also has exact pointwise write semantics and a complete frame, and its
   composition with that structural prefix is proved as a whole-domain
   equality to spec `sweepRegions` (including the exact option-valued region
   table). A generic decoded `writeReg; pcAdv` theorem (including hardwired
   `r0`) now closes the successful five-action payload through `rd := 0` and
   PC advance, with its run proved definitionally equal to `dropCirc`'s list.
   The Mover phase is now closed parametrically as well: unified field and
   memory bridges split absent, endpoint-killed, and surviving active jobs;
   the surviving case reuses the endpoint-local run theorems, while the killed
   case consumes the core's stale-status write. A new `square_retire_kill`
   assembler accepts these exact non-inert Mover faces. **DONE 2026-07-15:**
   `square_retire_drop` instantiates that assembler for all three outcomes and
   `square_retire_capdrop` is wired into the dispatcher. Next reuse the
   kill-aware assembly for the two gate arms and add their activation
   save/restore plus capability-transfer faces.
6. **DONE 2026-07-16 — Tier 4 `cap_revoke`.** `rvInit` establishes the
   vector invariant, `rvStep` doubles its represented horizon, full-cycle
   preservation handles issue/retire vacuity, and retirement identifies
   the saturated `rv_r` vector with the spec's `marks` closure.
7. **DONE 2026-07-16 — Assembly.** The leaf sorries were deleted and
   `square`/`abs_run`/`refines`/`invariant_transport` are CLEAN.

### Historical remaining-arm timeboxes (checkpointed 2026-07-15)

These are stop-and-reassess bounds, not promises to grind indefinitely:

1. **`gate_call`: 6 focused hours maximum.** Spend at most 2 hours inventorying
   the real `callAct`/`transferCap`/activation register faces and proving one
   selected transfer projection. Continue for the remaining 4 hours only if
   that projection composes with the existing kill-aware square. Otherwise
   checkpoint the missing shared bridge explicitly before more case work.
2. **`gate_return`: 4 focused hours maximum after the call checkpoint.** Reuse
   the transfer and activation framing from `gate_call`; stop after 90 minutes
   if return needs a materially different transfer theorem, and revise the
   bound rather than silently absorbing a second infrastructure project.
3. **`cap_revoke`: 8-hour convergence spike, then reassess.** First 3 hours:
   prove one concrete `rvInit`/`rvStep`-to-`iterMark` round relation and verify
   the proposed `RvSync` clause survives countdown. Remaining 5 hours only if
   the doubling/convergence invariant closes at the statement level. A full
   arm gets a separate estimate after that evidence; current source does not
   justify bundling it into the gate-arm window.

Established recipes (do not rediscover): benign ops →
`square_retire_domShape`; faults → `square_retire_fault_of`; memory
writers → `square_retire_store` over `moverAct_mem_core`; spec exec
reduction → show-the-do-term + `simp only [specM_bind, SpecM.<defs>]`
(hand-written match trees do NOT defeq-check); write-set frames →
value-free `regWrites` lists + quantified `decide +kernel`; new
`Coupled` clauses → the `CanonWritesAll`/`ZeroWritesAll` checker
pattern.

Verification gate per landing: `lake build` (full), `lake exe audit`,
`scripts/ci.sh`.

## 4. DONE 2026-07-04 - D11 scheduler stall-lock redesign

T6 used to carry the `StallFree` hypothesis because the scheduler had an
unbounded-priority-inversion bug (residual-budget stall-lock, found
2026-07-03: an underfunded top-priority domain stalled the core instead of
yielding the slot). Landed fix: underfunded serving issue now raises a
deterministic `.budget` fault and routes through the existing halt/unwind
proof path; underfunded non-serving issue burns the payer's residual
budget to zero. `T6.no_hostage` no longer has a `StallFree` premise.

## 5. Cheap hardening (one session, mostly independent)

- **(from TRUST.md audit)** Prove `compileImpl = compile` (or gate-compare
  reference output in audit/ci) - `@[implemented_by]` at
  `Loom/Hw/Compile.lean:386` is an unproved executable replacement; every
  emitted artifact and BMC CNF flows through it.
- DONE 2026-07-04: witness manifests landed in
  `Tests.Lnp64uWitnesses` and are explicitly built by `scripts/ci.sh`.
  Covered: `Manifest.WF`, `RMC.Fits`, T7 schedulability on the base
  lockstep manifest; a concrete isolated manifest for T5's finite
  `Isolated & TopPriority & AgreeOn` premises and T6's finite
  `StrictlySchedulable & positive budgets` premises. D11 deleted the former
  semantic `StallFree` side condition.
- PARTIAL 2026-07-04: `scripts/check_xfree_rtl.py` now runs in CI after
  fresh Acc8 + LNP64-u emission. It rejects X/Z/don't-care literals or
  constructs, missing register resets, and partial memory initialization in
  the exact emitted core RTL. Still open: turn this into a Lean parser/AST
  2-state-safety theorem and cover synthesis undefined-read/don't-care
  adequacy explicitly.
- **(from TRUST.md audit)** Specify platform event accounting and fault
  routing: who pays for interrupts/exceptions/flushes/stalls/debug entry,
  and how every hardware fault maps to the deterministic ISS behavior.
- DONE 2026-07-04: deleted the superseded `SystemOpsWf.Wip.system_preserves`
  sorry-bearing obligation and scrubbed stale "kernel-checked" claims that
  were actually compiled-eval (`#guard` round-trip). Still open: make one
  full-size round-trip genuinely kernel-checked (needs the
  String-to-ByteArray kernel-cost fix).
- DONE 2026-07-04: `scripts/ci.sh` now explicitly runs
  `lake build Tests.Acc8Bmc`, so stale baked LRAT certificates are caught by
  the normal CI path. The target is still intentionally documented because
  any `Loom/Hw/Compile.lean` change can invalidate the certificate.
- `parseCheck` kernel round-trip for `rtl/lnp64u.v` (mirror
  `Machines/Acc8/TextRoundTrip.lean`) - closes the printer out of the
  lnp64u TCB the way it's already closed for Acc8. Note: `rtl/` is
  untracked, so this needs either committing the artifact or checking at
  emission time.
- LNP64-u BMC demo via `Dp/Bmc` (machinery proven on Acc8; hasn't bitten
  into the big core yet). Regenerate certs with the untrusted cadical
  driver (`Loom/Dp/Solver.solve`) - remember baked certs go stale on ANY
  `Loom/Hw/Compile.lean` change.

## 6. RESOLVED 2026-07-13 - tagless-final datapath unification REJECTED

The Stage-1 experiment (RMCOps.lean) ran the refactor's own test case:
prove `cap_dup`'s datapath-value equivalences (`handleE_pack`,
`narrowKindE_pack`) and a representative ladder check (`freeSlotV_eval`)
with the existing bridge machinery. Verdict: each falls in ~25 mechanical
lines — the datapath values were never the cost center. The per-op cost
lives in (a) the errno-ladder control flow and (b) the kernel-write
structure, and both are *shared-helper-shaped* (`installA`, `clearSlotA`,
`transferA`, sweeps, `haltAct`), used by several ops each. A
tagless-final source refactor would not collapse (a) or (b), and would
churn every emitted artifact (goldens, Acc8 BMC certificate, lockstep).

Adopted instead: keep `Hw/SysOps.lean` exactly as emitted; grow the
proof-side shared library —

1. `RMCOps.lean` — per-op value packings and ladder-check bridges
   (encoder images, free-slot/free-cell scans, capSel).
2. Kernel-helper bridges, one per helper, each serving several ops:
   `haltAct` ↔ `haltDom` (all fault arms), `installA` ↔ `installDerived`
   (dup/grant/call/return), `clearSlotA` ↔ `clearSlot`, `transferA` ↔
   `transferCap`, sweeps ↔ `sweepRegions`/`sweepMover`.
3. A generic errno-ladder ↔ `SpecM` require-chain correspondence.

## Deferred / out of scope

FPGA bring-up; `Dp/Pdr` (until scaling demands); the Phase-3 logical
relation (T2'/T4') on the uLog seed; spec-cycle epoch alternatives
(superseded by the wrapping `BitVec 32` decision, see `STATUS.md`).

## Operational notes

- Agent worktrees need a fully-copied `.lake` seed or they rebuild the
  world (`cp -a .lake` then atomic swap; an interrupted copy leaves a
  broken cache). Agents should `git merge main --no-edit` before starting.
- Run emitters under `ulimit -v 25000000` - earlyoom kills whole process
  groups on this box and prefers `lnp64*`/`yosys` names.
- Baked SAT certificates go stale on ANY `Loom/Hw/Compile.lean` change,
  and `decide` will disprove them; regenerate via the untrusted cadical
  driver (`Loom/Dp/Solver.solve`). `ci.sh` now explicitly builds
  `Tests.Acc8Bmc`.
- The SpecM sweep pattern has nine worked instances (SlotGen, Budget,
  Inflight, Authority, Tombstone, GateStep, Hostage's chain kit, DFrame,
  DRel) - never write one from scratch.
- Audit policy: sorries only in `Machines/*/Theorems/` + `Wip` namespaces;
  `native_decide` banned; only the two uVerilog boundary declarations are
  whitelisted. `lake exe audit` is the gate; `scripts/ci.sh` the full check.

---

# Publication Readiness TODO

Goal: get the repo and project to the quality bar for CPP/ITP/FMCAD submission with
artifact evaluation, plus arXiv preprint. Ordered roughly by dependency, not priority —
items marked ★ are the ones reviewers/AEC members check first.

## P1. Proof ledger & trust story (the core claims)

- [ ] ★ **Freeze the claimed-theorem set.** Decide which ledger theorems are *in* the
      paper (proved, no `sorry` anywhere in their dependency cone) vs. explicitly
      future work. Reviewers will `grep -r sorry` — every hit must be in `Theorems/`/`Wip`
      *and* not upstream of anything the paper claims.
- [x] ★ **Axiom audit, printed.** Add a `lake exe axioms` (or extend `audit`) that prints
      the full axiom closure of each headline theorem (`#print axioms` per theorem,
      machine-collected). The paper's trust section should be generated from this, not
      hand-written. The µVerilog boundary declarations should be the only
      non-kernel project axioms listed.
      *(DONE 2026-07-04: `lake exe audit` prints `axioms <theorem>: [...]`
      for all 92 ledger theorems, reusing the same machine-collected closures
      that drive the CLEAN/STATED/FLAGGED policy.)*
- [x] **State `ImplementsStandard` precisely and minimally.** Reviewers will read this
      axiom character by character. Ensure it quantifies over exactly the µVerilog subset
      you emit, not "the Verilog standard" broadly. Consider splitting it if it currently
      bundles simulator + synthesizer assumptions.
      *(DONE 2026-07-04: `Axiom.lean` now states the boundary as concrete
      reset/cycle agreement for one emitted µVerilog module and one concrete
      tool realization, explicitly excluding full-Verilog, timing, physical,
      and arbitrary-flow claims. The Lean shape is documented as one boundary
      assumption exposed by the `ImplementsStandard` predicate plus the
      `implements_standard_spec` axiom.)*
- [ ] **Close or clearly fence the LNP64-µ ledger gaps.** STATUS.md rows that are
      partial should say *what* is missing (e.g. "noninterference proved for DMA-off
      configurations only"). Honest partiality is fine; vague partiality kills reviews.
- [ ] **Emission theorem statement review.** The generic register + multi-port memory
      fold theorem is the paper's centerpiece — have someone outside the project read
      just its statement (not proof) and confirm it says what the prose claims,
      especially `MemWriteWF` side conditions.
- [ ] **Name and number the decisions.** D9 (last-write-wins ≡ nonblocking) style
      decision records for every semantic choice; the paper's design-rationale section
      writes itself from these.

## P2. Repo hygiene & reproducibility ★ (artifact evaluation gate)

- [ ] ★ **One-command cold build.** From a clean clone on a fresh machine:
      `./scripts/reproduce.sh` fetches the pinned toolchain, builds, runs
      `lake exe audit`, the BMC/LRAT checks, emission + RTL hygiene, and both
      lockstep scripts. *(LANDED 2026-07-14: `scripts/reproduce.sh` = ci.sh +
      lockstep, with pinned tool versions documented in its header. Missing:
      golden `.v` diff (blocked on the rtl/ tracked-vs-regenerated decision).)*
      *(2026-07-27: first wiped-tree run of `build_verified_release.sh`
      exposed four defects invisible from a warm tree — an undocumented
      `ripgrep` dependency in `quality.sh`, a `test_release_binding.py`
      fixture that had drifted from its checker, `SymbolicVerified` missing
      from the lake prerequisites, and R-MC proofs broken by the `SysOps`
      opacity refactor. All fixed. Run wiped-tree builds on a schedule.)*
- [ ] **Audit host dependencies.** Every external binary a build script
      assumes must be either pinned and documented in `REPRODUCING.md` or
      replaced by something POSIX. `ripgrep` was neither, and it failed in
      the *first* phase of the release build.
- [x] ★ **Pin everything.** *(DONE 2026-07-14: `lean-toolchain` (v4.28.0) and
      the lake manifest are committed; `scripts/reproduce.sh` documents the
      external tool pins — iverilog 12.0, yosys 0.33, cadical 1.7.3 with
      `--no-binary --lrat`.)*
- [ ] ★ **Container image.** Dockerfile (or Nix flake) that reproduces the CI run
      bit-for-bit. Push a tagged image; artifact submissions that "just work" in a
      container get badges, ones that don't get rejected.
- [ ] **Committed golden artifacts + hashes.** Check in the emitted `Acc8.v` /
      `Lnp64u.v` with SHA-256 hashes, and document the one-liner that verifies a
      downloaded `.v` matches the emitted bytes that the round-trip checker
      parses. Do not call these bytes kernel-checked until the full-size
      round-trip uses kernel reduction rather than compiled evaluation.
      *(NOTE: `rtl/` is currently deliberately untracked (regenerate-on-demand);
      this item reverses that decision — and is the same call as the lnp64u
      `parseCheck` item in engineering §3 above. Decide once, do both together.
      Emission is deterministic: today's `lnp64u.v` re-emit was byte-identical.)*
- [ ] **CI on every push, publicly visible.** GitHub Actions badge running
      `scripts/ci.sh`; add a separate badge for `lake exe audit` so the trust gate is
      visible from the README.
- [ ] **Repo layout cleanup.** Remove dead code, stale branches, `Wip` files not
      referenced by STATUS.md. Reviewers browse; clutter reads as immaturity.
- [x] **LICENSE, NOTICE, output-exception text, DCO in CONTRIBUTING.md.** Plus the
      "no patents filed or planned; this disclosure is intentional prior art" statement.
      *(DONE 2026-07-04: Apache-2.0 root + SHL-2.1 on Machines/ (dual, SPDX
      `Apache-2.0 OR SHL-2.1`), NOTICE with output exception + patent pledge,
      DCO CONTRIBUTING.md, SPDX headers on all 124 tracked source files;
      copyright Kevin Baragona. README carries the exception + pledge up front.)*

## P3. Evaluation section material (what the paper measures)

- [ ] ★ **Proof-effort table.** Lines of Lean per component (EDSL, compiler, emission
      theorem, parser, per-machine specs/proofs), build time, proof-checking time.
      Standard table in every ITP/CPP paper; script it so it regenerates.
      *(TOOLING IN HAND 2026-07-27: `scripts/phase_timing.sh` records
      per-phase wall/CPU/parallelism for every run, and
      `scripts/measure_check_cost.py` separates kernel-checking CPU from
      per-process import toll. Report checking cost, not wall clock — wall
      clock measures the scheduler, not the proof.)*
- [ ] ★ **Lockstep campaign statistics.** How many cycles, how many programs
      (random? directed?), full-state vs. sampled comparison, for both machines.
      "Corroborated by lockstep" needs numbers to survive review.
      *(PARTIALLY IN HAND: LNP64-µ 256-cycle base-op + 2000-cycle system-op
      manifests, full-state per-cycle, in Lean (`Tests/Lnp64uCore.lean`) AND in
      iverilog vs ISS goldens (`scripts/lockstep_lnp64u.sh`); Acc8 likewise
      (`scripts/lockstep_acc8.sh`). Directed manifests only — no random-program
      campaign yet; that's the gap for review.)*
- [ ] **Synthesis results.** Yosys (+ OpenROAD or at minimum a generic synth target)
      area/timing for Acc8 and LNP64-µ. Even one table row each moves the paper from
      "model" to "hardware" in reviewers' eyes. Record exact tool versions/scripts.
      *(PARTIALLY IN HAND: yosys 0.33 generic-synth cell counts recorded in
      STATUS.md — LNP64-µ: 1.57M cells / 7,849 FFs / RAM as `$mem_v2`, via the
      memory-aware flow in `scripts/lockstep_lnp64u.sh`. Missing: Acc8 row in the
      same table form, timing numbers, OpenROAD.)*
- [ ] **Baseline comparison.** A qualitative (table-form) comparison against Kami,
      Kôika, Bluespec, Cava/Silver Oak, and translation-validation flows: what is
      proved, what is trusted, where the TCB boundary sits. This is the related-work
      section's spine and the most common "reject: doesn't situate itself" fix.
      *(Situate this work precisely: it holds a CompCert-shaped generic
      compiler theorem (`compile_cycle`) AND performs per-artifact
      translation validation on top of it, because the shipped bytes are a
      materialized rendering rather than a literal `compile d`. Reviewers
      familiar with either tradition will ask why both; the answer is the
      exact-byte binding, and it should be stated rather than discovered.)*
- [ ] **Trusted computing base inventory.** Explicit list: Lean kernel, `lake exe
      audit` implementation(?), the `#guard` byte-check path, `ImplementsStandard`,
      simulator binary. State what is *not* trusted (printer, compiler, parser impl).
- [ ] **A worked example small enough to print.** A 3–5 rule `Design` whose full
      journey (Lean value → mux-chain fold → emitted `.v` → re-parse) fits in two
      pages. Acc8 is probably too big for inline listings; make a toy.

## P4. Documentation & onboarding

- [ ] ★ **README rewrite for three audiences.** Top: what is proved, in one screen,
      with the axiom count. Then split paths: "I'm a Lean person" (Reservoir install,
      Zulip link), "I'm a hardware person" (download the `.v`, verify the hash, run
      lockstep), "I'm a reviewer" (reproduce.sh, STATUS.md, audit gate).
- [ ] **STATUS.md → generated, not hand-edited.** If any part is manual, make
      `lake exe audit` emit it. "Mechanically-audited ledger" is a headline claim;
      it must literally be mechanical.
      *(CURRENT STATE: the CLEAN/STATED verdicts come from `lake exe audit` but
      are transcribed into STATUS.md by hand; the narrative header sections are
      entirely hand-written. The generated/manual split needs to become
      structural.)*
- [ ] **Architecture document.** Promote `Hw/DESIGN.md` decisions into a top-level
      ARCHITECTURE.md with the D-numbered decisions, the semantics discipline, and a
      diagram of the trust chain (Design → Module → text → re-parse → #guard).
- [ ] **Docstrings on every public definition** in `Loom/` (the toolchain half at
      minimum). doc-gen4 output published via GitHub Pages.
- [ ] **A tutorial: "your first proved processor."** Walk a reader from empty file to
      a 2-register machine with one proved invariant and emitted Verilog. This is the
      single highest-leverage adoption artifact and reviewers love citing it as
      evidence of usability.
      *(Scoped 2026-07-28 by the goal-fork section: the tutorial promises the
      v1 claim only — invariant transport, not ISS refinement. It runs in
      parallel with Task 0, not after it, and it is not complete until the
      stranger-user falsification protocol in that section has been run at
      least once and its interventions filed as bugs.)*

## P5. The paper itself

- [ ] ★ **Pick venue + deadline and work backwards.** CPP (~mid-Sept deadline),
      ITP (~Feb), FMCAD (~May). Choose one primary; check current CFP dates now.
- [ ] **arXiv preprint first** (cs.LO, cross-list cs.AR/cs.PL) — timestamp + defensive
      publication. Can be a slightly rougher cut than the submission.
- [ ] **Decide the paper's single claim.** Candidate: "a proof-carrying HDL toolchain
      where the emitted Verilog's correspondence to the proved model is itself
      kernel-checked for at least one full-size artifact, with one narrowly
      stated µVerilog tool-boundary assumption to physical reality." Everything
      not serving that claim moves to future work or paper #2.
- [ ] **Reserve paper #2.** LNP64-µ security theorems (isolation/noninterference/
      revocation down to RTL) → S&P/USENIX/CCS later; don't dilute paper #1 with it
      beyond a teaser.
- [ ] **External pre-review.** One Lean/ITP person and one RTL/verification person
      read the draft cold; fix everything they stumble on before submission.
- [ ] **Artifact submission package.** Container + reproduce script + README-for-AEC
      with expected runtimes and expected outputs (hashes). Dry-run it yourself on a
      machine that has never seen the repo.

## P6. Community & credibility (parallel track, low cost)

- [ ] **Lean Zulip announcement thread** once README + tutorial land.
- [ ] **Reservoir (Lake package index) publication** for `Loom/`.
- [ ] **Talk proposals:** Lean Together; ORConf/Latch-Up; PLARCH or similar workshop
      for early feedback before the main submission.
- [ ] **Tag a versioned release** (`v0.x`) whose release notes are the theorem
      ledger delta — establish the "guarantees are the changelog" convention now.
- [ ] **(Optional) Tiny Tapeout run for Acc8** — cheap, and "the proved core exists
      in silicon" is a one-sentence credibility multiplier in every future talk.

### Suggested sequencing

1. §P2 reproducibility + §P1 ledger freeze (everything else depends on a stable,
   reproducible claim set).
2. §P3 evaluation data collection (scripted, so it survives later proof changes).
3. §P4 docs + §P6 community in parallel with…
4. §P5 arXiv draft → external pre-review → venue submission with artifact.
