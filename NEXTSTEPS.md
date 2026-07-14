# NEXT STEPS - active plan as of 2026-07-04

Current state: T1-T9 CLEAN, RTL corroborated (iverilog + yosys), R-MC
unbounded with ONE audit-legal R-MC sorry left (`square`);
`coupled_step` is CLEAN as of 2026-07-05 (`RMCFrames.lean` +
`RMCCanon.lean`, no native_decide).
See `STATUS.md` for the audited ledger and session history.

## Stopping point - 2026-07-04

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

Immediate next step (2026-07-14): **`square` is proven modulo the
retirement arm.** The master dispatcher in `RMC.lean` cases on
countdown / idle-stall / idle-issue — all three fully proven — leaving
`square_retire` (in-flight instruction on its last cycle: the 25-op
retirement grind + the `cap_revoke` mark engine) as the sole R-MC sorry.
The idle-issue arm landed complete (`RMCIssue.lean`): all eight outcomes
(fetch/decode/budget/protocol/donation faults via the halt bridge,
residual burn, plain and serving issue) with the scheduler/decode/
budget/donation condition glue. Next: the retirement dispatch skeleton
(retireAct: if_v clear, per-domain dispatch via the guarded-fold lemmas,
port-0 memory commit), then per-op arms using the kernel-helper bridges
(installA/clearSlotA/transferA/sweeps — the RMCOps/§6-resolution plan),
then the `cap_revoke` rv-engine convergence and its Coupled clause.

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

## 1. R-MC bridge rewrite - immediate target

Target: `lake build Machines.Lnp64u.Theorems.RMC` succeeds while shrinking
the remaining R-MC sorries in place. Current count: two (`square`,
`coupled_step`). This is the current highest value engineering task.

Build the file from scratch in this order:

1. **External shape.** DONE for reset. Keep the public statements downstream files depend on:
   `Fits`, `Coupled`, reset pullback facts, `coupled_step`,
   `design_run_succ`, and the invariant pullback section. Rename internals
   freely if that reduces proof friction.
2. **Generic frame layer.** Prove the small register and memory preservation
   facts needed for `refillAct`, `coreAct`, `moverAct`, and `tickAct` directly
   from `Act.regWrites`, `Act.memWrites`, and `Loom.Hw.Compile.run_regs_notin`.
   Generate repetitive frame lemmas only after the hand-written wrapper is
   compiling.
3. **Refill bridge.** Prove the refill abstraction facts fieldwise:
   `cycle`, `rctr`, `dbudget`, visible domain fields, gate state, inflight
   state, and memory preservation. Use current `SysOps.lean` definitions as
   the expression source.
4. **Core/tick bridge.** Prove the core-cycle unfold and tick abstraction:
   cycle increments, visible state is preserved except for the cycle field,
   and the final statement rewrites cleanly into the spec-side cycle lemmas
   already public in `Hostage.lean`.
5. **Mover bridge.** Re-derive the mover expression names from
   `Machines/Lnp64u/Hw/SysOps.lean` rather than copying old text. Prove the
   two primary cases: no live mover job preserves `mem`/`absMover`; a live
   mover job updates memory and `absMover` to match `Step.moverPhase`.
6. **Spec phase equations.** Add only the match-form equations the proof
   actually consumes for `refillPhase`, `corePhase`, and `moverPhase`.
   Reuse existing public cycle lemmas from `Hostage.lean`; do not duplicate
   them in `RMC.lean`.
7. **Assembly.** Rebuild the decomposition lemmas that reduce `square` to
   the per-arm cases, then reconnect `coupled_step`, `design_run_succ`, and
   invariant pullback.

Verification gate for this item:

- `lake build Machines.Lnp64u.Theorems.RMC`
- `lake build Machines.Lnp64u.Theorems.RMCAbs`
- `lake build Machines.Lnp64u.Theorems.RMCReset`
- `lake exe audit`
- `scripts/ci.sh` before committing a claimed landing

## 2. R-MC remaining sorries (`coupled_step`, then `square`)

The last link making T2-T9 theorems about the emitted netlist rather than
the spec. Do not block on a tagless-final refactor.

Work order:

1. Shared cycle/refill/tick bridge lemmas.
2. `coupled_step` preservation of `rctr_sync`, `run_canon`, and
   `kind_canon`; extend `Coupled` only when a proof obligation forces it.
3. `square` countdown/no-retire arm.
4. `square` issue arm.
5. Fourteen base-op retirement cases.
6. Ten system-op retirement cases.
7. `cap_revoke` pointer-doubling mark engine and the corresponding
   `Coupled` clause.
8. Final assembly and full CI.

## 3. Proof infrastructure - build only what the R-MC proof forces

Useful tooling should be extracted from the `RMC.lean` grind, not placed in
front of it as a prerequisite.

- **Automatic `Act` frame lemmas.** Compile/certify read-write sets and
  generate lemmas such as "this rule cannot write `cycle`", "this action
  preserves unrelated registers", and "this rule preserves memory `mem`".
- **Last-write-wins `Act.run` normalizer.** A tactic/normal form for
  projecting fields through nested `seqAll`, `.ite`, `RegEnv.set`,
  `MemEnv.set`, and record updates.
- **Rule-level abstraction contracts.** Standard theorem skeletons for
  `abs (rule.run pre acc) = specPhase ...` or fieldwise variants.
- **First-class post-rule derived state.** Support ghost/derived values for
  post-core fields, especially mover fields represented as mux expressions
  (`postJ`, `newJobSet`, kill sweeps, store forwarding).
- **Generated reset/register-table proof support.** Make reset abstraction
  automatic from register declarations, memory declarations, and encoder
  round trips.
- **BitVec/encoder simplification.** Certified simplifier for packed fields,
  decode/encode round trips, and `BitVec.toNat` range side conditions.

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
      `./scripts/ci.sh` (or a new `scripts/reproduce.sh`) must fetch the pinned
      toolchain, build, run `lake exe audit`, run both lockstep scripts, and diff the
      emitted `.v` against committed goldens. Time it; AEC budgets are ~2–4 hours.
      *(PARTIALLY IN HAND: `scripts/ci.sh` exists and passes — build + audit +
      Acc8 BMC certificate check + LRAT dual-checker crosscheck. Missing: the
      lockstep scripts, no golden diff, never timed from cold.)*
- [ ] ★ **Pin everything.** `lean-toolchain` committed; lake manifest committed;
      exact versions of iverilog/verilator + yosys documented; SAT solver version
      pinned (and its LRAT output format noted).
      *(PARTIALLY IN HAND: `lean-toolchain` (v4.28.0) and the lake manifest are
      committed. Missing: documented versions of iverilog/yosys/cadical — this box
      runs yosys 0.33, cadical via `--no-binary --lrat`.)*
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
