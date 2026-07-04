# NEXT STEPS — decided 2026-07-04

Current state: 92 ledger theorems, T1–T9 CLEAN, RTL corroborated
(iverilog + yosys), R-MC unbounded with exactly 4 audit-legal sorries.
See `STATUS.md` for the audited ledger and session history.

## 1. R-MC per-op squares (`square` / `coupled_step`) — highest value

The last link making T2–T9 theorems about the *emitted netlist* rather than
the spec (lockstep tests then become mere corroboration). Recipes are
itemized in the four sorries' docstrings in `Machines/Lnp64u/Theorems/RMC.lean`:

- Warm-up: `absDom_reset` / `coupled_reset` — mechanical; needs the
  declList elaborator optimization documented with
  `scripts/gen_rmc_reset_tab.py` to keep CI affordable (~548 lookup arms).
- Main: build an `Act.run` read/write frame kit first, then the 25 per-op
  cases. `cap_revoke`'s multi-cycle pointer-doubling mark engine is the one
  research-grade case (one spec step ↔ ~64 hidden-register cycles).

**Fork with item 4:** either grind the 25 squares on the current
architecture, or do the tagless-final unification first and get most of
them near-definitionally. Decide before starting either.

## 2. D11 — scheduler stall-lock redesign (drop `StallFree` from T6)

T6 carries the `StallFree` hypothesis because the real scheduler has an
unbounded-priority-inversion bug (residual-budget stall-lock, found
2026-07-03: an underfunded top-priority domain stalls the core instead of
yielding the slot). Redesign the scheduler (skip-to-next-eligible or
charge-at-retire), re-prove the touched T6/T7 bricks, and delete the
hypothesis — upgrading `no_hostage` to unconditional. Independent of item
1; good candidate to run in parallel.

## 3. Cheap hardening (one session, mostly independent)

- **(from TRUST.md audit ●)** Prove `compileImpl = compile` (or gate-compare
  reference output in audit/ci) — `@[implemented_by]` at
  `Loom/Hw/Compile.lean:386` is an unproved executable replacement; every
  emitted artifact and BMC CNF flows through it.
- **(from TRUST.md audit ●)** Witness manifests: kernel-checked (`decide`)
  satisfiability instances for each theorem's hypothesis conjunction
  (`Isolated ∧ TopPriority ∧ WF`, `StrictlySchedulable ∧ 0 < budgetQ`, …),
  ideally on the lockstep manifests — kills the vacuity question.
- **(from TRUST.md audit ●)** Delete the 5 superseded `SystemOpsWf.Wip`
  sorries; scrub "kernel-checked" claims that are actually compiled-eval
  (`#guard` round-trip); make one full-size round-trip genuinely
  kernel-checked (needs the String→ByteArray kernel-cost fix).

- Add `lake build Tests.Acc8Bmc` to `scripts/ci.sh` — the 2026-07-04 cert
  staleness (compile change silently invalidated the baked LRAT cert;
  `decide` disproved it) was NOT caught by ci.sh. ~32 s kernel decide.
- `parseCheck` kernel round-trip for `rtl/lnp64u.v` (mirror
  `Machines/Acc8/TextRoundTrip.lean`) — closes the printer out of the
  lnp64u TCB the way it's already closed for Acc8. Note: rtl/ is
  untracked, so this needs either committing the artifact or checking at
  emission time.
- LNP64-µ BMC demo via `Dp/Bmc` (machinery proven on Acc8; hasn't bitten
  into the big core yet). Regenerate certs with the untrusted cadical
  driver (`Loom/Dp/Solver.solve`) — remember baked certs go stale on ANY
  `Loom/Hw/Compile.lean` change.

## 4. Tagless-final per-op datapath unification (strategic refactor)

Write each opcode's datapath once, polymorphic over a `HwVal`-style
interface; instantiate to `BitVec` (ISS exec) and `Expr` (circuit builder).
Most per-op R-MC square obligations become near-definitional
(parametricity/`rfl`), collapsing the bulk of item 1's grind. What canNOT
unify — and must remain a two-sided refinement — is timing: issue/countdown/
retire pipelining and `cap_revoke`'s multi-cycle engine (that gap is the
theorem, not duplication). Discussed 2026-07-04; do this BEFORE hand-proving
the 25 squares, or not at all.

## Deferred / out of scope

FPGA bring-up; `Dp/Pdr` (until scaling demands); the Phase-3 logical
relation (T2′/T4′) on the µLog seed; spec-cycle epoch alternatives
(superseded by the wrapping `BitVec 32` decision, see `STATUS.md`).

## Operational notes (hard-won; keep)

- Agent worktrees need a fully-copied `.lake` seed or they rebuild the
  world (`cp -a .lake` then atomic swap; an interrupted copy leaves a
  broken cache). Agents should `git merge main --no-edit` before starting.
- Run emitters under `ulimit -v 25000000` — earlyoom kills whole process
  groups on this box and `--prefer`s `lnp64*`/`yosys` names.
- Baked SAT certificates go stale on ANY `Loom/Hw/Compile.lean` change,
  and `decide` will *disprove* them; regenerate via the untrusted cadical
  driver (`Loom/Dp/Solver.solve`). `ci.sh` does not currently build
  `Tests.Acc8Bmc` (item 3 fixes that).
- The SpecM sweep pattern has NINE worked instances (SlotGen, Budget,
  Inflight, Authority, Tombstone, GateStep, Hostage's chain kit, DFrame,
  DRel) — never write one from scratch.
- Audit policy: sorries only in `Machines/*/Theorems/` + `Wip` namespaces;
  `native_decide` banned; single `ImplementsStandard` axiom whitelisted.
  `lake exe audit` is the gate; `scripts/ci.sh` the full check.

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
- [ ] ★ **Axiom audit, printed.** Add a `lake exe axioms` (or extend `audit`) that prints
      the full axiom closure of each headline theorem (`#print axioms` per theorem,
      machine-collected). The paper's trust section should be generated from this, not
      hand-written. `ImplementsStandard` should be the only non-kernel axiom listed.
      *(PARTIALLY IN HAND: `lake exe audit` already enforces the single-axiom
      whitelist and per-theorem sorry-cone tracking; the delta is printing the
      per-theorem axiom closures.)*
- [ ] **State `ImplementsStandard` precisely and minimally.** Reviewers will read this
      axiom character by character. Ensure it quantifies over exactly the µVerilog subset
      you emit, not "the Verilog standard" broadly. Consider splitting it if it currently
      bundles simulator + synthesizer assumptions.
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
      LRAT dual-checker crosscheck. Missing: the lockstep scripts and
      `Tests.Acc8Bmc` aren't in it, no golden diff, never timed from cold.)*
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
      downloaded `.v` matches the kernel-checked bytes (the round-trip `#guard` story).
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
      kernel-checked, with a one-axiom TCB to physical reality." Everything not
      serving that claim moves to future work or paper #2.
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
