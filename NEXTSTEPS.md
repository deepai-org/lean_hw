# NEXT STEPS - active plan as of 2026-07-14

Current state: T1-T9 CLEAN (49/49 ledger), RTL corroborated (iverilog +
yosys + SAT crosscheck, pinned tools, one-command `reproduce.sh`), R-MC
down to ONE audit-legal sorry (`square_retire`): `coupled_step` CLEAN,
3 of 4 cycle arms CLEAN, retirement infrastructure complete, 16 of 25
op arms + the decode-failure fallback proven. The project is one
theorem (§1) plus packaging (§P2 remainder) from its headline claim.
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

Remaining (the deep tail): `cap_dup` /
`mem_grant` (cap install — needs an install-vs-watched-refs argument or
a Coupled clause that Mover job refs stay live/dead-stable under
installs), `cap_drop` / `gate_call` / `gate_return` (kill sets + gate
faces), and
`cap_revoke` (mark-engine convergence + rv `Coupled` clause). Then the
25-way opcode dispatcher inside `square_retire` (case on
`extractLsb' 0 6`; the not-in-table branch routes to
`square_retire_illegal` via `decode_eq_find`).

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

## 1. R-MC endgame — the retirement tail (single remaining sorry)

Target: close `square_retire` (the sole repo sorry, `RMC.lean`). All
infrastructure exists; what remains is exactly enumerable. Work order
(revised 2026-07-14, late — dispatcher first, revoke spike second):

1. **DONE 2026-07-15.** (dispatcher wired; 9 leaf sorries.) Rewrite `square_retire` as a
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
3. **Tier 1 — pattern extensions** (one session each, recipe = the `sw`
   arm): `map`/`unmap` (region-edit face: `mapSet`/`unmapSet` fire, so
   an Inert-minus-map variant plus `rgnVPostE`/`rgnValPostE` selected
   forms; region-face `absDom` variant like `absDom_regpcbud`), then
   `move` (job install: `newJobSet` fires; `postJ` selected forms; the
   mover-field face shows the installed job).
4. **Tier 2 — the install invariant** (`cap_dup`, `mem_grant`): an
   install must not flip a Mover-watched ref dead→live. First check
   whether T3's `MoverLiveMem`-class spec invariants (available through
   the arm's `hsr` reachability hypothesis) already give it; only add a
   `Coupled` clause if not. Then the two arms (cap-table face variant
   of `absDom`, errno ladders via the monad-unfold technique).
5. **Tier 3 — kill machinery** (`cap_drop`, `gate_call`,
   `gate_return`): `killedByCoreE` fires for real. Shared kill-variant
   of the Mover faces (watched-ref liveness *after* the kill sweep =
   spec `moverPhase` on the post-kill state), plus the gate
   save/restore faces for call/return (`absGate` variant exposing the
   activation fields).
6. **Tier 4 — `cap_revoke`**: prove the clause from step 2 (rvInit
   seeds, rvStep preserves through the countdown, retirement reads the
   converged marks = spec `marks` closure in ≤ 7 doubling rounds), then
   the arm.
7. **Assembly**: delete the leaf sorries; `square`/`abs_run`/`refines`/
   `invariant_transport` flip CLEAN. Full gate + STATUS/ledger update.

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
      golden `.v` diff (blocked on the rtl/ tracked-vs-regenerated decision),
      never timed from a truly cold clone.)*
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
