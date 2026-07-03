# Session Report — 2026-07-03 (updated, second stretch)

Scope: the Loom charter (`readme.md`) and `PLAN.md`. This report records what the
continuing session accomplished, what remains, and where the genuine blockers are.
Every completion claim is Lean-kernel-checked (`lake exe audit`); the flip side is
that nothing is claimed done that isn't.

Repository state at time of writing: **green build, audit clean, 44 CLEAN ledger
theorems**; full CI (`scripts/ci.sh`) and the Acc8 hardware lockstep pass.

---

## 1. Accomplished this stretch

### 1.1 The T-theorem program is essentially complete

**CLEAN (kernel-checked, standard axioms only):** T1 (complete), **T2 complete**
(`step_confined`, `authority_confined` — the `KindsLe`/`Dominated` authority sweep),
**T3 complete including the crown jewel** (`gen_monotone` → `no_resurrection` →
**`revoke_temporal_safety`**: after a retiring `cap_revoke`, no agent ever writes
under any marked descendant, forever — via the `Evo`/`RefFate`/tombstone relation and
two new machine invariants, `ClassLineage` and `MoverLiveMem`), **T4 complete**
(scrub equalities + the frame theorem via the `Touch`/`CalmLe` whole-cycle
characterization), **T7 complete** (`wcet_retirement` via the `InflightEq` sweep;
`budget_delivery`), **T8 complete** (`wx_machine_wide`, `status_word_safety`,
`prior_holder_excluded`), **T9 complete** (`ledger_balanced`, `budget_bounded` via
the `BudgetLe` sweep), plus A1, A-R, A-EV (below).

**STATED (in progress):** T5 `noninterference` — the two-run aligned-instant
stuttering simulation is fully assembled; five cycle-level engine lemmas remain
(Wip-sorried, precisely itemized). T6 `no_hostage` — statement repaired three times
(see §1.2), sorry-free scheduler/progress/potential bricks landed; the final
counting assembly remains.

### 1.2 Proof-forced findings (the charter's predicted class) — seven this stretch

1. **T8 retired-vs-dead**: `prior_holder_excluded` was false with `liveRef = false`
   (a dead-but-not-retired ref can be re-installed at the same generation); the
   faithful hypothesis is *retired* (`r.gen < slotGen`).
2. **T2 narrow wraparound (machine-checked counterexample)**: a zero-length narrow
   at exactly the end of memory wrapped the 12-bit base to 0, minting authority
   outside the roots' closure while remaining `Wf`. Fixed with a no-wrap `require`
   in `narrow` (semantics change, PLAN §8b).
3. **T6 starvation**: a legal top-priority hog (`Q = P`) starves the serving chain
   forever; `resumeBound` had no interference term → `StrictlySchedulable`.
4. **T6 occupancy ≠ charges**: an issue of cost c occupies c+1 cycles but charges c
   → occupancy factor in the utilization bound.
5. **T6 residual-budget stall-lock**: the core's stall arm spends nothing and
   re-picks the same underfunded domain forever — unbounded priority inversion in
   the frozen scheduler. v1: explicit `StallFree` hypothesis; scheduler redesign
   filed as PLAN D11.
6. **T5 three leak channels**: scheduler starvation freezes the destuttered
   trajectory in one run only; `mem_grant` installs into the isolated domain's
   table without consent (register-visible via later handle values); the isolated
   domain's own `mem_grant`/`move` read global state into rd. Fixes: `TopPriority`
   hypotheses, `Isolated.slots_full`/`code_local`/`wx_disjoint`, observation
   projected to regs/pc/run/cause (budget provably drifts).
7. **T3 gate-class gap**: `revoke_temporal_safety`'s hypotheses admit a live
   gate-class handle (revoke then destroys nothing); the theorem survives only via
   the new `ClassLineage` + `MoverLiveMem` invariants.

### 1.3 Phase 2 — the silicon path is now real for both machines

- **Acc8 chain closed end to end, kernel-checked**: spec ⊑ EDSL core (**A-R**),
  core ≃ compiled µVerilog module (**A-EV**, register AND memory halves of the
  generic emission theorem proved — `compile_cycle_regs`, `compile_cycle_mems`),
  µVerilog **parser + round-trip** (`parseCheck` soundness; a kernel-`decide`d
  full-grammar demo; byte-level `#guard` regression on the emitted `rtl/acc8.v`),
  and iverilog/yosys corroboration (`scripts/lockstep_acc8.sh`). The trusted base
  remains the Lean kernel + the single `ImplementsStandard` axiom.
- **Multi-port memories (`wrPorts`)**: Loom extension driven by the µ Mover's
  same-cycle dst+status writes (Rule 2); per-port compiler folds with the memory
  half of the emission theorem re-proved generically over port lists;
  3-port collision kernel test.
- **LNP64-µ core in the EDSL (task 1.11), base half**: full state encoding
  (633 registers, DESIGN.md naming/packing contract), `abs`, refill/scheduler/
  issue/retire/halt-unwind circuits, all 14 base ops; **256-cycle full-state
  lockstep vs the ISS is green**. System-op + Mover circuits and `rtl/lnp64u.v`
  emission are in flight (see §2).
- **µLog seed (L1)**: generic BI core (`Pcm`/`Prp`, sep/wand adjunction laws),
  step-indexing (`later`, Löb induction), and the µ resource-algebra instance
  wired to T9's conserved quantities.

### 1.4 Phase 3 — L2 proof engines

- **`Loom/Dp/Cert/Check.lean`**: in-house, kernel-reducible RUP/LRAT checker with
  a full soundness proof (`check_sound → CNF.Unsat`), axioms `[propext, Quot.sound]`.
  Real D2 numbers (cadical certs under plain kernel `decide`): php4 ≈ 0.2 s,
  php5 ≈ 1.5 s, php6 ≈ 13.5 s, php7 ≈ 4.5 min — **D2: go**, budget ~10²–10³
  solver-LRAT steps per query.
- **`checker/`**: the independent second checker — a standalone Lake package
  (zero Loom/Machines/Mathlib imports, own CNF/LRAT types, full deletion
  support) with a `chk` CLI, cross-validated against the Loom leg on cadical
  proofs plus a mutation-rejection matrix; CI-wired with solver-absent skip.
- **BMC/k-induction** (`Dp/Cnf, Solver, Bmc, KInduction`) are in flight.

### 1.5 Earlier in this same continuing session

The L1 capability-safety invariant `wfa_invariant` (`Wf ∧ Acyclic` for every
reachable state, all 25 opcodes, no hypotheses, no sorry) — see STATUS.md for the
full account, including `marks_fixpoint`, `acyclic_reparent_sibling`, and the
`transferCap` verification core.

---

## 2. Remaining work

1. **T6 assembly** (in flight): the lex-measure/potential counting argument on top
   of the landed bricks.
2. **T5 engine lemmas** (in flight): five Wip cycle-level sweeps
   (`insulated_step`, `frame_step`, `retire_step_lockstep`, `progress`, `issue_step`).
3. **LNP64-µ core completion** (in flight): the 11 system-op circuits (including
   the unrolled 64-iteration revoke marking fixpoint), the Mover rule on write
   ports 1/2, full-ISA lockstep, `rtl/lnp64u.v` emission + iverilog/yosys.
4. **BMC/k-induction** (in flight): Tseitin encoding with the `encode_sound`
   direction proved, cadical driver, first certificate-checked result on Acc8.
5. **R-MC** (LNP64-µ core ⊑ spec): by the 1-cycle-per-spec-cycle design this is a
   plain `Simulation` per field; statement lands with the completed core; the proof
   is the natural next major stretch (Phase 3).
6. **Scheduler redesign (PLAN D11)**: fix the stall-lock priority inversion in the
   machine and re-run the (mechanical) invariant stack; would let T6 drop the
   `StallFree` hypothesis.
7. FPGA bring-up and hardware corroboration: **explicitly out of scope** this
   session (per direction); the flow stops at iverilog/yosys.

---

## 3. Blockers and honest caveats

1. **T6/T5 closure risk.** Both are genuine liveness/relational proofs; the
   remaining pieces are precisely itemized but nontrivial. If they don't close this
   session, the ledger will honestly show them STATED with sorry-free
   infrastructure beneath.
2. **The stall-lock is a real machine bug** (D11), not a proof artifact: the frozen
   scheduler admits unbounded priority inversion. T6 currently carries `StallFree`
   as an explicit hypothesis; the honest fix is a semantics change.
3. **Emission scale.** The unrolled revoke fixpoint makes `rtl/lnp64u.v` large;
   yosys runtimes/cell counts will be reported as measured, and the DESIGN.md
   records the multicycle-marking optimization path if needed.
4. **checker/ divergence note**: Std's LRAT checker does full propagation and so
   accepts one hint-dropping mutant the strict checker rejects (both sound); noted
   in the crosscheck script.

## 4. Where to resume

1. Land the four in-flight branches (T6, T5 engines, core completion, BMC).
2. R-MC statement + proof for the completed core.
3. D11 scheduler change + re-verification sweep; then drop `StallFree` from T6.
4. Phase 3 logical relation (T2′/T4′) on the µLog seed; PDR as scaling demands.
