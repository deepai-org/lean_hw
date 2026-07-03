# Session Report — 2026-07-03

Scope: the Loom charter (`readme.md`) and `PLAN.md` — a machine-generic verified-processor
toolchain in Lean 4, LNP64-µ as the first modeled machine. This report records what this
session accomplished, what remains, and where the genuine blockers are.

Repository state at time of writing: **green build (741 jobs), audit clean**, all work
committed to `github.com/deepai-org/lean_hw`.

---

## 1. Accomplished

### 1.1 The L1 capability-safety invariant — complete, unconditional, sorry-free

The central Phase-1 deliverable. `wfa_invariant` (`Machines/Lnp64u/Logic/AcyclicWfa.lean`)
proves that **every reachable machine state satisfies `Wf ∧ Acyclic`**, across all 25
opcodes (14 base + 11 system), with no hypotheses and no `sorry`:

- `#print axioms` = `[propext, Classical.choice, Quot.sound]` — Lean-kernel-verified.
- Route: `system_preserves_wfa` (all 11 system ops) → `ExecPreservesWfA` →
  `retire_preserves_wfa` → `corePhase_preserves_wfa` → `step_wfa` → `wfa_invariant`.
- The hard cases done in full: **cap_drop** (reparent/orphan + clearSlot + sweeps),
  **cap_revoke** (bulk mark-and-destroy), **gate_call** / **gate_return** (activation
  bookkeeping routed through the capability-transfer core `transferCap`).

Supporting theory built from scratch this session:

- **Acyclicity theory** (`Acyclic.lean`, `AcyclicExec.lean`, `AcyclicPhase.lean`):
  `climb`/`parentRef` lineage-following, `NoCycle`, preservation through every state
  operation.
- **Two novel lemmas**:
  - `marks_fixpoint` — the revoke sweep's mark set saturates (Finset-counting argument:
    `markStep` is monotone + inflationary, marked count strictly increases until stable,
    bounded by `numDomains × numSlots`).
  - `acyclic_reparent_sibling` — a relabeling function ψ collapsing `new ↦ old` commutes
    with `climb`, so sibling reparenting preserves acyclicity.
- **The capability-transfer core**: `wf_transferCap`, `acyclic_transferCap`,
  `transferCap_frame`, `transferByHandle_preserves`.

### 1.2 Three proof-forced design findings

The charter predicts formalization will force invariant strengthenings; three occurred
(each recorded in `STATUS.md` and project memory):

1. **Acyclicity bound** — the chain-depth bound must be `numDomains × numLineage`
   (cross-domain), not per-domain.
2. **cap_drop Wf↔Acyclic coupling** — cap_drop's Wf preservation is unprovable without
   acyclicity (the Wf-only obligation `system_preserves` is dead/superseded); the combined
   invariant is the correct statement.
3. **gate_saved_none** — `Wf` needs the clause `∀ g a, (gates g).act = some a →
   a.savedServing = none` (activations never stack in µ); without it `gate_return`'s
   serving-restore is unprovable. Added to `Wf` and re-discharged in all ~25 op proofs.

Also proof-forced (found while stating T3/T8): `transferCap` must sweep regions/mover
after the move, else the giver retains cached authority over the moved range.

### 1.3 T-theorems discharged (2 of 9 → plus one nearly complete)

- **T9 `ledger_balanced`** — lineage ledger balances in every reachable state, via a
  `Finset.card_bij` bijection between derived caps and occupied cells
  (`LedgerBalanced_of_Wf`, from the invariant). Unconditional.
- **T8 `wx_machine_wide`** — W^X machine-wide, discharged from `wfa_invariant`
  (dropped its former `ExecPreservesWf` hypothesis). Unconditional.

### 1.4 gen_monotone (T3) — infrastructure complete, dispatch 9/11

`gen_monotone` (slot generations never decrease across `step`) unlocks T3 temporal safety
(`gen_monotone_n` and `no_resurrection` are already proven modulo it). Built this session
in `Machines/Lnp64u/Logic/SlotGen.lean`:

- **`SlotGenLe` combinator** — SpecM-level monotonicity, mirroring `PreservesAcyclic`:
  `of_preservesGen`, `pure`, `bind`, `iteBool`, `reg`, `raise`, `require`, `load`,
  `setReg`, `updDomPc`, `store`, `demand`, `get`, `narrow`, `capLive`, `updDomGen`,
  `allocDerived`.
- **`base_slotGen_le`** — all 14 base opcodes proven.
- **Kernel bounds** — slotGen is written in exactly two places (`clearSlot`,
  `destroyMarked`), both via `bumpGen`: `clearSlot_slotGen_ge`,
  `destroyMarked_slotGen_ge`, plus composite bounds `clearSlot_sweeps_slotGen_ge`
  (cap_drop core) and `destroyMarked_sweeps_slotGen_ge` (cap_revoke core), and
  preservation lemmas (`haltDom_slotGen`, `installDerived_slotGen`, `reparent_slotGen`,
  `sweepMover_slotGen`, `setDom_slotGen_of`).
- **`transferCap_slotGen_ge`** — the gate-op kernel core never lowers slotGen (just
  completed, builds green).
- **Phase reduction** — `step_slotGen_reduce`: step's slotGen equals
  `corePhase (refillPhase σ)`'s (mover phase and cycle bump leave domains untouched).
- **`system_slotGen_le` dispatch: 9 of 11 ops done** — cap_dup, cap_drop, cap_revoke,
  mem_grant, map, unmap, move (via `move_slotGen_le`, mirroring `move_ok`/`move_err`),
  yield, halt. In the audit-permitted `Wip` namespace with 2 sorries remaining
  (gate_call, gate_return).

### 1.5 Session-earlier context (same continuing session)

Phase 0 and the Phase-1 skeleton predate this stretch: machine-generic `Loom` core
(SpecM, machine/manifest, Invariant), the full LNP64-µ ISA (25 opcodes with semantics,
cost model, prose), `init_wf`, phase lemmas, the audit executable, and STATUS tracking.

---

## 2. Remaining work

### 2.1 Immediate (Phase 1, mechanical from here)

- **`system_slotGen_le`: gate_call + gate_return** — the last two dispatch cases. Both
  route through `transferByHandle` → `transferCap`; `transferCap_slotGen_ge` (done) is
  the hard kernel piece. What remains is threading each gate op's exec prefix
  (requires/gate-config reads/depth check) exactly as their Wf proofs did — fiddly
  (the gateDepth match-motive issue returns) but established-pattern work.
- **`corePhase_slotGen_ge` + `gen_monotone`** — lift the exec bound through retire →
  corePhase, compose with `step_slotGen_reduce`. Then **T3 temporal safety**
  (`gen_monotone_n`, `no_resurrection`) discharges immediately.

### 2.2 Phase 1: remaining T-theorem bodies (each ~150–400 lines, sorried)

| Theorem | Content | Character |
|---|---|---|
| T2 | `step_confined`, `authority_confined` | per-op frame analysis over exec |
| T4 | `activation_entry_scrubbed`, `caller_resumption`, frame | gate-op operational detail |
| T5 | noninterference | two-run relational proof — hardest remaining |
| T6 | `no_hostage` | liveness-flavored, needs budget/refill reasoning |
| T7 | `wcet_retirement`, `budget_delivery` | cost-model accounting |
| T8 | `prior_holder_excluded`, `status_word_safety` | from invariant + transfer frame |
| T9 | `budget_bounded` | refill-phase budget ≤ quota, near-mechanical |

The completed L1 invariant is the correct foundation for all of these — each is now a
matter of per-cycle operational reasoning above it, not new invariant discovery.

### 2.3 Phases 2–4 (not started; multi-person-scale per the charter)

- **Phase 2**: µLog (the HDL subset) and its logical relation to the spec; the pipeline
  model; the memory-port emission half.
- **Phase 3**: the L2 proof engines; the second (independent) checker.
- **Phase 4**: FPGA bring-up and hardware corroboration of the verified core.

---

## 3. Blockers

1. **Charter scope vs. session scope (the fundamental one).** `readme.md` explicitly
   scopes Loom as a multi-phase, multi-person research program. "Fully implement
   PLAN.md and readme.md" is not achievable in any single session; the honest stopping
   state is maximal verified progress plus an accurate record (this file). Every
   completion claim in this repo is Lean-kernel-checked; the flip side is that nothing
   can be claimed done that isn't.
2. **Proof-labor scaling, not conceptual difficulty.** No remaining Phase-1 item is
   blocked on an unknown: the invariant, kernel bounds, and reduction lemmas exist. But
   each opcode case is 30–80 lines of exact syntactic threading (SpecM bind-casing per
   the `specM_bind`-expansion style), and Lean's dependent-match motives make shortcuts
   fail (`cases h : e` non-substitution; `let`-inlined matches breaking syntactic
   rewriting — twice worked around by extracting named defs, `gateDepth`/`gateCallExec`).
   This is throughput-bound, not idea-bound.
3. **T5 noninterference needs new machinery.** Unlike the others, it needs a two-run
   state relation (low-equivalence) and a simulation argument — the one remaining
   Phase-1 item that is design work, not threading.
4. **Phases 2–4 need artifacts that don't exist yet** (µLog definition, pipeline model,
   second checker, FPGA target) — they are green-field subprojects, not proofs over the
   current codebase.

---

## 4. Where to resume

1. Finish `system_slotGen_le` gate cases (use `gateCallExec`/`gateDepth` named defs;
   `transferCap_slotGen_ge` + `transferByHandle` threading).
2. `corePhase_slotGen_ge` → `gen_monotone` → T3 closes.
3. T9 `budget_bounded` (likely the cheapest remaining theorem: refill sets budget := Q,
   exec only decrements — mirror the slotGen combinator with a budget bound).
4. T2/T4/T8 residuals from the frame lemmas already in `ExecWf.lean`/`CapDropWfa.lean`.
5. T5 design (low-equivalence relation) before its proof.
