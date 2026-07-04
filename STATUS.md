# STATUS — LNP64-µ / Loom

## ★ 2026-07-04: SPEC MADE PHYSICALLY HONEST — `cycle` IS A WRAPPING `BitVec 32`; R-MC IS UNBOUNDED ★

D-class spec change (user decision): `MachineState.cycle : Nat` → `BitVec 32`, matching the
hardware's wrapping counter exactly. This resolves the R-MC uninhabitedness finding — with a
`Nat` counter the spec had no periodic points, so the unbounded simulation against the 32-bit
core was provably empty.

- **Proof-forced WF clause:** `Manifest.WF.period_dvd : ∀ d, periodP ∣ 2^32` (wrapping-timer
  periodicity — the refill cadence `cycle % P = 0` stays `P`-periodic across the wrap only
  under divisibility; same constraint real RTOS tick periods have). `hyperL_dvd_pow32`
  derived. All checked-in manifests already comply (periods 32/64).
- **Boot-skip guard removed** from `refillPhase` and `Hw.refillCondE` (`cycle ≠ 0` cannot be
  implemented against a wrapping counter — boot *is* indistinguishable from a wrap; the
  cycle-0 refill rewrites the boot quota, a no-op; the wrap boundary must refill).
- **Counter arithmetic single point of truth:** `step_cycle`/`stepN_cycle` are now `BitVec`
  equations (wrap silently); every window/boundary argument reduces to `Nat` mod-`P`
  arithmetic through the one bridging lemma `Hostage.stepN_cycle_mod` (uses `period_dvd`).
  T1–T9 statements unchanged; T6's counting stack re-proved with *simpler* proofs (the
  `cycle = 0` case splits vanished).
- **R-MC upgraded** (`Theorems/RMC.lean`): `abs_run` and `invariant_transport` are
  horizon-free (∀ n — through any number of wraps), and the unbounded simulation is landed:
  `refines : Nonempty (Simulation (machine m) (reachCore m))` with `Hw.abs` as the
  abstraction function, where `reachCore` is the core on its boot orbit (same states/reset/
  reachable set as `(core m).toTSys` — `reachCore_reachable_iff`; `invariant_pullback`
  restates transport on the full core). The old `hwrap` side conditions on
  `square`/`coupled_step` are gone; the same 4 audit-legal sorries remain
  (`absDom_reset`, `coupled_reset`, `square`, `coupled_step`).
- `Hw.abs` maps the cycle register **verbatim** (was `.toNat`); `Hw/` otherwise unchanged.
  Both Lnp64u lockstep tests (256-cycle base + 2000-cycle system, full state) still pass;
  full `lake build` green; audit clean with no ledger regressions.


## ★★ 2026-07-04: THE LEDGER IS FULLY CLEAN — ALL 49 THEOREMS, T1–T9, ZERO STATED ★★

`lake exe audit`: **49/49 CLEAN, zero STATED entries.** The last two fell this session:

- **T5 (`noninterference`, `sim`, `catchup_halt`, `catchup_retire`)** — the four engine
  lemmas (`insulated_step`, `frame_step`, `retire_step_lockstep`, `progress`) closed via two
  new sweeps: `Logic/DFrame.lean` (unary d-frame: `DCtx`/`DKeep`/`DKLe` over all 25 ops +
  `DSelf` for d's own `code_local` retirements) and `Logic/DRel.lean` (two-run relational:
  `RC` coupling, 21-op `exec_rel`, `retire_rel`). No statement changes — the adjudicated
  signatures survived verbatim.
- **T6 (`no_hostage`)** — proved bottom-up: whole-cycle chain classification
  (`corePhase_chain` atop the `ChainOut`/`GateCallShape`/`GateReturnShape` sweep in
  `Logic/Hostage.lean`), the serving chain as a deterministic relation with head uniqueness
  (`Logic/HostageChain.lean`), the radix lex measure with chain surgery
  (`Logic/HostageMeasure.lean`), per-shape foreign-cycle frames (`Logic/HostageFrame.lean`),
  and the potential/window counting `cycle_master → drain → window → resume_of_measure`
  (`Logic/HostageCount.lean`). One T6-owned constant honestly adjusted:
  `interferenceWindow` (endpoint counting certifies `n/P + 2` refill boundaries per window,
  and the origin-funding wait is absorbed); the `no_hostage` statement is unchanged.

Also this session: the previously-unverified **2000-cycle full-state system-op lockstep
passed** (Phase 2 claim below is now verified), and `lake exe emit lnp64u` was fixed from a
115 GB memory blowup (pointer-memoized compile + structural hash-consing in the printer)
with the emitted RTL passing the 2000-cycle iverilog ISS-golden sim and yosys synth clean
(1.57M cells — 1.43M mux, 7,849 FFs ≈ the 633 registers' state bits, RAM kept as `$mem_v2`;
emit now 11 s / <1 GB; `rtl/` stays untracked, regenerate via `scripts/lockstep_lnp64u.sh`).
R-MC (transport of T2–T9 onto the emitted core) is stated and in progress in
`Theorems/RMC*.lean`.

---

## ★ L1 CULMINATION: the machine-wide `Wf ∧ Acyclic` invariant is UNCONDITIONALLY PROVEN ★

`wfa_invariant (m : Manifest) (hwf : m.WF) : (machine m).Invariant (fun σ => Wf σ ∧ Acyclic σ)`
holds for **every reachable state**, with **no hypotheses** beyond a well-formed manifest and
**no `sorry`** — `#print axioms wfa_invariant` = `[propext, Classical.choice, Quot.sound]` (the
standard axioms only). All **11 system opcodes** (cap_dup, cap_drop, cap_revoke, mem_grant, map,
unmap, gate_call, gate_return, move, yield, halt) and all **14 base opcodes** preserve the combined
invariant: a well-formed capability table with an acyclic lineage forest. This is the L1
capability-safety result the charter's Phase 1 targets.

Proof-forced findings surfaced and fixed along the way: the acyclicity bound unsoundness, the
cap_drop Wf↔Acyclic coupling, and `Wf.gate_saved_none` (activations never stack in µ). Novel lemmas:
`marks_fixpoint` (Finset-counting saturation), `acyclic_reparent_sibling` (relabeling-commutes-with-
climb), plus the complete transferCap verification machinery.

**T-theorems grounded on the invariant (this session):** T9's `ledger_balanced` (via
`LedgerBalanced_of_Wf`, a `Finset.card_bij` from the DomWf bijection) and T8's `wx_machine_wide`
(machine-wide W^X, now unconditional) both follow from `wfa_invariant`. Remaining T-theorem bodies
(T2 confinement, T3 `gen_monotone`→temporal safety, T4 frame/scrub, T5 noninterference, T6 no_hostage,
T7/T9 budget) are per-cycle operational proofs over the semantics, each with the L1 invariant now
available as their foundation.

(The 5 remaining sorries in `SystemOpsWf.system_preserves` are the *superseded* standalone Wf-only
obligation — not used by `wfa_invariant`, which routes through the combined `system_preserves_wfa`.)

---

## Phase 2: the LNP64-µ EDSL core is COMPLETE (task 1.11)

All 25 opcode circuits (14 base + **all 11 system ops**), the Mover rule
(multi-port memory: core store port 0, Mover data port 1, status port 2 —
one syntactic write per port, so `MemWriteWF` holds by construction), and
emission. `cap_revoke`'s marks fixpoint runs as a **pointer-doubling engine
in hidden registers** across the in-flight countdown cycles (the naive 64×
combinational unroll is unrepresentable without expression sharing —
recorded in `Machines/Lnp64u/Hw/DESIGN.md`). Verified by full-state
per-cycle lockstep against the spec: the base manifest (256 cycles) plus a
system-op manifest exercising every system opcode, incl. a revoke of a
cross-domain-granted tree aborting an in-flight Mover transfer (2000
cycles) — `Tests/Lnp64uCore.lean`. Emission: `lake exe emit lnp64u` +
`scripts/lockstep_lnp64u.sh` (iverilog ISS-golden lockstep + yosys synth;
standalone, deliberately not in `ci.sh`).

---

# Status

Honest, mechanically-checked state of the build. Regenerate the theorem
counts with `lake exe audit`; run `scripts/ci.sh` for the full gate.

> **Update:** `wf_orphanChildren` and **`dropCore_preserves`** are PROVED. `dropCore_preserves` assembles every `cap_drop` lemma into one: the dispatch (reparent-or-orphan) + `clearSlot` + sweeps preserves **both `Wf` and `Acyclic`**. `cap_drop`'s entire mathematical content is now proven; what remains to formally wire it is (a) the `capLive → dropCore` monadic thread and (b) the invariant plumbing — threading `Acyclic` through the L1 chain (`ExecPreservesWf` → phase lemmas → `step_wf` → `wf_invariant`) as a combined `Wf ∧ Acyclic` invariant, which needs `Acyclic` preservation for the other ops (free for non-lineage ops via the now-proved `acyclic_setDom`/`acyclic_write` — every register/PC/region/budget/schedule update and memory write; **the entire L1 acyclicity threading is complete** — `wfa_invariant` proves the combined `Wf ∧ Acyclic` invariant (reduced to `ExecPreservesWf` + `ExecPreservesAcyclic`), via `acyclic_step` and the per-phase lemmas (`acyclic_refillPhase`/`corePhase_preserves_acyclic`/`acyclic_moverPhase`/`acyclic_setCycle`, `retire_preserves_acyclic`). And **every per-op Acyclic lemma is proved**: `acyclic_clearSlot`/`acyclic_orphanChildren`/`acyclic_reparent`/the sweeps (revocation), `acyclic_setDom`/`acyclic_write` (non-lineage), and `acyclic_installDerived` (derivation — a fresh-leaf argument via `acyclic_add_leaves`, no counting). This became clean after **redefining `Acyclic` as genuine acyclicity** (`NoCycle`: no reference returns to itself) — which also removed a latent unsoundness in the earlier bound-based definition (cross-domain derivation via `mem_grant` makes chains exceed one domain's `numLineage`). Every transport signature was preserved, so `dropCore_preserves` and all downstream rebuild verbatim). **DONE:** the combined `Wf ∧ Acyclic` invariant is threaded end-to-end — `PreservesAcyclic`
combinator, `base_preserves_acyclic` (all 14 base ops), `execPreservesAcyclic_of_system`
(reducing `ExecPreservesAcyclic` to `SystemOpsPreserveAcyclic`), the phase lemmas, and
`wfa_invariant`. The combined invariant now rests on exactly `SystemOpsPreserveWf` +
`SystemOpsPreserveAcyclic`. **Architectural note the formalization forced:** `cap_drop`'s
*Wf* clause itself needs `Acyclic` (its reparent branch's no-dangling-ref obligation uses
`Acyclic.parentRef_ne`), so the two invariants cannot be proved independently for the
revocation ops — the system-op obligation must be the *combined* `Wf ∧ Acyclic → Wf ∧ Acyclic`.
**`cap_drop` is now FULLY DISCHARGED** — `capdrop_preserves_wfa` proves it preserves the
combined `Wf ∧ Acyclic` by threading `capLive → dropCore_preserves`. The first (and hardest)
revocation opcode is a kernel-verified theorem. Remaining for the combined invariant: the
7 non-revocation ops' `Acyclic` clauses (trivial for the non-lineage ops; `acyclic_installDerived`
for `cap_dup`/`mem_grant`), assembling `SystemOpsPreserveAcyclic`, and the mechanical refactor
threading the combined obligation into `wfa_invariant`. **`cap_revoke`'s Acyclic core is now proved** (`acyclic_destroyMarked` — bulk removal is
edge-removal, so acyclicity survives via `acyclic_of_parentRef_le`); its Wf core
(`wf_destroyMarked`, the bulk lineage-bijection lemma) remains. The gate ops (`gate_call`/
`gate_return`) need `transferCap`'s preservation — a fresh-leaf install + sibling-reparent +
`clearSlot` + sweeps, the most intricate remaining Acyclic core. Then each of the three
remaining ops is finished by its own `capLive → …` thread, exactly as `cap_drop` was.

> **Update:** `system_preserves_acyclic` now proves **9 of 11** ops' Acyclic clauses ops' Acyclic clauses (cap_drop, cap_dup, mem_grant via `acyclic_allocDerived`; map/unmap/yield/halt/move via the combinator + threading). Only **cap_revoke and the 2 gate ops** remain — exactly the 3 that need the hard kernel lemmas `wf_destroyMarked`/`transferCap`. `acyclic_destroyMarked` (cap_revoke's Acyclic half) is already proved. **The combined obligation `system_preserves_wfa` is now proved** (`SystemOpsPreserveWfA`,
8 of 11 ops: cap_drop via `capdrop_preserves_wfa`, the other 7 by pairing each op's Wf
proof with `system_preserves_acyclic`). **DONE — the combined invariant is now machine-wide:** `wfa_invariant_of_system` proves
`Invariant (Wf ∧ Acyclic)` reduced to exactly one obligation, `SystemOpsPreserveWfA`, via
`ExecPreservesWfA` and the combined phase lemmas (`retire_preserves_wfa`,
`corePhase_preserves_wfa`, `step_wfa`). **`cap_drop` is fully proven in the reachable-state
invariant.** The entire invariant now rests on `system_preserves_wfa` (**9 of 11 ops proved**);
**`cap_revoke` is now fully discharged** (`wf_destroyMarked_sweep` via the marks-fixpoint
saturation `marks_fixpoint`/`marks_closed`). Only the **2 gate ops** (`transferCap`) remain as
that single obligation's sorries.

**Gate-ops path (mapped this session).** Both `gate_call`/`gate_return` route through
`transferByHandle` → `transferCap` (install-at-recipient + `reparent oldRef newRef` +
`clearSlot from_ s` + sweeps), then update gates/serving/run/blocked. The concrete lemmas:
(1) **install-move Wf** — install a fresh slot/cell holding the *moved* cell (parent =
original cell's parent, live by `Wf.parent_live`); analogous to `wf_installDerived` (~150
lines). (2) **transferCap Wf composition** — `wf_reparent` (newRef live) + `reparent_no_ref`
(no cell points to oldRef) → `wf_clearSlot_sweep` (~50 lines; all pieces exist). (3)
**reparent-to-fresh-sibling acyclicity** — `parentRef newRef = parentRef oldRef` with newRef
fresh; distinct from `acyclic_contract` (which needs `parentRef oldRef = newRef`), needs a
new climb argument (~100 lines). (4) **gate-consistency Wf** for the activation updates
(gate_serving/serving_gate/blocked_gate) in each gate op (~150 lines each).

**Progress (this session):** all transferCap building blocks + the Wf core are now proved —
`acyclic_reparent_sibling` (novel), `setDom_installMove_parentRef`, `wf_installMove`,
`wf_installCapNone`, `wf_reparent_clear_sweep`, and **`wf_transferCap`** (the full Wf, both
lineage cases). **`acyclic_transferCap` and `transferByHandle_preserves` are now also proved** — the entire
capability-transfer core (transferCap preserves `Wf ∧ Acyclic`, and the `transferByHandle`
wrapper) is complete, with no kernel lemmas left. **gate_return is fully proved and wired (10 of 11 combined ops).** `gate_call`'s gate-consistency
core `wf_acyclic_gateCall` is also fully proved (installing the activation / activating the callee /
blocking the caller preserves `Wf ∧ Acyclic`, using `gate_saved_none`), along with `gateCallExec`,
`require_cond`, `transferCap_frame`, `transferByHandle_frame`. Only `gate_call`'s exec-threading
remains — connecting `gateCallExec` to `wf_acyclic_gateCall` through the 5-require chain — which is
blocked on a finicky Lean reduction of the `require`-chain + inlined `depth`-match (a tactics
mechanics issue, not a math gap; the `require5` condition term resists syntactic rewriting).

The earlier remaining piece for the gate ops
is the **gate-activation consistency**: the gates/serving/run/blocked updates in
`gate_call`/`gate_return` must preserve `gate_serving`/`serving_gate`/`blocked_gate` (the gate
chain bookkeeping) — intricate but needs no new kernel machinery.

**Proof-forced finding (this session):** `gate_return` restores `c.d.serving := act.savedServing`,
so `serving_gate` needs `savedServing`'s consistency. In µ, `savedServing` is always `none`
(gate_call requires `cal.serving.isNone`), making `serving_gate` vacuous after return — **but the
current `Wf` does not state this**, so it's unusable in the proof. The invariant needs a new
machine-level clause `gate_saved_none : ∀ g a, gates(g).act = some a → a.savedServing = none`.
Adding it: strengthen `wf_of_skeleton`'s `hact` to also carry `a'.savedServing = a.savedServing`,
then discharge the clause in each direct Wf constructor (mechanical — gates unchanged for ~13 ops;
`gate_call` establishes it from its require). This is the same proof-forced pattern as the
acyclicity-bound and cap_drop-coupling findings earlier this session — the formalization forcing a
real invariant strengthening. It is the concrete unblocker for both gate ops.

**DONE:** the `gate_saved_none` clause is now added to `Wf` and discharged in all ~15
constructors (`wf_of_skeleton`'s `hact` strengthened to carry `savedServing`; the `haltDom`
unwind clears the activation; `init_wf` vacuous). Green build (742 jobs), audit clean. This
unblocks the gate ops' Wf — with `c.d.serving` restored to `none`, `gate_return`'s `serving_gate`
is vacuous, and the gate-consistency case analysis (a domain serves/blocks at most one gate, from
`serving_gate`/`blocked_gate`) closes. The remaining gate-op work is now purely the combined
`Wf ∧ Acyclic` threading of `gate_call`/`gate_return` — `transferByHandle_preserves` + the
gate/serving/run updates — with every supporting lemma in place. — exactly parallel to how the Wf-only invariant rested on
`SystemOpsPreserveWf`. `acyclic_destroyMarked` (cap_revoke's Acyclic half) is already done.

## What builds and runs (verified end to end)

- **`lake build`** — the whole stack compiles: Loom toolchain (Core, Isa, Dp,
  Hw, Emit, Book, Logic), two machines (Acc8, LNP64-µ), tools, tests.
- **`lake exe iss`** — boots Acc8's golden program and LNP64-µ's four-domain
  demo manifest, prints the frozen lockstep trace; final states match the
  checked-in goldens (`Tests/`).
- **`lake exe emit`** → `rtl/acc8.v` — the Acc8 core compiled through the
  EDSL→µVerilog compiler. **iverilog** simulates it to the ISS golden
  (`acc=40, mem[3]=40, halted=1`); **yosys** synthesizes it to 704 cells,
  0 problems. `scripts/lockstep_acc8.sh` re-checks this.
- **`lake exe bookgen`** → `book-out/{lnp64u,acc8}.html` — both ISA books as
  projections of the `isa` arrays.
- **`lake exe audit`** — the CI gate: walks the ledger, enforces the sorry
  policy, the µVerilog-boundary axiom whitelist, the `native_decide` ban
  (Rule 1), and the `Loom`-never-imports-`Machines` DAG (P0). It also prints
  the raw axiom closure for each ledger theorem, so the CLEAN/STATED verdicts
  are auditable from the command output.

## Theorem ledger (from `lake exe audit`)

**Proved clean** (kernel-checked, standard axioms only):

- **T1 (complete)** — decode totality + determinism over all 25 opcodes,
  assemble∘disassemble identity, operand preservation, coverage/refusal,
  errno ABI bound, handle round-trip, null-handle unconstructibility.
- **A1 (complete)** — Acc8's T1 analog.
- **T2.init_confined** — boot authority ⊆ manifest roots.
- **T9.init_balanced** — boot lineage ledger balances.
- **Inv.init_wf** — the whole machine well-formedness invariant holds at boot
  (all 8 machine-wide + 6 per-domain conditions), resting only on `step_wf`.
- **T6.totality** — the machine is total and deterministic.
- **Loom.Hw.Compile.compileExpr_eval** — emitted combinational logic evaluates
  to the source expression (full induction).
- **Loom.Hw.Compile.nextReg_correct** — the register-fold keystone: the compiled
  next-value mux tree evaluates to the value the design's action writes (last
  write wins), by induction on actions. This is the core of C-HW/E-V; the
  emission theorems now reduce to assembling it over the register/memory folds.
- **Loom.Hw.Compile.rules_nextReg / foldl_set_nomatch / foldl_set_get /
  compile_cycle_regs** — the **register half of the emission theorem is fully
  proved, generically and sorry-free**: for any design with distinct register
  names, every register of the emitted µVerilog equals the design's register
  after one cycle. `Loom/Hw/Compile.lean` has zero sorries. The remaining
  emission work is the memory-port half (guarded write-port fold).
- **Logic/KernelLemmas** — `bumpGen` monotonicity, `clearSlot_slotGen`.

**Stated precisely, proof in progress** — *this list is now EMPTY for the
T-ledger (2026-07-04: every entry below flipped to CLEAN; kept for history)*:

- ~~T2 authority_confined, step_confined~~ ✓ — the confinement induction.
- ~~T3 gen_monotone, revoke_temporal_safety~~ ✓ (the crown jewel).
- ~~T4 frame + two scrub equalities~~ ✓.
- ~~T5 noninterference (2-safety, path-free pairs)~~ ✓ (2026-07-04).
- ~~T6 no_hostage (donation-bounded resume)~~ ✓ (2026-07-04).
- ~~T7 wcet_retirement, budget_delivery~~ ✓.
- ~~T8 wx_machine_wide, prior_holder_excluded, status_word_safety~~ ✓.
- ~~T9 ledger_balanced, budget_bounded~~ ✓.
- ~~Inv step_wf, wf_invariant~~ ✓ (subsumed by `wfa_invariant`).
- ~~A-R / A-EV Acc8 core ⊑ spec, core ≃ emitted µVerilog~~ ✓.

In progress now: **R-MC** (LNP64-µ ISS ⊑ EDSL core, transporting T2–T9 onto
the emitted Verilog) — statement landed in `Theorems/RMC*.lean`.

**The linchpin, decomposed.** `step_wf` (one-cycle Wf preservation) is
assembled from proved pieces: `refillPhase_preserves_wf` ✓,
`moverPhase_preserves_wf` ✓, `wf_setCycle` ✓. Its remaining `corePhase`
obligation is further decomposed with proved scaffolding —
`wf_of_skeleton` ✓ (Wf congruence under skeleton-preserving edits),
`wf_of_skeleton_sameGates` ✓, `schedule_running` ✓ — and the
inflight-countdown and retirement dispatch are proved. **The entire well-formedness invariant is now a proved theorem.**
`Machines/Lnp64u/Logic/` has **zero sorries**. `Inv.wf_invariant`,
`Inv.step_wf`, and `T8.wx_machine_wide` are all CLEAN — proved *conditional on
a single explicit hypothesis*, `ExecPreservesWf`: "every instruction's
semantics preserves the machine invariant." Every structural piece is proved
outright (refill/mover/core phase preservation, the haltWith gate-unwind, the
issue-path budget/donation bookkeeping, `retire`'s decode/fault/errno
dispatch). `ExecPreservesWf` is the sole remaining Phase-1 obligation — the
per-opcode security argument (25 ops × the capability-kernel operations), the
irreducible research core. It is a clean `def`, not a `sorry`: the invariant's
conditionality on it is explicit in the statement. **`Logic/ExecWf` builds the
compositional framework, and the 14 base opcodes are proved.** `Logic/ExecWf`
has the `PreservesWf` combinator (closed under `pure`/`bind`/`ite`) with every
base primitive proved; `Logic/BaseOpsWf.base_preserves` discharges all 14 base
ALU/branch/memory opcodes; and `execPreservesWf_of_system` proves the whole
`ExecPreservesWf` from a single remaining obligation, **`SystemOpsPreserveWf`
— the 11 system opcodes**. So the entire machine invariant now reduces, with
everything else proved, to `SystemOpsPreserveWf` — the eleven system opcodes.
Of those, **7 are proved** (`Logic/SystemOpsWf`): `unmap`, `yield`, `halt`,
`map`, `cap_dup`, `mem_grant` (the full capability-derivation authority ops, via
the `wf_installDerived` lineage-bijection chain), and `move` (the Mover, via a
read-only-prefix thread into `wf_setMover`). **4 opcodes remain**: `cap_drop`,
`cap_revoke` (revocation — the `clearSlot`/`destroyMarked` lineage-graph
maintenance; the `wf_sweepRegions`/`wf_sweepMover` cached-authority sweeps they
need are **proved**), and `gate_call`/`gate_return` (the gate-transfer
machinery). These are the deepest T3 revocation + gate content, the irreducible
research core. **Infrastructure landed:** `wf_reparent` (lineage reparenting
preserves Wf — the graph half of `cap_drop`), `wf_sweepRegions`, `wf_sweepMover`.
**`wf_clearSlot_sweep` — the `clearSlot`+sweep composition, the single hardest
revocation lemma (~230 lines) — is now proved** (`Logic/ExecWf`): removing a
capability breaks `region_backed`/`mover_wf` for anything it backed, and the
sweeps repair them while the lineage bijection is maintained. `cap_drop`'s
remaining wiring needs `wf_orphanChildren` (the root-drop branch, mechanical) and
— a **proof-forced design finding** — a `Wf` clause ruling out self-parenting
(`parentOf (d,s) ≠ ⟨d,s,·⟩`): the reparent branch's "no cell points to the dropped
ref" obligation holds iff the dropped cap's parent isn't itself. Self-parenting is
unreachable by construction (`installDerived` always uses a fresh slot) but is not
currently excluded by the invariant, so completing `cap_drop`'s reparent branch
requires adding and re-establishing that clause — exactly the kind of
proof-driven invariant strengthening the charter anticipates.

**The acyclicity invariant is now built** (`Logic/Acyclic`): `Acyclic σ` (the
parent chain from any reference reaches a root within `numLineage` links), with
`init_acyclic` (boot has empty lineage tables) and `Acyclic.parentRef_ne` (no
capability is its own parent) proved. Both of `cap_drop`'s "no cell points at the
dropped ref" obligations are also proved — `reparent_no_ref` (reparent onto a
distinct parent) and `orphan_no_ref` (root drop) — so with `wf_reparent` and
`wf_clearSlot_sweep` both `cap_drop` branches are supported at the lemma level.
**The acyclicity preservation framework is now built and all of `cap_drop`'s
`Acyclic`-preservation is proved** (`Logic/Acyclic` + `Logic/ExecWf`):
`acyclic_of_parentRef_eq` (links unchanged → free, all non-lineage ops),
`acyclic_of_parentRef_le` (links only dropped → `clearSlot`, `orphanChildren`,
sweeps), and `acyclic_contract` (links rerouted onto the parent → `reparent`), on
top of the `climb`/`climb_add`/`climb_none_ge` well-foundedness kit. Concrete:
`acyclic_clearSlot`, `acyclic_orphanChildren`, `acyclic_sweepRegions`,
`acyclic_sweepMover`, and `acyclic_reparent` (via `reparent_parentRef`). **Remaining
for `cap_drop`:** ~~`wf_orphanChildren`~~ **(now PROVED)** and — mechanical but
fiddly) and the invariant plumbing — strengthening the workhorse invariant to
`Wf ∧ Acyclic` and re-establishing `Acyclic` across the remaining ops (free for the
non-lineage ops via the framework; a fresh-leaf/pigeonhole argument, `acyclic_installDerived`,
for `cap_dup`/`mem_grant`). `cap_revoke` needs `destroyMarked`; the gate ops need `transferCap`. Infrastructure in
place: `capLive_ok`/`capLive_err_state` (cap-op state characterization),
`freeSlot_caps_none`/`freeCell_none` (allocation specs), `wf_installRegion`,
and — the two hardest kernel lemmas — **`wf_installDerived`** (capability
derivation preserves Wf including the full T9 lineage bijection, ~150 lines)
and **`allocDerived_ok`** (its bridge). With these, `cap_dup`/`mem_grant`
reduce to threading `capLive` + a `narrow` characterization (plus the
narrowed range's BitVec no-wrap bound); `cap_drop`/`cap_revoke` to
`clearSlot`/`destroyMarked` + sweep lemmas; the gate ops to the gate
machinery; `move` to the Mover (`wf_setMover` proved).

These stated theorems are the genuine mathematical content of the program —
the readme's "honest budget" work. Every statement is fixed and audited; the
sorries are localized to proof bodies (P4), so progress is glanceable: a
theorem flips from STATED to CLEAN when its body is filled, without any
statement moving.

## Phase status (PLAN §8)

- **Phase 0 — Bootstrap: complete.** Generic ISA framework proven by two
  machines; T1 + A1 clean; both ISSes boot; trace frozen; skeletal books;
  L3/µLog design docs; µVerilog subset + semantics drafted; DSL front-end
  with the definitional-equality regression.
- **Phase 1 — Spec-level security: in progress.** Full T2–T9 + Wf invariant
  stated; L1 vocabulary (authority order, resource counting, access
  predicates) and the Wf invariant defined; EDSL semantics + Acc8 core
  lockstep against the ISS. Remaining: the invariant proofs; the L2 engines
  (BMC/k-induction/PDR — D2 found core's LRAT checker isn't kernel-reducible,
  so an in-house reducible checker is scheduled as task 1.2a); LNP64-µ's
  multicycle core.
- **Phase 2 — Silicon path: substantially prototyped.** EDSL→µVerilog
  compiler built, compiler keystone proved, Acc8 emitted and corroborated on
  iverilog + yosys. Remaining: the emission theorems' bodies, the µVerilog
  parser + round-trip, LNP64-µ emission, real FPGA bring-up.
- **Phases 3–4:** stated targets; refinement tactic, pipeline, logical
  relation, checker, demo — not yet started.

## The two-item TCB, today

1. The Lean kernel.
2. The µVerilog tool-boundary assumption, exposed as
   `Loom.Emit.MicroVerilog.ImplementsStandard` plus
   `Loom.Emit.MicroVerilog.implements_standard_spec` and whitelisted by
   audit only for emission-dependent theorems.

No trusted printer, no importers, no solver in the TCB. Mathlib is a
dependency but adds nothing to the TCB (kernel-checked, P8).

**gen_monotone (T3) infrastructure — COMPLETE (as of this session):** the `SlotGenLe` combinator
(`Machines/Lnp64u/Logic/SlotGen.lean`), all 14 base opcodes (`base_slotGen_le`), both kernel bump
lemmas (`clearSlot_slotGen_ge`/`destroyMarked_slotGen_ge` — the only slotGen writers, both via
`bumpGen`), the composite cap_drop/cap_revoke bounds, the preserving-op lemmas (halt/yield/unmap/
mapUpd/allocDerived/installDerived_slotGen/capLive/updDomGen/reparent/sweepMover), and the phase
reduction (`step_slotGen_reduce`: step's slotGen = corePhase(refillPhase σ)'s). **Remaining:** the
exec dispatch (`system_slotGen_le`, 11 system-op cases — 7 preserving via the combinator, 4 bumping
via the kernel bounds) + `corePhase_slotGen_ge` + `gen_monotone`. Same threading pattern as the
already-completed `system_preserves`/`system_preserves_acyclic`.


## Session update (2026-07-03, continued): T3 monotonicity chain, T9 budget, T8 complete

- **T3 `gen_monotone` CLEAN** — `system_slotGen_le` finished (gate_call/gate_return via
  `transferByHandle_slotGen_le`), lifted through `exec_slotGen_le` → `retire_slotGen_ge` →
  `corePhase_slotGen_ge` → `step_slotGen_ge`. `gen_monotone_n` and `no_resurrection` now
  unconditional. Remaining in T3: `revoke_temporal_safety`.
- **T9 `budget_bounded` CLEAN** — `Logic/Budget.lean`, a full `BudgetLe` combinator sweep
  (exec never raises budget; yield's 0 is the one inequality; refill restores exactly Q),
  assembled by `TSys.Inductive`.
- **T8 complete (all three CLEAN)** — `status_word_safety` (moverPhase case analysis) and
  `prior_holder_excluded`, with a **proof-forced statement fix**: the hypothesis must be
  *retired* (`r.gen < slotGen`), not merely *dead* (`liveRef = false`) — a dead-but-not-retired
  ref (empty slot at the ref's gen) can be re-installed at the same generation and become
  writable again, so the dead form is false. Destruction always retires (bumpGen strict off
  saturation; `freeSlot` tombstones saturated slots), so the retired form is the faithful
  reading of "destroyed". Proof: `no_resurrection` + `Wf.mover_wf`/`Wf.region_backed` over
  `reachable_stepN`.
- **T2 proof-forced semantics fix (machine-checked counterexample):** `step_confined`
  was FALSE — `narrow` allowed a zero-length narrow at exactly the end of memory to
  wrap the 12-bit base (`.mem 1 4095 p` + `off = 4095, nlen = 0` → `.mem 0 0 ⊥`),
  minting authority outside the roots' downward closure while remaining `Wf`. Fixed
  with a no-wrap `require` in `narrow` (PLAN §8b). `narrow_ok`/`narrow_err_state`
  re-proved; new `narrow_no_wrap` lemma.
- **T2 complete (all three CLEAN)** — `step_confined`/`authority_confined` via the
  `KindsLe`/`Dominated` sweep (`Logic/Authority.lean`); `narrow_kind_le` rests on the
  no-wrap fix.
- **T4 complete (all three CLEAN)** — `Touch`/`CalmLe` whole-cycle characterization
  (`Logic/GateStep.lean`, ~1450 lines): scrub equalities + the frame theorem (the
  `hcaps` hypothesis turned out unnecessary — caps traffic never reaches regs/pc/cause).
- **T6 proof-forced statement fix (starvation counterexample)** — `no_hostage` was FALSE:
  a top-priority hog with Q = P (legal) starves the serving chain forever; `resumeBound`
  had no interference term. Fixed: `StrictlySchedulable m` hypothesis (strict hyperperiod
  utilization) + interference-aware `resumeBound`. Scheduler/unwind/progress lemmas proved
  (`Logic/Hostage.lean`, sorry-free); final measure assembly remains (itemized in T6.lean).
- **T5 proof-forced statement fix (three channels)** — `noninterference` was FALSE:
  (1) the same scheduler starvation (destuttered trajectory freezes in one run only);
  (2) grants-in: `mem_grant` installs into the isolated domain's table without consent,
  perturbing its later handle values (register-visible); (3) the isolated domain's own
  `mem_grant`/`move` read globally-sensitive state into rd. Fixed: `TopPriority`
  hypotheses + `Isolated` gains `slots_full` and `code_local` clauses. Coupling
  infrastructure proved (`Logic/NonInt.lean`, sorry-free); the aligned-instant simulation
  assembly remains (plan in T5.lean).
- **★ T3 COMPLETE — `revoke_temporal_safety` (the crown jewel) is CLEAN ★** After a
  retiring `cap_revoke`, no agent ever writes under any marked descendant, forever.
  Proof machinery (`Logic/Tombstone.lean`, ~2700 lines): the `Evo` per-step relation
  (gen monotonicity + `RefFate` transport + tombstone permanence + Mover-liveness),
  the `ClassLineage` invariant (derived caps share their parent's class), and forward
  evaluation of the retiring revoke. **Proof-forced finding:** the statement admits a
  live *gate*-class handle (nothing forces mem class), where nothing is destroyed —
  the theorem survives only because gate-class descendants can never back a region
  register or Mover destination, which required the new `ClassLineage` and
  `MoverLiveMem` reachability invariants. All of T3 is now unconditional.
- **Second checker landed** — `checker/` standalone Lake package (`chk` CLI): independent
  from-scratch DIMACS+LRAT checker (own types, full deletion support, strict hints), zero
  Loom/Machines/Mathlib imports; `scripts/crosscheck_lrat.sh` cross-validates both legs on
  cadical php proofs + mutation rejections; CI-wired with solver-absent skip.
- **T6 refuted twice more (proof-forced):** the occupancy-vs-charge gap and the
  residual-budget **stall-lock** (the frozen scheduler's stall arm re-picks an underfunded
  top-priority domain forever — unbounded priority inversion). Statement now carries the
  occupancy-corrected `StrictlySchedulable`, a `StallFree` side condition, and an
  exponential lex `resumeBound`; scheduler redesign filed as PLAN D11. Assembly still open
  (5 itemized obligations in T6.lean).
- **L2 engines online (Phase 3)** — `Dp/Cnf` (Tseitin bit-blaster with the proved
  `blast_spec` soundness direction), `Dp/Bmc` + `Dp/KInduction` (`bmc_sound`,
  `kinduction_sound`: kernel-backed theorems over `Module.run` composing `blast_spec`
  with the in-house checker's `check_sound`), `Dp/Solver` (untrusted cadical/LRAT
  driver). **First certificate-checked BMC result**: Acc8's halted-stickiness at k=1
  (1416 clauses, 244 RUP steps, kernel `decide` ≈ 32 s). Axioms: classical trio only.
