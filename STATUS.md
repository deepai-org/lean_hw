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
threading the combined obligation into `wfa_invariant`. `cap_revoke`/gate ops still need
`destroyMarked`/`transferCap` (their own kernel lemmas, then the same thread).

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
  policy, the single-axiom whitelist, the `native_decide` ban (Rule 1), and
  the `Loom`-never-imports-`Machines` DAG (P0).

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

**Stated precisely, proof in progress** (`sorry` in body or transitively):

- **T2** authority_confined, step_confined — the confinement induction.
- **T3** gen_monotone (per-step) — the one remaining obligation under which
  `gen_monotone_n` and **no_resurrection** are already fully proved; plus
  revoke_temporal_safety (the crown jewel).
- **T4** frame + two scrub equalities.
- **T5** noninterference (2-safety, path-free pairs).
- **T6** no_hostage (donation-bounded resume).
- **T7** wcet_retirement, budget_delivery.
- **T8** wx_machine_wide (**body complete**, rests on step_wf),
  prior_holder_excluded, status_word_safety.
- **Inv** `haltWith_preserves_wf` **proved**; `refillPhase`/`moverPhase` preserve
  Wf (proved); `step_wf` bottoms out at `corePhase` issue-path + `retire`.
- **T9** ledger_balanced, budget_bounded.
- **Inv** step_wf, wf_invariant (init_wf is done; the invariant rests only
  on one-cycle preservation).
- **A-R / A-EV** Acc8 core ⊑ spec, core ≃ emitted µVerilog.

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
2. `Loom.Emit.MicroVerilog.ImplementsStandard` — the single boundary axiom,
   whitelisted by audit only for emission-dependent theorems.

No trusted printer, no importers, no solver in the TCB. Mathlib is a
dependency but adds nothing to the TCB (kernel-checked, P8).
