# Status

Honest, mechanically-checked state of the build. Regenerate the theorem
counts with `lake exe audit`; run `scripts/ci.sh` for the full gate.

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
- **Loom.Hw.Compile.compileExpr_eval** — the compiler keystone: emitted
  combinational logic evaluates to the source expression (full induction).
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
- **T9** ledger_balanced, budget_bounded.
- **Inv** step_wf, wf_invariant (init_wf is done; the invariant rests only
  on one-cycle preservation).
- **A-R / A-EV** Acc8 core ⊑ spec, core ≃ emitted µVerilog.

**The linchpin, now reduced to one lemma.** `step_wf` (one-cycle preservation
of the well-formedness invariant) is fully assembled from proved pieces:
`refillPhase_preserves_wf` ✓, `moverPhase_preserves_wf` ✓, `wf_setCycle` ✓.
The **single remaining sorry in the entire L1 invariant chain** is
`corePhase_preserves_wf` — the per-instruction argument (25 opcodes × the
kernel functions). Landing that one lemma flips `wf_invariant`,
`T8.wx_machine_wide`, and (with `gen_monotone`) `T3.no_resurrection` to CLEAN
at once. A whole cluster of the crown-jewel theorems bottlenecks on this
single, well-isolated obligation.

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
