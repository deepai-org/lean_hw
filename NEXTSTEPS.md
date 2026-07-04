# NEXT STEPS — decided 2026-07-04

Current state: 92 ledger theorems, T1–T9 CLEAN, RTL corroborated
(iverilog + yosys), R-MC unbounded with exactly 4 audit-legal sorries.
See `STATUS.md` for the ledger, `HANDOFF.md` for session state.

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
