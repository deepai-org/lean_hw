# Retime / stuttering-simulation spec (D17 candidate)

Motivation: pipeline-aware refinement. A 2-stage component ≠ the 1-stage
one cycle-for-cycle; the relationship is refinement up to timing: an
abstraction function (Burch–Dill "flush") + a simulation where one impl
step maps to a spec step or a stutter. Timing-insensitive properties
(architectural invariants, "err never set", one-hot-ness, conservation)
transport automatically; timing properties don't, by design.

## Layer 1 — Loom/Core: stuttering simulation (new defs, additive)

In Loom/Core/Ts.lean's style (read it first; reuse TSys/Simulation):
- `StutterSimulation (impl spec : TSys)`: abs : impl.S → spec.S;
  init_ok; square: each impl step ⇒ (spec step on abs) ∨ (abs unchanged).
- `StutterSimulation.invariant_pullback`: a spec invariant holds of
  `abs s` for every reachable impl s. Prove this (small, same induction
  as Simulation.invariant_pullback).
- `Simulation.toStutter`: every Simulation is a StutterSimulation.

## Layer 2 — Loom/Hw/Retime.lean: the combinator (verified for a safe class)

The genuinely-safe first primitive (registered-output split / feedforward
cut): `retimeReg (d : Design) (r : String) (w : Nat) : Design` — add a new
register `r__pre` (width w, init = r's init); every rule write to r
becomes a write to r__pre; append a final rule `r <= r__pre`. Effect: r's
value stream is delayed by exactly one cycle; the combinational cone
feeding r is cut at the new register (the timing win when r's next-expr is
the critical path AND r's readers tolerate lag — e.g. observability
registers, latched read-back values like reg_rd/uart_byte/dmem_rd,
counters feeding slow consumers).

Soundness (state; prove what's tractable, defer the rest with the lemma
statement in a docstring — NO sorry in committed code):
`retimeReg_stutter : conditions → StutterSimulation (retimeReg d r w).toTSys
d.toTSys` with abs = "project r__pre into r, drop r__pre" — valid when no
rule of d READS r (write-only/observability registers) — that restricted
class needs no Burch–Dill flush and the square is provable by the same
foldl reasoning as compile_cycle. Decidable side condition
`readsReg d r = false` via an Expr.readsOf traversal.

## Layer 3 — application to lnp64mini (timing task #31, separate agent)

Candidates where readers-tolerate-lag holds by inspection: reg_rd,
uart_byte, dmem_rd(?NO — S_L1 reads it), o_* observability latches, the
next_ready/free_slot encoders (readers are next-cycle anyway — but they
ARE read; needs the general theory, skip). Use retimeReg where legal;
the bigger Fmax wins come from source-level restructuring (tree-ified
funnel guards, balanced encoders) — measured by nextpnr, validated by the
existing ladder. Do NOT change architectural semantics (ISS stays valid);
any FSM state addition needs the ISS updated in lockstep + full ladder.

## Deviations (implementation, 2026-07)

Implemented in `Loom/Core/Ts.lean`, `Loom/Hw/Retime.lean`,
`Machines/Substrate/RetimeDemo.lean`, `scripts/retime_demo.sh`. Everything
additive; no existing theorem or definition was touched; `lake build` + `lake
exe audit` green; no `sorry` in committed code; no new axioms.

* **Layer 1 was already present.** `StutterSimulation`,
  `StutterSimulation.invariant_pullback`, and `StutterSimulation.reachable`
  already lived in `Ts.lean`. Only `Simulation.toStutter` (every forward
  simulation is a stuttering one) was missing; added and proved.

* **`retimeReg_stutter` is PROVED, not merely stated.** For the
  `readsReg d r = false` class it is delivered as a genuine
  `StutterSimulation` obtained from a strict forward `Simulation`
  (`retimeReg_simulation`) via `Simulation.toStutter`. Supporting lemmas all
  proved: `Expr.eval_retimeAbs`, `RetimeRel.run_redirect` (per-action
  square), `RetimeRel.fold_redirect` (rule-list fold), `retimeReg_cycle` (the
  cycle square), `retimeReg_reset` (reset commutes with the abstraction).

* **Abstraction refinement — the D9 read-timing subtlety.** The copy-back
  rule `r <= r__pre` reads the *pre-cycle* `r__pre` (D9: all reads are
  pre-cycle), so the committed `r` lags `r__pre` by one further cycle. The
  sound abstraction therefore reads the *new* `r__pre` value as the spec's
  `r` (`retimeAbs`), which makes the copy-back a no-op under `abs`. `retimeAbs`
  additionally **zeroes** the `r__pre` coordinate (it is unobservable at the
  spec level): this is required for the commuting square to hold *at* the
  `r__pre` coordinate, since `d.cycle` never touches it. The soundness class
  is stated with the exact decidable side conditions bundled as `RetimeLegal`
  (the `retimeRegOkB` checks plus register-name `Nodup` from `DesignWF`,
  including `d.readsReg (r__pre) = false` / `d.writesReg (r__pre) = false`,
  which are freshness facts implied by legality + WF).

* **Traversals.** `Expr.readsOf` (name list) and `Expr.readsReg`/`Act.readsReg`
  /`Design.readsReg` (decidable Bool) are provided; `Act.writesReg`
  /`Design.writesReg` were added to state `r__pre` freshness. The redirect is
  `Act.redirectWrite`; the combinator is `retimeReg`, with `retimeRegInit`
  factored out and `retimeRegOkB` the decidable legality guard.

* **Demo register choice.** The spec suggested S13Soak's `maxout`, but
  `maxout` is *read* by `maxoutRule` (`ult maxout popc32`), so it is outside
  the proved no-read class. To exercise the *proved* theorem the demo uses a
  purpose-built write-only observability latch (`RetimeDemo.baseline`: a
  counter `cnt` and `obs := cnt + 7`, `obs` read by nothing). `retimeReg` on
  `obs` is emitted and iverilog-checked to be exactly the baseline delayed by
  one cycle over 40 cycles (`scripts/retime_demo.sh`), and cross-checked on
  the EDSL semantics in `RetimeDemo.check`.
