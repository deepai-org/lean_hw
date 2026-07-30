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
