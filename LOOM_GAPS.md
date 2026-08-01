# The capability ledger: what building real machines taught Loom

**The method.** Loom's capabilities are discovered by need, not designed in
advance. Every campaign drives a real artifact onto real silicon; every point
where the toolchain forces a workaround becomes a numbered decision (D-series,
`Loom/Hw/DESIGN.md`) rather than a hack. This file is the standing ledger:
closed gaps as evidence the method works, and *predicted* gaps for the work in
flight so they are built deliberately instead of discovered mid-proof.

**The rule**: friction is a ledger entry. If a proof needs a side condition the
architecture does not require, or a design needs a shape the EDSL cannot say,
that is a Loom defect — record it here before working around it.

## Closed (each discovered by a campaign, not by design)

| D | Capability | Discovered by |
|---|---|---|
| D9 | last-write-wins rule semantics (= NBA) | the first core port |
| D12–D14 | decidable read-validity / emission / CSE-identifier checks | the release-certificate path |
| D15 | input ports as environment-owned coordinates | the substrate ports (a JTAG regfile is not a closed system) |
| D16 | compose: prefixed / par / connect | the all-Lean SoC |
| D17 | StutterSimulation + verified `retimeReg` | pipeline-aware refinement |
| D18 | verified fast evaluator (retires hand-written ISSes) | mini-scale proof/eval cost |
| D19/D20 | sync-read + thread-table memories (BRAM inference) | the dual core did not fit |
| D21 | CDC contract: verified toggle-sync + `CmdPulseTrace` | the wrapper boundary |
| D22 | post-synthesis equivalence checking (LRAT-certified) | the yosys-adequacy assumption |

## Predicted, for engine verification (the epoch campaign and beyond)

**D23 — bounded response / temporal properties. REQUIRED BY THE CURRENT GOAL.**
`Loom/Core/Ts.lean` has `Invariant` (safety) and nothing else. The epoch demo's
acceptance is "bump-return-to-fail-closed within the ack bound"; §3's
acknowledgement bound, Law 5's bounded instruction, and all of Appendix C are
the same shape. Needed: a `WithinK` / bounded-until form over `TSys` runs, its
induction principle, transport across `Simulation`/`StutterSimulation` (a lag-k
simulation must compose with a K-bound), and the link to measured silicon
cycles so a proved bound and a board number are the same quantity. Bounded
liveness is also the honest hardware substitute for unbounded liveness — it is
WCET-shaped, and the ISA prices everything in named bounds anyway.

**D24 — rely-guarantee as first-class.** `CmdPulseTrace` (D21) is a hand-rolled
instance: a Prop on input traces that a design's theorems may assume. The
external-state doctrine (`Machines/Epoch/EPOCH_SPEC.md`) needs the general
theory: environment predicates, theorems quantified over all environments
satisfying `Φ`, satisfiability witnesses so a rely is provably non-vacuous, and
composition lemmas (rely of the whole from relies of the parts) that agree with
D16's `connect`.

**D25 — refinement toolkit beyond stutter.** A hardware engine commits over
several cycles what a protocol spec commits atomically; when the commit point
depends on the future (which volume acks last), plain forward simulation fails.
Needed: auxiliary/prophecy variables, or a backward/history-indexed simulation,
with the same `invariant_pullback` ergonomics. Expected to bite in the epoch
refinement (Layer 3) — if it does not, say so and close the entry.

**D26 — spec-to-design synthesis with soundness.** The proof-derived bus
monitor (`monitor_sound : monitor flags trace ↔ ¬ trace ⊨ Φ`) is a new
capability class: compile a temporal spec into a Loom `Design` and prove the
compilation correct. Distinct from D22 (which checks a design against text);
this checks the *world* against a spec, in hardware.

**D27 — checking-interface abstractions.** Authenticated backing store
(MAC/Merkle, epoch-bound anti-replay) so DDR-resident engine state carries
zero-assumption safety. The cryptography need not live in Loom; the reusable
piece is the *shape*: a validated view over untrusted bulk, with one refinement
quarantining the hierarchy (EPOCH_SPEC.md theorem 3).

## How to use this file

A campaign closes an entry by shipping the capability AND the artifact that
needed it — never the capability alone. An entry that survives two campaigns
without being needed is deleted: Loom grows by demand, and unused generality is
a cost, not an asset.
