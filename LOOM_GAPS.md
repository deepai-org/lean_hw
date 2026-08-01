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
| D23 | bounded response (`MustReach`), ranking rule, transport across `Simulation`/`StutterSimulation` | the epoch demo's acceptance criterion: bump-return within the ack bound |

### D23, in detail (closed 2026-08-01)

**Shipped** — `Loom/Core/Bounded.lean` (capability) and
`Machines/Epoch/Bounded.lean` (the artifact that needed it):

* `MayReach Q n s` (`EF≤n`), `MustReachOrBlock Q n s` (`AF≤n`, deadlock
  tolerated) and `MustReach Q n s` (`AF≤n` **plus** an enabledness witness at
  every pre-response state). `BoundedResponse P Q K` = "from every reachable
  `P`-state, `MustReach Q K`". The all-paths reading is not left to the
  definition's shape: `MustReachOrBlock.on_path` proves that every explicit
  path of length `n` out of `s` contains a `Q`-state.
* The **enabledness decision, made explicit**: over a relation that may block,
  `AF≤K` is vacuously true at a stuck non-`Q` state, which is not a hardware
  bound. So `MustReach` carries the "can step" obligation, `MustReachOrBlock`
  does not, and every theorem that produces the former takes the concrete
  enabledness hypothesis as an argument rather than assuming totality.
* The **workhorse**: `TSys.Ranking Q Dom μ` (progress off `Q`, `Dom` closed,
  `μ` strictly decreasing) with `Ranking.mustReach : μ s ≤ n → MustReach Q n s`
  and `boundedResponse_of_ranking`.
* **Transport**: `Simulation.mustReachOrBlock_pullback` (no side conditions),
  `Simulation.mustReach_pullback` / `boundedResponse_pullback` (same bound `K`,
  given implementation enabledness), and
  `StutterSimulation.mustReach_pullback`: with a stutter rank `≤ b` that
  strictly decreases on every stuttering step, a spec bound `K` becomes an
  implementation bound `K*(b+1) + rank s`, hence `K*(b+1) + b`.
* **The artifact**: `Machines/Epoch/Bounded.lean` proves the epoch protocol's
  ack bound without touching the frozen `Protocol.lean` — under the ack-phase
  schedule `ackSys` (each step is a *fresh* ack or the return, and each step is
  a genuine `Protocol.Step`), `bumpReturn` is enabled within `K` steps and the
  bump has returned within `K + 1`, on all paths, with no deadlock. The
  fairness hypothesis is shown to be load-bearing rather than decorative:
  `unbounded_without_fairness` proves that in the *unrestricted* protocol a
  bound of any size implies the bump had already returned (`use` is an
  always-enabled self-loop).

**Not covered.** Unbounded liveness and fairness proper (`◇`, `□◇`, weak/strong
fairness) remain out of scope — there is no fairness algebra here, and a
property with no nameable `K` gets no support. The bound is over *steps of the
transition system*, not cycles: converting a proved `K` into a silicon number
requires a steps-per-cycle argument at the refinement that introduces the clock
(D23's "link to measured silicon cycles" is therefore deferred to the engine
refinement, which is where the cycle-accurate system exists). Nested/until
temporal formulae, past-time operators, and any automaton-based specification
language are absent; the response predicate is a plain state predicate.
Transport is forward-simulation-shaped, so a refinement needing prophecy (D25)
must be repaired there first — a bound cannot be pulled through a simulation
that does not exist.

## Predicted, for engine verification (the epoch campaign and beyond)

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

## D28 — steps-to-cycles: a proved bound and a measured number must be one quantity

Discovered closing D23 (2026-08-01). Bounded response is stated in
*transition-system steps*; the goal's acceptance is in *fabric cycles*. Those
are only the same quantity once a refinement fixes the steps-per-cycle
correspondence — which is exactly what the Engine→Protocol refinement (Layer 3)
introduces, via the stutter budget `b` that `StutterSimulation.boundedResponse_pullback`
already takes. So the entry is small but load-bearing: state, in one place, that
the spec bound `K` transported through a design with budget `b` is the number of
CLOCK CYCLES a silicon measurement may be compared against, and make the epoch
demo cite that theorem when it prints its latency. Without it, "proved bound"
and "measured cycles" are two numbers that merely look alike — which is exactly
the sloppiness this project exists to refuse.
