# L3 — Hardware EDSL and verified compiler: design

**Named win (Rule 5):** exact fit to the `TSys` spine and the `View` construct —
rule-atomic semantics whose linearization points coincide with the spec's
instruction-retirement snapshots, and maintained views whose data structures *are* the
T2/T3/T9 induction hypotheses. No existing framework (Kôika, Bluespec, Chisel) gives us
that coupling, and none is importable under Rule 4 anyway.

## Semantics (from the Kôika papers; no Kôika code)

- A **design** is: a set of typed registers/memories, and an ordered list of **rules**.
- A **rule** is an atomic guarded action: reads observe the *pre-cycle* state; writes are
  accumulated in a log; a rule that double-writes or reads-after-write in conflict with an
  earlier rule in the schedule *aborts* (its writes drop) — the one-rule-at-a-time (ORAAT)
  semantics.
- **Cycle semantics** = fold the schedule over the log; commit the log at cycle end. The
  scheduling-correctness story: the parallel (hardware) execution of one cycle equals the
  sequential ORAAT execution — proved once, generically, over the log algebra.
- This gives `TSys` directly: `S` = register/memory valuation, `step` = one committed cycle.

## Action language

Intrinsically typed terms (deep embedding): `Action Γ τ` with reads, writes, pure ops
(BitVec kit), `if`, `let`, memory read/write ports. Depth of typing is driven by one
requirement: `View q` (a maintained-view register) demands a DBSP derivative proof *in its
constructor*, so construction is proof-carrying — correct-by-construction views.

## Compiler

`Action` → netlist IR (registers, LUT-expressible combinational nodes, memory ports), with
semantics preservation stated as `TSys` equality against the ORAAT semantics. One-rule
designs first (Acc8's core is a single rule); the log/schedule composition after.

## Order of construction

1. `Action`/`Rule`/ORAAT semantics + `TSys` instance (task 1.10)
2. Acc8 core as the first user; lockstep vs Acc8 ISS (task 1.11)
3. LNP64-µ multicycle core (task 1.11)
4. Netlist IR + verified compiler (tasks 2.1–2.2)
5. `View` construct + DBSP normalizer when the readiness OR-tree and sweep aggregation
   need them (task 3.3)
