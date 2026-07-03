# HANDOFF — 2026-07-03 session stop (restart guide)

The session was stopped mid-flight (Fable usage credits ran out under a fleet of
subagents; the user then killed everything). **Nothing was lost**: all completed
work is merged to `main` (pushed to origin through commit `03a55d4`), and every
in-flight agent's uncommitted work was salvaged into a `worktree-agent-*` branch.
This file records exactly where things stand and the path to full completion.

Goal being pursued (unchanged): *finish the T-theorems, Phase 2 µLog, Phase 3 L2
proof engines; ensure correct Verilog emission for the core the T-theorems govern.
No FPGA bring-up.*

---

## 1. State of `main` (pushed, green)

`lake build` ✓ · `lake exe audit` all checks passed · `scripts/ci.sh` ✓ ·
`scripts/lockstep_acc8.sh` ✓. 44+ CLEAN ledger theorems.

### Done (kernel-checked CLEAN unless noted)

- **T1, T2, T3 (incl. `revoke_temporal_safety`, the crown jewel), T4, T7, T8, T9 —
  ALL COMPLETE.** Only T5/T6 remain STATED (see §2).
- **Acc8 silicon chain closed end-to-end**: A1, A-R (spec ⊑ EDSL core), A-EV
  (core ≃ compiled µVerilog; generic emission theorem — register AND multi-port
  memory folds proved), µVerilog **parser + round-trip** (`parseCheck` +
  kernel-checked demo + byte-level `#guard` on `rtl/acc8.v`), iverilog+yosys
  corroboration. TCB = Lean kernel + the single `ImplementsStandard` axiom.
- **Multi-port memories (`wrPorts`)** in Loom (Mover needs 3 same-cycle writes):
  per-port compiler folds, `MemWriteWF`, emission theorem generalized,
  `Tests/MultiPort.lean`.
- **LNP64-µ EDSL core, base half** (`Machines/Lnp64u/Hw/`): full 633-register
  state encoding + `abs`, refill/scheduler/issue/retire/halt circuits, 14 base
  ops; **256-cycle full-state lockstep vs the ISS passes** (`Tests/Lnp64uCore.lean`).
- **µLog seed**: `Loom/Logic/Sep/Bi.lean` (PCM/BI, sep/wand adjunction),
  `Loom/Logic/StepIndex.lean` (later + Löb), `Machines/Lnp64u/Logic/Sep/Resource.lean`
  (µ resource algebra + T9 bridges).
- **L2 engines (Phase 3)**: `Loom/Dp/Cert/Check.lean` (kernel-reducible RUP/LRAT
  checker + `check_sound`; D2 benchmarks: php6 ≈ 13.5 s kernel decide — GO),
  `Dp/Cnf` (Tseitin, proved `blast_spec`), `Dp/Bmc` + `Dp/KInduction`
  (`bmc_sound`, `kinduction_sound` — kernel-backed over `Module.run`),
  `Dp/Solver` (untrusted cadical driver), **first certificate-checked BMC
  result** (`Tests/Acc8Bmc.lean`: Acc8 halted-sticky, k=1, 244-step cert,
  kernel decide ≈ 32 s), and `checker/` — the independent second checker
  (standalone package, own LRAT implementation, `chk` CLI,
  `scripts/crosscheck_lrat.sh`).

### Seven proof-forced findings this session (all recorded in STATUS.md/PLAN §8b + auto-memory)

1. T8: "dead" ≠ "retired" — `prior_holder_excluded` hypothesis strengthened.
2. T2: `narrow` 12-bit base wraparound (machine-checked counterexample) — no-wrap
   `require` added to the semantics.
3. T6: top-priority `Q = P` hog starves the serving chain → `StrictlySchedulable`.
4. T6: occupancy (cost+1 cycles) ≠ charges (cost) → occupancy factor.
5. T6: **residual-budget stall-lock** — real scheduler bug (unbounded priority
   inversion); v1 hypothesis `StallFree`, scheduler redesign filed as **PLAN D11**.
6. T5: three leak channels (starvation, grants-in, globally-sensitive ops) →
   `TopPriority` + `Isolated.slots_full`/`code_local`/`wx_disjoint`; observation
   projected to regs/pc/run/cause (budget provably drifts).
7. T3: gate-class handles satisfy revoke's hypotheses (nothing destroyed) —
   survived via new `ClassLineage` + `MoverLiveMem` invariants (Tombstone.lean).

---

## 2. Salvage branches (un-merged work — INTEGRATE THESE FIRST)

Each is a branch in this repo; the matching worktrees under `.claude/worktrees/`
can be deleted after harvesting (`git worktree remove --force <path>`, keep the
branches until merged). **Branch `worktree-agent-a079de190f5cb5942` is stale
(T4, already merged) — delete it.**

### A. `worktree-agent-afda9cba86a956ef8` — LNP64-µ core completion (MOST VALUABLE)

Contains (WIP-salvage commit on top): ALL 11 system-op circuits
(`Machines/Lnp64u/Hw/SysOps.lean`) including a **pointer-doubling marks engine**
for cap_revoke running in hidden registers across in-flight countdown cycles
(the naive 64× combinational unroll was unrepresentable — recorded in
`Hw/DESIGN.md`); the Mover rule on memory write ports 0/1/2; a system-op test
manifest (`Hw/Demo.lean`); Enc/BaseOps/Core extensions; a 2000-cycle full-state
system-op lockstep in `Tests/Lnp64uCore.lean`; `Tools/Emit.lean` lnp64u target;
a drafted STATUS entry **claiming completion — UNVERIFIED** (the agent died while
the 2000-cycle lockstep was still elaborating; treat the claim as pending).

**To finish**: merge the branch into a fresh worktree/main-copy; `lake build`;
run `lake build Tests.Lnp64uCore` (the 2000-cycle test takes several CPU-min);
if it diverges, debug circuits against `Step.lean`/`Isa/System.lean` (the test
reports the divergent cycle + reason); then verify/finish
`scripts/lockstep_lnp64u.sh` (emit `rtl/lnp64u.v`, iverilog vs ISS golden, yosys
stat — record cell counts); reconcile the STATUS claim with reality.
(Branch `worktree-agent-a6f6229edb856ae63` is an opus continuation that had just
merged this salvage — nothing extra in it; its `.lake` copy was interrupted and
is BROKEN, don't reuse that worktree.)

### B. `worktree-agent-afa3abca020da8214` — T5 engine lemmas progress

Committed `a3c30c8`: `issue_step` CLOSED; two proof-forced statement repairs
(`Insulated.latch_rom` clause — latch provenance; `progress` gained `hcost`);
memory-disjointness bricks (`covers_not_underRoots`, `moverPhase_mem_frame`, …).
Remaining sorries in `Logic/NonInt.lean`: `insulated_step`, `frame_step`,
`retire_step_lockstep`, `progress` (grep to confirm — its sub-agents' results
were lost). T5's top-level simulation in `Theorems/T5.lean` is fully assembled
and consumes exactly these.
(`worktree-agent-acba20c4c500df7e6` = opus continuation, just the merge, nothing extra.)

**To finish**: merge, build green, then close the four sweeps. Reuse
`Logic/GateStep.lean`'s `Touch`/`CalmLe` hard. Key facts: d never blocked/serving
(no gate caps, callee ≠ d); `slots_full`+`code_local`+`wx_disjoint` kill
grants-in/self-modify; boot roots have `lineage = none` so others' revokes never
mark them; `sweepRegions` only removes dead-backed regions.

### C. `worktree-agent-ad5faca33d33b2db5` — T6 assembly WIP

WIP-salvage commit: a `ChainLe`/`ChainOut` combinator kit (chain-observable
frame: gates/maxDonation/budget/serving/run) proved for base ops + kernel ops +
`transferByHandle`, plus drafted `GateCallShape`/`GateReturnShape` postcondition
defs, appended to `Logic/Hostage.lean`. May have errors near the end (mid-iteration).
(`worktree-agent-abfb548dfdba02a17` = opus continuation, merged salvage + minor WIP.)

**To finish T6** (`no_hostage` — hardest open item): obligations 1, 3, 4 of its
docstring itemization are DONE on main (`halted_serving_none_invariant`,
`step_cycle`/`stepN_cycle`, `halted_stays`/`stepN_halted`,
`refill_within_period`/`origin_refill_eligible`, plus `corePhase_cases`,
`massExcept` accounting, scheduler lemmas — all sorry-free in `Logic/Hostage.lean`).
Remaining: (obligation 2) prove the gate ops establish the Shape postconditions
(mirror `gatecall_slotGen_le`'s require-chain threading in `Logic/SlotGen.lean`),
define the chain (domains distinct since a domain serves ≤ 1 gate ⇒ length ≤
numDomains) and the radix lex measure Σ donatedᵢ·W^(L−i), W = maxDonationBound+2
(a parent's charge-decrease dominates a new child's appearance); (obligation 5)
the interference-window counting via `StrictlySchedulable`/`StallFree` and final
assembly. `resumeBound`/`interferenceWindow` formulas may be adjusted (T6-owned
defs) with documented reasons.

---

## 3. Remaining path to full completion (ordered)

1. **Integrate salvage A** (core completion) → LNP64-µ full-ISA lockstep green →
   `rtl/lnp64u.v` emitted + iverilog/yosys corroborated. This completes the
   user's "emit correct Verilog for the core" at the Acc8-equivalent level.
2. **Integrate salvage B** → close the 4 T5 engine sweeps → T5 CLEAN.
3. **Integrate salvage C** → T6 measure + window assembly → T6 CLEAN.
   (T5+T6 are the only STATED ledger entries left.)
4. **R-MC statement + proof** (`Simulation (machine m) ((core m).toTSys)` via
   `Hw/Enc.abs`) — plain per-field simulation by the 1-cycle-per-spec-cycle
   design; this is what formally transports T2–T9 onto the emitted Verilog
   (text via the parser round-trip, tools via the `ImplementsStandard` axiom).
   Big but mechanical-ish; land the statement first (sorry in Theorems/ is
   audit-legal).
5. **Optional hardening**: D11 scheduler fix (drop `StallFree` from T6);
   per-artifact `parseCheck` kernel check for `rtl/lnp64u.v` (mirror
   `Machines/Acc8/TextRoundTrip.lean`); LNP64-µ BMC demo via `Dp/Bmc`;
   `Dp/Pdr` when scaling demands; the Phase-3 logical relation (T2′/T4′) on the
   µLog seed.

## 4. Operational notes for the next session

- **Agent worktrees need a `.lake` seed** or they rebuild the world:
  `cp -a /home/ubuntu/lean_hw/.lake <worktree>/.lake.new && rm -rf <worktree>/.lake
  && mv <worktree>/.lake.new <worktree>/.lake` — copy FULLY before use (an
  interrupted copy leaves a broken cache, as in the a6f622 worktree).
- Agent worktrees sometimes branch from a stale commit — have each agent
  `git merge main --no-edit` (or fast-forward) FIRST and verify the expected
  files exist before believing the task brief.
- The session died on **Fable usage credits** with ~7 agents in flight; consider
  smaller waves (2–3) and `model: "opus"` for mechanical sweeps.
- The sweep pattern (SpecM combinator over 25 ops) now has SEVEN worked instances
  to mirror: SlotGen, Budget, Inflight, Authority, Tombstone (Evo), GateStep
  (Touch/CalmLe), Hostage (hsn/CycleEq/HaltedStays). Never write one from scratch.
- Audit policy: sorries only in `Machines/*/Theorems/` + `Wip` namespaces;
  `native_decide` banned; single axiom whitelisted. `lake exe audit` is the gate;
  `scripts/ci.sh` the full check.
