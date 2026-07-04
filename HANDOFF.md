# HANDOFF — 2026-07-04

**The 2026-07-03 handoff is fully executed.** All three salvage branches were
integrated, and the goal it recorded — *finish the T-theorems, Phase 2 µLog,
Phase 3 L2 proof engines; correct Verilog emission for the core the
T-theorems govern* — is complete except for the R-MC transport proof (statement
landed, proof decomposed and in progress).

## State of `main`

- **The theorem ledger is fully CLEAN: 49/49, T1–T9, zero STATED**
  (`lake exe audit`). T5's four engines closed via the new `Logic/DFrame.lean`
  + `Logic/DRel.lean` sweeps; T6 `no_hostage` proved via
  `Logic/HostageChain/Measure/Frame/Count.lean` (chain relation + radix
  measure + potential/window counting). No statement changes; one T6-owned
  constant (`interferenceWindow`) honestly enlarged, documented in its
  docstring.
- **LNP64-µ core verified end-to-end at the Acc8-equivalent level**: the
  2000-cycle full-state system-op lockstep passes (`Tests/Lnp64uCore.lean`),
  `lake exe emit lnp64u` works (115 GB blowup fixed: pointer-memoized
  `compileImpl` via `implemented_by` + structural hash-consing in the
  printer), and the emitted `rtl/lnp64u.v` passes the 2000-cycle iverilog
  ISS-golden sim (`scripts/lockstep_lnp64u.sh`; yosys flow is memory-aware —
  RAM stays `$mem`).
- `README.md` now documents the Design→compile→emit→proof pipeline.

## The one open thread: R-MC (branch `wt-rmc` if unmerged)

`Simulation (machine m) ((core m).toTSys)` via `Hw/Enc.abs` — transports
T2–T9 onto the emitted Verilog. Statement + sorry-free assembly over named
sub-lemmas landed in `Machines/Lnp64u/Theorems/RMC*.lean`; encoder/decoder
round-trip kit and abs-at-reset field lemmas proved. Remaining: the per-op
square lemmas (mechanical, large — see the itemized docstring at the
top-level sorry for the recommended decomposition).

## Optional hardening (unchanged from before)

D11 scheduler fix (drop `StallFree` from T6); per-artifact `parseCheck`
kernel check for `rtl/lnp64u.v` (mirror `Machines/Acc8/TextRoundTrip.lean`);
LNP64-µ BMC demo via `Dp/Bmc`; `Dp/Pdr` when scaling demands; the Phase-3
logical relation (T2′/T4′) on the µLog seed; tagless-final unification of the
per-op datapath semantics (single polymorphic definition interpreted as both
ISS exec and circuit — would make most per-op R-MC obligations definitional;
discussed 2026-07-04, deliberately not started).

## Operational notes

- Agent worktrees need a fully-copied `.lake` seed (see 2026-07-03 notes; an
  interrupted copy leaves a broken cache).
- Run emitters under `ulimit -v 25000000` — earlyoom kills whole process
  groups here and `--prefer`s `lnp64*`/`yosys` names.
- The sweep pattern now has NINE worked instances (add DFrame, DRel — plus
  Hostage's chain kit) — never write one from scratch.
- Audit policy unchanged: sorries only in `Machines/*/Theorems/` + `Wip`;
  `native_decide` banned; single `ImplementsStandard` axiom whitelisted.
