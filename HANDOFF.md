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

## The one open thread: R-MC (now UNBOUNDED; 4 audit-legal sorries remain)

**Resolved 2026-07-04 (D-class, user decision):** the uninhabitedness
finding (spec `cycle : Nat` strictly increases; concrete orbits are
eventually periodic) was repaired by making the spec physically honest —
`MachineState.cycle` is now a **wrapping `BitVec 32`**, exactly the
hardware register. Proof-forced companion: `Manifest.WF.period_dvd`
(`periodP ∣ 2^32` per domain; `hyperL_dvd_pow32` derived) — the refill
cadence stays `P`-periodic across the wrap only under that divisibility
(same constraint real RTOS tick periods have). The boot-skip guard in
`refillPhase`/`Hw.refillCondE` is gone (boot is indistinguishable from a
wrap; the cycle-0 refill rewrites the boot quota, a no-op). Counter
arithmetic re-plumbed once: `step_cycle`/`stepN_cycle` are `BitVec`
equations, windows reduce mod `P` through `Hostage.stepN_cycle_mod`.

R-MC statements are now horizon-free (`Machines/Lnp64u/Theorems/RMC.lean`):
`abs_run : ∀ n, Hw.abs ((core m).run n reset) = stepN m n initState`,
`invariant_transport` for every cycle count, and the unbounded
`refines : Nonempty (Simulation (machine m) (reachCore m))` — the plan's
simulation for the core *on its boot orbit* (`reachCore` shares states,
reset, and the whole reachable set with `(core m).toTSys`,
`reachCore_reachable_iff`; `invariant_pullback` restates transport on the
full core system). The full-garbage-state-space form is deliberately not
stated: `square` is conditioned on the physical coupling `Coupled`, and a
simulation over arbitrary junk register files would need spec-side
predecessors for garbage states — no verification content.

Ledger: RMC assembly entries CLEAN; the same 4 STATED with itemized
recipes: `absDom_reset`/`coupled_reset` (mechanical; needs the declList
optimization documented with `scripts/gen_rmc_reset_tab.py` to keep CI
affordable) and `square`/`coupled_step` (the large piece — build an
`Act.run` read/write frame kit first, then 25 per-op cases; `cap_revoke`'s
mark engine is the one research-grade case; NOTE: the `hwrap` hypotheses
are gone — the tick arm wraps identically on both sides, and `rctr_sync`
survives the wrap via `period_dvd`).

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
