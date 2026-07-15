# Loom package-readiness audit

Audited 2026-07-15 against the current repository, Lean/Lake documentation,
Reservoir metadata requirements, `lean-action`, and `doc-gen4` guidance.
This is an acceptance checklist, not a theorem-status ledger; proof progress
remains in `STATUS.md` and `NEXTSTEPS.md`.

## Verdict

Loom already has most baseline package infrastructure: a stable pinned
toolchain, committed dependency manifest, public umbrella modules, Apache-2.0
licensing, CI, tests, contribution policy, and an unusually explicit trust
document. It is structurally packageable, but it is **not release-ready** yet.

The blocking gap is consistency between the repository's trust claims and its
current build products. `lake build Machines.Lnp64u.Theorems.RMC` succeeds, but
the default `Machines` library still contains three `sorry` leaves and
`lake exe audit` rejects trusted-compiler dependencies introduced by the recent
retirement-arm proofs. CI correctly treats that audit as required, so current
`main` is expected to be red until the trust cleanup lands.

## P0 — release blockers

- [ ] **Restore the audit gate.** Remove the `native_decide`/trusted-compiler
  dependencies from the newly imported retirement proof stack. At this audit,
  the concentrated source hits are 141 in `RMCRetireDrop.lean`, 30 in
  `RMCRetireGrant.lean`, two in `RMCRetireGrantFrame.lean`, and one in
  `RMCRetireDropArm.lean`. Prefer shared finite-name injectivity/disjointness
  lemmas over hundreds of one-off reductions; use `decide +kernel` only where
  it remains tractable.
- [ ] **Close the three R-MC leaves.** `cap_revoke`, `gate_call`, and
  `gate_return` are the only remaining `sorry` bodies in the default library.
- [ ] **Reconcile advertised status with machine output.** Once the two items
  above land, regenerate or update `STATUS.md`, `NEXTSTEPS.md`, and `TRUST.md`
  from a green audit. `TRUST.md` still describes the older one-sorry R-MC state.
- [ ] **Prove or explicitly gate the executable compiler replacement.** The
  private unsafe fast path behind `@[implemented_by]` is already disclosed in
  `TRUST.md`, but it remains part of the artifact-generation TCB. Either prove
  `compileImpl = compile`, compare reference and optimized output in CI, or
  narrow release claims accordingly.
- [ ] **Run the clean-checkout release gate.** From a fresh clone: `lake build`,
  `lake test`, `lake exe audit`, `scripts/ci.sh`, and the headline
  `leanchecker` replay must all pass.
- [ ] **Meet Reservoir's external inclusion threshold.** Reservoir currently
  requires a public, non-fork GitHub repository with an OSI-approved detected
  license, a root manifest, and at least two stars. The repository is public,
  non-fork, licensed, and has the manifest, but currently has zero stars.

## P1 — community-facing readiness

- [x] Stable release pinned in `lean-toolchain` (`v4.28.0`), with a committed
  `lake-manifest.json`.
- [x] `Loom`, `Machines`, `Tools`, and `Tests` Lake targets are declared;
  `Loom.lean`, `Machines.lean`, and `Tests.lean` provide umbrella imports.
- [x] Reservoir-facing package metadata and a standard `lake test` driver are
  declared in `lakefile.lean`.
- [x] Apache-2.0 `LICENSE`, `NOTICE`, SPDX headers on every tracked Lean file,
  and the additional `Machines/` license are present.
- [x] GitHub Actions runs the repository quality check, the project CI/audit
  gate, Reservoir eligibility checking, and the toolchain's built-in
  `leanchecker` on the headline refinement module.
- [x] The README now contains a clean-clone quick start and version-update
  policy; `TRUST.md` documents the trusted computing base and claim limits.
- [ ] **Upgrade canary.** Reservoir currently lists Lean v4.31.0 as stable, so
  the pinned v4.28.0 toolchain is three stable releases behind.
  Test the next toolchain on a branch after the audit cleanup, not in the middle
  of it; regenerate the manifest and record the supported-version policy.
- [ ] **API documentation.** Add the nested `docbuild/` project recommended by
  doc-gen4, then publish `Loom:docs` and `Machines:docs`. Do not add doc-gen4 to
  the runtime dependency graph.
- [ ] **Docstring coverage.** Module headers are nearly complete, but a rough
  source count finds 1,830 declaration docstrings for 2,526 public-looking
  declarations. Establish the intended public API first, mark helpers private
  or internal, then enforce documentation on the exported surface.
- [ ] **Downstream smoke test.** In CI, create a tiny consumer package that
  requires Loom at the checked-out path and imports `Loom` and `Machines`.
- [ ] **Resolve the existing Loom collision before release.** Reservoir already
  indexes `@verse-lab/loom`, which also exports a top-level `Loom` library and
  namespace. Reservoir scopes disambiguate package lookup, but the shared Lean
  module namespace prevents consumers from depending on both. Decide whether
  this project should be renamed/re-namespaced before its public API freezes.
- [ ] **Release mechanics.** Add `CHANGELOG.md`, choose the first release tag,
  choose the final Reservoir scope/name, and document maintainers and the
  supported Lean-version window.
- [ ] **Community files.** Add a Code of Conduct and issue/PR templates,
  including an axiom/trust-surface checkbox.

## P2 — polish and maintainability

- [x] Remove committed Python bytecode and superseded scratch/draft proof files;
  ignore their future regeneration.
- [x] Add a fast `scripts/quality.sh` check for the pinned toolchain, package
  files, SPDX coverage, whitespace, and tracked scratch artifacts.
- [ ] Minimize the broad `import Mathlib` in `Loom/Dp/Bmc.lean`; the rest of the
  tree mostly uses focused Mathlib imports. Keep Mathlib if the proof/tactic
  surface justifies it—dependency minimization should not duplicate libraries.
- [ ] Extend the audit with an explicit inventory for `unsafe`, `partial`,
  `extern`, and `implemented_by`. Unsafe code is currently concentrated in the
  compiler/printer fast paths and should be whitelisted by declaration and
  documented, not merely found by an ad-hoc text search.
- [ ] Add a deliberate lint driver for public declaration documentation,
  unused arguments, and exported simp lemmas. Mathlib's linters may be used
  because Mathlib is already a dependency; avoid a second linter framework.
- [ ] Split CI reporting into proof/audit, documentation, RTL corroboration,
  and scheduled toolchain-canary jobs once the primary gate is green.
- [ ] Add parser negative/edge-case tests and reviewable Verilog goldens; keep
  simulator-dependent lockstep checks deterministic and separate from ordinary
  package builds.
- [ ] Mechanically generate or verify the theorem-status summary so prose
  cannot claim a green audit when the executable gate is red.

## Corrections to generic checklist advice

- `lakefile.toml` is not inherently more acceptable than `lakefile.lean`.
  Current Lake officially supports both; TOML is the declarative subset, while
  Lean configuration is appropriate when code-level build customization is
  needed. A format migration has no acceptance value by itself.
- The old external `lean4checker` repository is deprecated. Lean v4.28.0 and
  newer ship `leanchecker`; CI should use `lake env leanchecker`.
- Moving incomplete theorems to a WIP library would make a distributable core
  sorry-free, but it would also hide the actual headline refinement gap. Keep
  the three R-MC leaves visible until proved unless publishing a deliberately
  narrower `Loom`-only release.
- File-wide copyright headers are already complete. The remaining legal task
  is third-party attribution review, not mass header insertion.

## Authoritative ecosystem references

- Lake package configuration and metadata:
  <https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/>
- Standard Lean GitHub CI action:
  <https://github.com/leanprover/lean-action>
- doc-gen4's recommended nested-project setup:
  <https://github.com/leanprover/doc-gen4>
- Built-in `leanchecker` migration note:
  <https://github.com/leanprover/lean4checker>
