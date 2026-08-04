# Package readiness

This checklist covers public Lean-package quality. It does not duplicate
theorem status or the release TCB; see [`STATUS.md`](STATUS.md) and
[`TCB.md`](TCB.md).

## Current verdict

The repository has the necessary package structure but is **not ready for a
public release tag at the current head**. The immediate blockers are concrete:

- `lake test` fails because several test designs have not been updated for
  mandatory `Design.outputs` and the current output-selection API;
- `scripts/quality.sh` reports two missing SPDX headers;
- repository CI and the release wrapper therefore do not complete; and
- the current LNP64mini hardware integration has not recovered its network
  acceptance result.

The exact current gate table lives in [`STATUS.md`](STATUS.md).

## Ready foundations

- Lean is pinned to a stable release and dependency revisions are committed.
- `Loom`, `Machines`, `Tools`, and `Tests` Lake targets exist, with root import
  modules for the public libraries.
- Package name, version, description, keywords, licenses, and test driver are
  declared in `lakefile.lean`.
- Apache-2.0, the additional `Machines/` Solderpad license, NOTICE, DCO,
  contributor guidance, conduct policy, issue forms, and PR template exist.
- GitHub Actions runs package quality, the repository CI script, and a direct
  `leanchecker` replay of the headline refinement module.
- A downstream smoke test creates a fresh consumer package and imports
  `Loom` and `Machines` through a path dependency.
- The audit inventories theorem axioms, project axioms, `sorry`, unsafe code,
  executable replacements, imports, `partial`, and `extern`.
- The README, current status, reproduction tiers, TCB, and trust limitations
  have distinct documented roles.

## Required before the first public release

- [ ] Make `scripts/quality.sh`, `lake build`, `lake test`, `lake exe audit`,
      and `scripts/ci.sh` pass from a clean checkout.
- [ ] Complete a clean Tier A release recheck and retain its metrics and exact
      source/tool identifiers.
- [ ] Revalidate or explicitly exclude the current hardware integration
      claims for the release commit.
- [ ] Choose the public package/module name and check for namespace conflicts
      before freezing the API.
- [ ] State the supported Lean-version window and test at least the intended
      next-version canary.
- [ ] Generate browsable API documentation for the intended public surface.
- [ ] Mark internal helpers accordingly and enforce docstrings/lints on the
      public API rather than on every implementation declaration.
- [ ] Review third-party notices and generated-artifact licensing for the tag.
- [ ] Tag a version and move the relevant `Unreleased` changelog entries into
      that version.

## Desirable follow-up

- Split CI reporting into package, proof/audit, tutorial, RTL, and optional
  external-tool jobs so a skip cannot look like a pass.
- Add parser negative tests and small reviewable golden Verilog fixtures.
- Run the toolchain upgrade canary separately from the pinned release job.
- Publish documentation and release artifacts from a reproducible tagged
  workflow.

## Package policy notes

- `lakefile.lean` is a supported Lake configuration format; changing to TOML
  has no quality value by itself.
- Mathlib is an ordinary checked proof dependency, not an external solver.
- The separate `checker/` package is an LRAT cross-validator, not an
  independent Lean kernel checker.
- Cached `.olean` files and generated release sources are build products, not
  distributable proof evidence.
