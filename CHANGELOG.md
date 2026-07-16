# Changelog

All notable user-visible changes will be recorded here. This project follows
[Semantic Versioning](https://semver.org/) once the first release is tagged.

## Unreleased

### Added

- Unbounded, sorry-free LNP64-µ ISS↔EDSL refinement (`RMC.square`,
  `abs_run`, `refines`, and `invariant_transport`) across all 25 opcodes.
- Bounded `cap_revoke` pointer-doubling convergence and synchronized
  retirement proof.
- Machine-enforced executable trust inventory for unsafe helpers,
  `implemented_by`, `partial`, and `extern` declarations.
- External downstream-package smoke test importing `Loom` and `Machines`.

### Changed

- Trust and status documents now distinguish the proved ISS↔EDSL chain from
  executable compiler/printer replacements and the physical µVerilog/SoC
  boundary.

## 0.1.0-dev

Initial development line; no stable release has been tagged.
