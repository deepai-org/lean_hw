# Changelog

All notable user-visible changes will be recorded here. This project follows
[Semantic Versioning](https://semver.org/) once the first release is tagged.

## Unreleased

### Added

- **Declared observability** (Loom D39): `Design.outputs : Option (List
  String)` selects which registers a design exports as `o_<name>` ports;
  `none` (the default) keeps the previous behaviour, so every existing
  emitted module is byte-identical. An undeclared selection entry is a hard
  error at `Design.emit`. Proved: for `outputs = some ns`, a name outside
  `ns` appears at no output port — at the compiler (`compile_not_exported`)
  and over the emitted text (`printed_not_exported`). This lets a design
  hold a key in a register; `Machines/CapWalk`'s MAC key is now six
  unexported registers and its deviation CE5 is retired.
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
