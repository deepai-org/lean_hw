# Changelog

All notable user-visible changes will be recorded here. This project follows
[Semantic Versioning](https://semver.org/) once the first release is tagged.

## Unreleased

### Added

- **Declared memory targets** (Loom D38): `Loom/Hw/MemTarget.lean` states
  the memory shape checks as "is this design realizable on target T"
  instead of "is this bank block-RAM friendly". `MemTarget` is ordinary
  data (write-port budget for the dedicated macro, capacity/depth
  thresholds, whether each realization's reset image is delivered), with
  profiles `xc7` (validated against yosys + ZC702 silicon), `ecp5` and
  `asicSram` (datasheet-derived; unsourced numbers are marked TODO in
  their docstrings). `Design.realizableOnB` is the check — the write-port
  trace condition promoted out of `Machines/CapWalk` plus D37's image rule
  read through the profile — and `Design.emit` enforces it for
  `MemTarget.default = xc7`, so every emitted module is byte-identical. It
  is strictly stronger than D37 there: a bank whose *second* write port
  pushes it out of block RAM now loses its image at compile time instead
  of on a board. `lake exe memtargets` prints the per-design portability
  table.
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
