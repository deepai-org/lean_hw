# Changelog

All notable user-visible changes will be recorded here. This project follows
[Semantic Versioning](https://semver.org/) once the first release is tagged.

## Unreleased

### Added

- **Declared memory targets** (Loom D38): `MemTarget` records macro/soft
  memory names, write-port limits, size thresholds, and image-delivery
  behavior. `Design.realizableOnB` checks a design against `xc7`, `ecp5`, or
  `asicSram`; emission enforces the default XC7 profile. XC7 is the exercised
  repository target, while ECP5 and generic ASIC SRAM retain explicit
  provisional/TODO assumptions. `lake exe memtargets` prints the table.
- **Declared observability** (Loom D39): every `Design` has a mandatory
  `outputs : List String` selecting the registers exported as `o_<name>`
  ports. An unknown selection is a hard error at `Design.emit`. The compiler
  and printed-artifact theorems show that an unselected name is not exported.
  This lets the capability engine keep its MAC-key registers off the module
  interface.
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
