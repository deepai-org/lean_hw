# Design composition

`Loom/Hw/Compose.lean` provides structural composition over `Design` values.
It does not change the core cycle semantics.

## Operations

- `Design.prefixed p d` prefixes register, memory, input, rule, and declared
  output names throughout a design.
- `Design.par a b` concatenates two designs. `parOkB` checks the disjointness
  conditions required for safe use.
- `Design.connect d wire` removes selected inputs and substitutes their
  expressions into rule bodies. Connections are combinational, same-cycle
  wiring.

Signal traversal and substitution live in `Loom/Hw/Rename.lean`. Substitution
replaces matching-width reads but never write targets; normal well-formedness
rules reject inconsistent declarations.

A typical composition prefixes instances, combines them with `par`, then
connects consumer inputs to producer registers. The resulting `inputs` and
mandatory `outputs` lists are the composite module boundary.

## Established guarantees

`Loom/Hw/Outputs.lean` proves that prefixing renames the exported set, parallel
composition exports the selected outputs of its parts, and connection cannot
resurrect an output that was not selected. The normal emission checks also
enforce name and output validity.

Full semantic refinement theorems for `prefixed`, `par`, and `connect` are not
yet part of the proved API. In particular, callers should not cite an
unproved general product or bisimulation theorem.

## SoC use

The LNP64mini SoC composes the core with single-clock HP and GP AXI masters.
The GP master uses the `gpm_` prefix to avoid core-name collisions, and its
read-data input uses the `_in` suffix. Debug shift logic, clock buffers,
reset generation, CDC, and the PS7 primitive stay in the board wrapper; Loom
owns the single-clock state machines and their declared interface.

Some hardware aliases and AXI constants are represented by registers because
the current EDSL has no general combinational output declaration. Such
observability registers can lag their source by one cycle and are not part of
the architectural core behavior.
