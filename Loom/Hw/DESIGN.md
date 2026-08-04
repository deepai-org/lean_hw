# Loom hardware EDSL

The hardware layer represents a synchronous design as ordinary Lean data,
gives it an executable cycle semantics, and compiles it to µVerilog.

## State and actions

`Loom/Hw/Syntax.lean` defines fixed-width expressions, register and memory
declarations, input ports, ordered rules, and the mandatory output selection.
Registers and memories are design-owned state. Inputs are environment-owned
coordinates refreshed before each open-design cycle.

An action can write registers and memory ports under guards. Expressions read
the pre-cycle state. Rules execute in list order and later enabled writes win,
including the declared ordering of memory write ports. This ordering is part
of the semantics, not a scheduling heuristic.

`Loom/Hw/Semantics.lean` provides reset, closed cycles, open cycles, and runs.

## Compiler and proof

`Loom/Hw/Compile.lean` lowers a `Design` to the µVerilog IR. The main compiler
correctness development is in `CompileCorrect.lean` and
`CompileWhole.lean`; it relates source cycles to module cycles under the
documented well-formedness conditions. `EmitIO.lean` performs checked
emission, and the artifact/parser certificates connect the in-memory module
to the text consumed downstream.

The executable compiler has audited `implemented_by` boundaries. Those
boundaries are listed in `TRUST.md`; they are not axioms and are not hidden
from the release audit.

## Checked design conditions

Emission fails closed on the repository's structural requirements:

- declaration and signal-name consistency;
- expression read validity and widths;
- module well-formedness and CSE identifier discipline;
- input ownership and clashes;
- synchronous-read memory shape;
- memory initialization deliverability and target shape where requested; and
- validity of the explicit output selection.

Composition, signal renaming, output guarantees, memory targets, CDC
contracts, and the restricted retiming primitive are documented beside their
implementations in this directory.

## Open designs

For a design with inputs, `fastRunOpen` and the ordinary semantics quantify
over an `InEnv` trace. A theorem about such a design is only as strong as its
quantification or explicit trace predicate. Wrapper behavior such as a CDC
command stream can be connected through a stated contract, but is not
silently assumed by the EDSL.

## Current limitations

The language is intentionally small. It does not currently provide arbitrary
combinational output declarations, multi-clock semantics, analog primitives,
or a fully proved semantic theory for every composition transform. Vendor
primitive mapping and physical timing are downstream evidence, not Lean
theorems of the source design.
