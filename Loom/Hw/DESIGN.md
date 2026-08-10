# Loom hardware EDSL

The hardware layer represents a synchronous design as ordinary Lean data,
gives it an executable cycle semantics, and compiles it to µVerilog.

## State and actions

`Loom/Hw/Syntax.lean` defines fixed-width expressions, register and memory
declarations, input ports, ordered rules, and the mandatory output selection.
Registers and memories are design-owned state. Inputs are environment-owned
coordinates refreshed before each open-design cycle.

`Loom/Hw/Notation.lean` provides opt-in width-typed register and memory handles.
`Loom/Hw/Declarations.lean` lets those handles contribute declarations and
interface policy once, then lowers them to the same core `Design`; direct
`Design` construction remains supported.

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

For local proofs, `cycle_support` rewrites a register or memory projection of
one cycle to only the rules whose computed write footprints contain that
coordinate. This preserves rule order and last-write-wins semantics while
keeping unrelated rules out of the proof state.
`regPropertySupport` and `memPropertySupport` compute one ordered writer
cone for every coordinate named by a multi-coordinate property. Their cycle
theorems preserve each member projection. Typed register and memory
projections are `simp` lemmas, so retained rules simplify through the handle
API.
`PropertyFootprint` combines register and memory coordinates into one
reduced `propertyCycle`. The full cycle is proved to agree with it on the
complete footprint, and `invariant_of_propertyCycle` packages reset plus
reduced-step preservation as an ordinary transition-system invariant.
`PropertyFootprint.lift` constructs supported properties by projecting away
all unnamed state, and `invariant_of_liftedPropertyCycle` removes the manual
dependency proof. `propertyFootprintOkB`/`propertyFootprintReport` reject
unknown or wrong-width coordinates before a typo can manufacture an empty
support.
For properties stated as predicates of an EDSL expression,
`PropertyFootprint.ofExpr` derives the coordinates from `Expr.readSites`.
`exprPropertyCycle` and `invariant_of_exprPropertyCycle` then infer both the
dependency proof and the reduced writer cone; no coordinate list is maintained
beside the expression.
When a property is clearer as several differently typed observations,
`ExprProperty` combines expression atoms with `and`, `or`, and `not` while
retaining their propositions in `Prop`. Its `footprint` and `supports` theorem
are structural, and `propertyExprCycle` /
`invariant_of_propertyExprCycle` consume the resulting writer cone without a
manual union or dependency lemma.
`ExprProperty.truth` is the identity used by `ExprProperty.all`, so generated
tools can construct a conjunction from a list of differently typed atoms
without a special nonempty case or a hand-written binary tree.

Rule selection is followed by action projection when a retained rule is itself
large. `Act.projectRegs` and `Act.projectMems` erase unselected writes and
collapse syntactic no-ops; `Act.projectFootprint` combines both sides.
`propertyProjectedCycle` applies that projection to every retained rule, with
closed/open agreement theorems and invariant combinators. LNP64mini's real
thread-array funnel shrinks from three register plus eight memory writes to
one of each for an `in_gate`/`tpc` property. This is a proof view only; it does
not change the design or RTL.
`Loom.Hw.PairSafety` supplies a proved abstract interpreter for two distinct
one-bit registers. It explores guards nondeterministically, preserves ordered
writes, retains literal-bit precision, and turns its executable exclusivity
check into an `Act.run` preservation theorem.

## Open designs

For a design with inputs, `fastRunOpen` and the ordinary semantics quantify
over an `InEnv` trace. A theorem about such a design is only as strong as its
quantification or explicit trace predicate. Wrapper behavior such as a CDC
command stream can be connected through a stated contract, but is not
silently assumed by the EDSL.

`Design.toAssumedOpenTSys` makes such a contract part of every transition: a
step carries an input valuation, the state-dependent `InputAssumption`, and
the resulting `cycleOpen` equality. `invariant_of_assumedCycleOpen` is the
generic assume/guarantee induction rule. For inferred properties,
`propertyCycleOpen` applies inputs before writer-cone reduction and
`invariant_of_assumedPropertyExprCycleOpen` combines the explicit contract
with the same footprint-agreement theorem used by closed designs.
`invariant_of_assumedProjectedPropertyExprCycleOpen` additionally removes
unselected writes inside every retained rule.

## Debug instrumentation

Shipping, semantically meaningful observations should remain ordinary typed
design outputs. For temporary board bring-up, `Loom.Hw.DebugTap` provides a
smaller explicitly unverified path: a `DebugMap` is one list of typed register
taps or raw wrapper expressions from which Loom generates child-port bindings,
two-flop DRCK sampling, optional first-event capture, core selection, and the
BSCAN read decoder.

`DebugTap.ofDualExpr` accepts a typed, register-only EDSL expression and derives
its exported-register dependencies for both cores. `stickyOfDualPredicate`
turns a one-bit expression into a resettable first-event observation. Existing
wrapper bindings and dependencies repeated across taps are reused. Expressions
that read an internal memory fail the map guard because the wrapper has no
memory port to bind.

A sticky tap may request halt-on-trigger. The generated per-core request stays
high until that tap's reset clears its valid bit. Whether and where the request
is connected is wrapper policy outside the semantic design; LNP64mini routes
the core-1 request into its existing instruction-boundary hold and leaves the
core-0 composition unchanged.

This facility deliberately does not extend `Design`, the ISS, lockstep state,
or the compiler theorem. Its report and generated header identify raw
expressions, CDC behavior, wrapper integration, and observed values as external
instrumentation. Map checks reject address collisions, malformed widths,
missing or wrong-width typed outputs, unsupported memory expressions, and stale
generated artifacts. Debug-only export of an internal memory expression remains
open; raw expressions are the current escape hatch for values already visible
in the wrapper.

## Current limitations

The language is intentionally small. It does not currently provide arbitrary
combinational output declarations, multi-clock semantics, analog primitives,
or a fully proved semantic theory for every composition transform. Vendor
primitive mapping and physical timing are downstream evidence, not Lean
theorems of the source design.
