# LNP64mini Loom port

The Loom port preserves the small core's ordered state-machine behavior while
making inputs, memories, outputs, execution, and observation explicit in the
hardware EDSL.

## Source structure

- `Core.lean` defines the hardware `Design` and typed state declarations.
- `Harness.lean` runs the certified Design-derived simulator with behavioral
  DDR and GP environments and checks architectural outcomes.
- `HpMaster.lean`, `GpMaster.lean`, and `Soc.lean` form the single-core SoC.
- `HpArbiter.lean` and `DualSoc.lean` form the shared dual-core system.
- `Emit.lean` exposes guarded artifact generation and selftest commands.

## Semantic commitments

Expressions read pre-cycle state, rules execute in declared order, and later
writes win. Inputs are environment coordinates rather than registers owned by
the core. Large tables use Loom memories with explicit read timing and ordered
write ports. The output list is explicit; internal state is not exported merely
because it is a register.

LNP64mini has no hand-maintained cycle ISS. The shared-DAG simulator is derived
from `Design` and connected to the reference semantics by the generic evaluator
theorems. Tests read typed registers and memories through `DerivedRun`.

## Verification ladder

1. structural, declaration, and emission checks;
2. certified Design-derived execution with explicit architectural outcomes;
3. emitted RTL against Design-derived expectations;
4. post-synthesis resource and timing evidence; and
5. accounted board boot and network behavior.

A result on an earlier rung does not imply a later one. The current result of
each standing gate is in `STATUS.md`.

## Scope

The port is a bounded implementation used for verification and board
integration. It does not implement the complete LNP64 architecture, and its
serialized external memory interface is not a production coherent memory
hierarchy.
