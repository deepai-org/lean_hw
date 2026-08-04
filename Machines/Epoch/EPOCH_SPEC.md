# Epoch engine

The epoch engine implements bounded freshness, poison, and invalidation for
two local replicas. The directory contains an abstract protocol, a Loom
engine, a refinement proof, bounded checks, and LNP64mini integration.

## Protocol

`Protocol.lean` defines epoch cells, per-core replicas, checks, bumps,
acknowledgements, saturation, and poison. The core safety results establish:

- stale references remain invalid after a completed bump;
- a saturated cell is permanently dead;
- poison is sticky and rejects future uses;
- failure outcomes follow the defined precedence;
- epochs and replicas are monotone; and
- operations concurrent with an unfinished bump are not over-constrained.

`ProtocolLib.lean` provides stable theorem restatements. `Bounded.lean` and
`Bmc.lean` supply the finite executable/model-checking view.

## Hardware and refinement

`Engine.lean` is an open Loom design with on-chip cell and replica memories,
two request paths, local check responses, and a bump FSM that broadcasts
invalidation and waits for acknowledgements. Both the normal and tiny
instances satisfy the synchronous-read and FastEval checks, with proved
open-run agreement.

`Refines.lean` relates the hardware state machine to the protocol through an
abstraction and proves the cycle cases needed by the refinement. `EpochSoc.lean`
connects the engine to the LNP64mini SoC through its MMIO-facing integration.

## External-state rule

Safety-critical freshness state is checked on chip. External memory is an
adversarial input unless a separate composition or rely condition is supplied;
a value fetched from it cannot become authority merely because a bus returned
it. Liveness cannot be unconditional because an environment may never reply.

Initialization deliverability is checked before emission. A nonzero logical
image that the selected physical memory class cannot load is rejected rather
than treated as board state.

## Evidence and current status

Run:

```sh
scripts/epoch_ladder.sh
```

This is the maintained source/model/emission/simulation ladder. The protocol
and refinement artifacts are current. There is no accepted epoch board result
for the present hardware head; consult `STATUS.md` and the ZC702 README.

The model is bounded and target-specific integration remains outside its
theorems. It does not prove an arbitrary external memory, AXI fabric, CDC
wrapper, or physical implementation correct.
