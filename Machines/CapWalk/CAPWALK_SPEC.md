# Capability walk and fill engine

This directory contains the capability-table protocol model, its proved
safety properties, a Loom implementation, and an SoC integration surface.

## Protocol

`Protocol.lean` models cells, entries, cache lines, queries, fills,
duplication, revocation, and reuse. Handles encode a bounded slot and epoch;
the null value is excluded by the live-handle invariant.

The proved T-C1 through T-C6 family covers:

- handle layout and null rejection;
- exhaustive, ordered validation outcomes;
- rights/range narrowing and no authority amplification;
- descendant invalidation after lineage revocation;
- safe slot reuse through monotone epochs and sticky death; and
- fidelity of cache fill and backing-store views under the model invariant.

`ProtocolLib.lean` exposes stable restatements of the protocol and theorem
types used by downstream code.

## Hardware engine

`Engine.lean` implements the bounded table/cache controller as an open Loom
design. Requests and external-memory responses are explicit inputs. Values
returned from external storage are checked before they can authorize use;
safety claims do not treat DDR as trusted capability state.

The design declares its architectural outputs, keeps the MAC-key registers
internal to that interface, satisfies the synchronous-read and fast-evaluator
checks, and proves `fastRunOpen_agrees` for arbitrary input traces.
`selftest` exercises protocol-linked adversarial cases and the executable
model. `CapSoc.lean` supplies the LNP64mini integration surface.

## Evidence

Use the maintained ladder:

```sh
scripts/capwalk_ladder.sh
```

It checks the Lean model and engine, emission, simulation legs available on
the host, and the configured equivalence steps. `Emit.lean` also enforces the
memory-shape requirements before producing RTL.

## Security and implementation boundary

Architectural non-export of the key is proved at the generated module
interface. It is not protection against bitstream extraction or physical
attacks. The external-memory protocol can deny service, and liveness needs a
separate compliant-environment assumption. Generic authenticated backing
storage, arbitrary table scale, board-wrapper behavior, and physical timing
are not consequences of the protocol theorems.

Current source-level proof and simulation evidence is maintained in the
repository. Do not infer that the current repository head has a passing board
demo; the board status is tracked in `STATUS.md` and `fpga/zc702/README.md`.
