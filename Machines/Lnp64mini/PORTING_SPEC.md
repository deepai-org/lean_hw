# LNP64mini Loom port

The Loom port preserves the small core's ordered state-machine behavior while
making inputs, memories, and outputs explicit in the hardware EDSL.

## Source structure

- `Core.lean` defines the hardware `Design` and emitted architectural state.
- `Iss.lean` is the executable instruction-set/state-transition oracle.
- `Harness.lean` drives agreement checks.
- `HpMaster.lean`, `GpMaster.lean`, and `Soc.lean` form the single-core SoC.
- `HpArbiter.lean` and `DualSoc.lean` form the shared dual-core system.
- `Emit.lean` performs guarded artifact generation.

## Semantic commitments

Expressions read pre-cycle state, rules execute in declared order, and later
writes win. The rule order mirrors the phases of the core transition rather
than relying on implicit scheduling. Register-file updates, memory responses,
priority selection, traps, and retirement must agree with the ISS at the
architectural observation points.

Inputs such as memory and command responses are D15 environment coordinates.
They are not registers owned by the core. Large tables use Loom memories with
explicit read latency and ordered write ports. The output list is explicit;
internal state is not exported merely because it is a register.

## Verification ladder

The maintained sequence is:

1. structural and emission checks;
2. ordinary semantics against FastEval;
3. EDSL trace against the ISS;
4. emitted RTL against the same workload;
5. post-synthesis checks and resource/timing reports; and
6. board boot and network behavior.

A result on an earlier rung does not imply a later one. In particular, the
current source/opcode checks pass while the combined board workload does not;
see `STATUS.md`.

## Known scope

The port is a bounded implementation used for verification and FPGA work. It
does not implement the entire LNP64 architecture, and its serialized external
memory interface is not a model of a coherent production memory hierarchy.
