# Project status

Checked against repository head on **2026-08-10**. This file is a current
snapshot, not a development diary. Historical milestones belong in Git and
[`CHANGELOG.md`](CHANGELOG.md); detailed hardware campaigns belong in their
machine and board specifications.

## Gate status

| Check | Current result | Notes |
|---|---|---|
| `lake build` | **PASS** | Rechecked on 2026-08-10; warnings remain. |
| `lake exe audit` | **PASS** | Rechecked on 2026-08-10; reports 1,061 clean ledger theorems, 19 whitelisted unsafe declarations, 5 `implemented_by` replacements, 0 source `partial`, and 0 `extern`. |
| `lake test` | **PASS** | Rechecked on 2026-08-10, including runner, coverage, identity, and certified-DAG regressions. |
| `scripts/quality.sh` | **PASS** | Rechecked on 2026-08-10. |
| `scripts/emit_all.sh --check` | **PASS** | Rechecked twice on 2026-08-10: the first run correctly rejected stale ignored RTL, and the second reproduced the regenerated artifacts byte-for-byte. |
| `scripts/ci.sh` | **PASS** | Rechecked on 2026-08-09, including the explicit 528-second Epoch BMC, audit, emissions, debug map, round trip, release binding, and LRAT cross-check. |
| `scripts/reproduce.sh` | **NOT RECHECKED** | The broader reproduction wrapper remains a separate unrerun gate; optional external checks are host-dependent. |
| `scripts/build_verified_release.sh` | **NOT RECHECKED** | No current release rebuild is claimed by this snapshot. |
| Optional Yosys/CaDiCaL/Icarus checks | **Host-dependent** | Scripts self-skip when tools are missing. A zero exit from a wrapper does not by itself prove every optional check executed. |

`Machines.Epoch.Bmc` is an explicit CI target rather than part of the default
`Machines` umbrella. This keeps ordinary builds lightweight without dropping
the bounded-model-check proof from the standing gate.

The full reproduction and release workflows remain separate, explicitly
unrerun gates.

## Formal verification state

- The LNP64-µ public ledger imports T1–T9, the machine invariant assembly, and
  R-MC from `Machines/Lnp64u/Theorems/Ledger.lean`.
- `lake exe audit` classifies all 1,061 ledger theorems as clean and finds no
  unapproved project axioms, no `native_decide`/trusted-compiler dependency,
  and no disallowed `sorry` outside the permitted theorem/WIP policy.
- R-MC supplies an unbounded simulation from the LNP64-µ machine model to the
  reachable compiled EDSL transition system, including reset and all modeled
  retirement arms.
- The generic compiler/emission proof covers the EDSL-to-µVerilog module
  semantics. Open-design cycle semantics and input/output support also exist.
- `Tools/VerifiedRelease.lean` defines the combined Acc8/LNP64-µ release
  theorem. Its named LNP64-µ consequences are authority confinement,
  machine-wide W^X, lineage-ledger conservation, and budget boundedness.
- `Tools/ReleaseAudit.lean` requires the combined theorem's axiom closure to
  be exactly `propext`, `Classical.choice`, and `Quot.sound` when the release
  command builds it.

The release theorem is not a filesystem, synthesis, P&R, or silicon theorem.
See [`TCB.md`](TCB.md).

## Tool and artifact state

- Lean is pinned to 4.28.0; Mathlib and transitive dependencies are pinned by
  `lake-manifest.json`.
- The checked audit inventory currently contains 19 unsafe declarations and 5
  executable replacements. They are generator/tool performance paths; the
  release theorem is phrased over reference definitions and kernel-checked
  witnesses.
- The concrete release renderer and denotation cover registers, memory images
  and ordered writes, SSA wires, and outputs. Exact host-file association uses
  the separate binder described in `REPRODUCING.md`.
- There is currently no post-synthesis equivalence implementation in Loom. A
  future checker is scoped to a technology-neutral logical netlist; synthesis
  formats, vendor primitives, mapped netlists, and their conversion remain
  external evidence.
- Memory-target diagnostics are parameterized by explicit profiles from the
  separate `Evidence` library; they predict realizability but do not prove a
  synthesis mapping. Generic RTL emission selects no target.
- The primary LNP64mini simulator is generated from `Design`, prepares the
  certified shared DAG fail-closed, and drives its behavioral environment from
  generated core state. That environment now resolves typed register handles
  once into flat-state slots; missing or stale-width handles fail preparation,
  and generic slot-read theorems connect the resulting values to `Agree`.
  The independent ISS remains available as a differential oracle. The default
  lockstep compares the fail-closed
  `Design.coords` plan. The hand-maintained comparator and duplicate coverage
  tables have been removed. Explicit ISS value bindings derive register and
  memory names and widths from the Design's typed handles; intentional memory
  exclusions do the same.
- LNP64mini's GP master, HP master, and HP arbiter now declare their inputs and
  state through typed handles. Their executable expressions, environment
  adapters, and outcome checks reuse those handles instead of repeating
  coordinate names and widths. Their duplicate ISS transition functions are
  gone; directed tests now assert handshake, routing, and reservation outcomes
  on the Design semantics.
- Open-machine environment adapters use heterogeneous typed `InputBinding`s;
  LNP64mini core/components and Substrate S0 no longer dispatch inputs through
  repeated string/width match tables. The core smoke battery now checks seven
  architectural scenarios on the certified Design-derived simulator rather
  than treating sampled Design/ISS agreement as its success criterion.
- LNP64mini's domain, fail-stop, data-cache, SMP, slot-capacity, MMU,
  subword, ALU-gap, gate, preemption, MMU-identity, and refusal-conformance
  campaigns now consume typed `DerivedRun` observations. Preemption additionally
  audits every
  observed thread switch through resolved register/memory slots. The old
  `MiniIss` remains behind the not-yet-migrated gate-stress, fault/sentinel
  conformance, capability-transfer, trace, opcode-matrix, relocation, and
  explicit oracle-diagnostic commands. This is the current migration pause
  boundary; deleting `MiniIss` before those commands move or are deliberately
  retired would remove useful coverage.
- Substrate S0 and S13 no longer maintain second transition functions. Their
  tests use the universally related generated evaluators and check direct
  architectural outcomes through 100,008 S13 cycles and the complete
  33-command S0 trace. S0's command adapter derives input names from typed
  handles.
- `Loom.Runner` supplies the shared differential-run control and structured
  result contract used by Acc8, LNP64mini core/components, and FastEval
  corroboration. Acc8's bespoke comparator/recursive runner and LNP64mini's
  parallel evaluator entry points are gone; closed coverage gaps fail by name.
- `Loom.Artifact` binds observations to exact bytes and writes deterministic
  text only when bytes change. Generic shell helpers cover command capture and
  freshness; external workflows can create and verify SHA-256 identity
  manifests with `scripts/artifact_identity.py`.
- LNP64mini's generated debug map and core share a lightweight typed interface
  for observed registers, so the runtime generator stays cheap without
  redeclaring debug names and widths. Board transport remains external.
- Loom provides footprint-inferred `ExprProperty` state properties and general
  typed `TransitionProperty` before/after relations. LNP64mini proves with the
  latter that waking a parked thread preserves its ordinary resume PC and gate
  continuation metadata for every slot and stack depth.
- Runner mismatch output is flushed immediately. `emit_all.sh` uses the shared
  diagnostic helper, reports the exact failed command and output, and attaches
  a digest of the emitted artifact set to its successful result.

## Hardware integration

The current LNP64mini integration head is **not hardware-green**:

- cross-repository opcode agreement is restored for 70 shared opcodes;
- the rebuilt guest passes the zero-trap emulator gate;
- silicon reports zero traps; but
- the guest still does not reach the network: core 0 deterministically halts
  and core 1 remains parked in a futex wait after only 20 retirements.

Raw console-ring data shows each guest byte write replicated into a 64-bit
word at stride eight while adjacent 32-bit metadata is correct. Guest C,
clang, the Loom design, ISS, and emitted-RTL simulation all specify the
expected packed single-lane write. The remaining mismatch is in the physical
HP AXI path or a downstream artifact; the next diagnostic is a tiny
known-pattern write-and-halt probe read back over JTAG. No NetBSD, Ethernet,
SMP, epoch, or capability board result is currently accepted for this head.

## Property limits that remain open

- T5 erases timing through destuttering and is conditional on its isolation,
  agreement, code-locality, W^X-disjointness, and top-priority hypotheses.
- T6/T7 are conditional scheduler results, not global liveness under arbitrary
  memory stalls, interrupts, clock gating, or platform failures.
- The model is two-state and begins from a mathematical reset state.
- External DMA, interrupts, debug, MMU/IOMMU behavior outside a modeled
  machine, and hostile SoC agents are not silently included.
- Electrical reset, metastability physics, timing closure, power, analog
  effects, and physical side channels remain outside the core theorems.

The longer adversarial analysis is [`TRUST.md`](TRUST.md).

## Where to look next

- Release claim and TCB: [`TCB.md`](TCB.md)
- Independent reproduction: [`REPRODUCING.md`](REPRODUCING.md)
- Ordered unfinished work: [`ROADMAP.md`](ROADMAP.md)
- Hardware record: [`fpga/zc702/README.md`](fpga/zc702/README.md) and the
  specifications below each `Machines/` subtree
