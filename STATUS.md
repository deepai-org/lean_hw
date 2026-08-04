# Project status

Checked against repository head on **2026-08-04**. This file is a current
snapshot, not a development diary. Historical milestones belong in Git and
[`CHANGELOG.md`](CHANGELOG.md); detailed hardware campaigns belong in their
machine and board specifications.

## Gate status

| Check | Current result | Notes |
|---|---|---|
| `lake build` | **PASS** | Rechecked on 2026-08-04; warnings remain. |
| `lake exe audit` | **PASS** | Reports 1,061 clean ledger theorems, 21 whitelisted unsafe declarations, 6 `implemented_by` replacements, 0 source `partial`, and 0 `extern`. |
| `lake test` | **FAIL** | `Tests.MultiPort`, `Tests.MemInitOk`, `Tests.MemTarget`, `Tests.Outputs`, `Tests.ArtifactCert`, and `Tests.NamedCertificate` have not caught up with mandatory `Design.outputs`. |
| `scripts/quality.sh` | **FAIL** | Missing SPDX headers in `Machines/PingPong/PingPong.lean` and `Machines/PingPong/PingPongArtifact.lean`. |
| `scripts/ci.sh` / `scripts/reproduce.sh` | **FAIL** | They build the `Tests` target, which currently contains the stale test modules above. GitHub Actions also runs `scripts/quality.sh` before `scripts/ci.sh`. |
| `scripts/build_verified_release.sh` | **BLOCKED before theorem checking** | Its first substantive gate is `scripts/quality.sh`, which currently fails. |
| Optional Yosys/CaDiCaL/Icarus checks | **Host-dependent** | Scripts self-skip when tools are missing. A zero exit from a wrapper does not by itself prove every optional check executed. |

The passing audit is meaningful but narrower than a green CI build: it checks
compiled `Loom`/`Machines` declarations and trust policy, while the current
test and packaging regressions remain real.

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
- The checked audit inventory currently contains 21 unsafe declarations and 6
  executable replacements. They are generator/tool performance paths; the
  release theorem is phrased over reference definitions and kernel-checked
  witnesses.
- The concrete release renderer and denotation cover registers, memory images
  and ordered writes, SSA wires, and outputs. Exact host-file association uses
  the separate binder described in `REPRODUCING.md`.
- The netlist equivalence checker has a proved CNF expression encoding for its
  declared fragment and rechecks UNSAT LRAT certificates. The driver,
  netlist/cell interpretation, executable bit-blaster replacement, unsupported
  `shl`/`shr`/`slt`, exclusions, and acknowledged defects remain explicit.
- Memory-target diagnostics are parameterized by declared target profiles;
  they predict realizability but do not prove a synthesis mapping.

## Hardware integration

The current LNP64mini integration head is **not hardware-green**:

- cross-repository opcode agreement is restored for 70 shared opcodes;
- the rebuilt guest passes the zero-trap emulator gate;
- on silicon the trap count is restored from 10,722 to zero; but
- the guest still does not reach the network: core 0 deterministically halts
  and core 1 remains parked in a futex wait after only 20 retirements.

The next diagnostic is to read the in-guest console ring immediately after a
board run before guessing at another cause. No NetBSD, Ethernet, SMP, epoch,
or capability board result is currently accepted for this head.

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
- Current roadmap: [`NEXTSTEPS.md`](NEXTSTEPS.md)
- Capability and assurance gaps: [`LOOM_GAPS.md`](LOOM_GAPS.md)
- Hardware record: [`fpga/zc702/README.md`](fpga/zc702/README.md) and the
  specifications below each `Machines/` subtree
