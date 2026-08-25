# Project status

Current snapshot: **2026-08-25**.

## Gates

| Check | Result | Current evidence |
| --- | --- | --- |
| `lake test` | **PASS** | 8,295 jobs on 2026-08-25 |
| `scripts/quality.sh` | **PASS** | 2026-08-25 |
| `lake exe audit` | **PASS** | 36 inventoried `unsafe`, 9 reviewed `implemented_by`, 0 `partial`, 0 `extern` |
| Import adapter suite | **PASS** | all positive, equivalence, and fail-closed negative fixtures |
| `Machines.Epoch.Bmc` | **PASS** | explicit CI proof; 664 seconds on 2026-08-25 |
| `scripts/ci.sh` | **PARTIAL RECHECK** | build, BMC, downstream smoke, import adapters, and audit passed; the run was intentionally stopped before its final emission/round-trip gates to merge immediately |
| `lake exe releaseAudit` | **PASS** | last complete run 2026-08-12; exact axiom closure below |
| `scripts/emit_all.sh --check` | **PASS** | last complete run 2026-08-17 |
| `scripts/reproduce.sh` | **NOT RECHECKED** | host-dependent broader reproduction wrapper |
| `scripts/build_verified_release.sh` | **NOT RECHECKED** | no fresh full release rebuild is claimed at this snapshot |

Optional tools may report `SKIP`; a wrapper's zero exit is not evidence that a
skipped check passed. `Machines.Epoch.Bmc` deliberately remains outside the
ordinary `Machines` umbrella because of its high time and memory cost.

## What works

- One typed `Design` supplies synchronous semantics, proofs, certified DAG
  execution, deterministic technology-neutral Verilog, and artifact metadata.
- The compiler simulation transports arbitrary Design invariants to compiled
  µVerilog behavior.
- Selected release artifacts are theorem-bound to exact rendered bytes.
- Expressions include multiplication, widening multiplication, division,
  remainder, concatenation, shifts, comparisons, slices, and extensions.
- Packed nominal structs may nest and work in registers, ports, memories, and
  channels; partial packed-register field writes are checked.
- Typed components, streams, buses, memories, register maps, arbiters,
  pipelines, plugins, and reusable hierarchy scale to CPU-sized assemblies.
- Typed multiclock Systems use schedule-quantified semantics, certified channel
  realizations, compositional fragment projection, explicit timing/reset
  contracts, and complete neutral physical-intent inventories.
- External components and islands have typed contracts, exact byte identities,
  named assumptions, and fail-closed substitution/coverage checks.
- The RTL importer preserves modules and clock/reset domains, accepts the full
  pinned 74-module KianV design under an explicit four-state policy, and has
  complete bottom-up equivalence evidence.

## Formal claim

The publication declaration is:

```lean
theorem Loom.Release.Theorems.verifiedReleases :
  Nonempty Loom.Release.Theorems.VerifiedReleases
```

Its checked axiom closure is exactly:

```text
propext
Classical.choice
Quot.sound
```

It covers fixed Acc8, LNP64-µ, and portable two-clock artifacts. See
[`TCB.md`](TCB.md) for the exact boundary and
[`REPRODUCING.md`](REPRODUCING.md) for commands.

## Multiclock status

The stock path provides same-clock FIFOs, portable Gray FIFOs, independent
flush/recovery, conservative and full-rate registered sink presentation,
schedule replay, channel conservation/order proofs, and reusable fragment
theorem projection. Generated artifacts carry crossing, timing, reset,
storage, and physical-obligation manifests.

The digital proof does not establish metastability resolution, MTBF, target
constraint interpretation, placement, or timing closure. Target RAM and
synchronizer substitutions remain named assumptions. The openXC7/Zynq-7000
profile rejects the known-bad inferred independent-clock RAM mode above 36
bits; this is an evidence-layer policy, not generic Loom semantics.

The ZC702 multiclock and typed-SoC gauntlets have retained formal, routed, and
silicon evidence, including 100-million-transfer CDC campaigns and a
million-transfer typed composition tile. Optional Vivado CDC reporting remains
an honest `SKIP` on the available installation because its Zynq-7000 part
database is absent.

## RTL import and KianV

The checked KianV package covers all 74 reachable specializations: 73
Loom-logic equivalence passes and one exact GF180 SRAM external contract. The
emitted `soc` boots the pinned xv6 image in the upstream pin-level harness at
the matched modeled clock. Evidence is under [`Evidence/KianV`](Evidence/KianV).

The generated GF180 physical handoff validates hierarchy, 21 SRAM macro paths,
power integration, floorplan translation, selected antenna repair, and exact
artifact hashes. The first full physical run found one SRAM-edge spacing site
and two marginal antenna markers; the targeted fixes are generated and checked,
but a clean pinned LibreLane rerun remains the fabrication-release gate.

## Boundaries and remaining work

Loom does not currently prove:

- post-synthesis or extracted-netlist equivalence;
- external IP, FPGA primitives, foundry macros, or EDA tools;
- timing closure, electrical reset delivery, metastability/MTBF, or silicon;
- liveness without explicit clock/service assumptions; or
- complete semantic separate compilation of arbitrary emitted hierarchy.

The importer is intentionally tied to a Yosys normalization adapter at its
untrusted frontend boundary; Loom's accepted IR, semantics, compiler, and
signoff schema are not Yosys-specific. Unsupported RTL remains fail-closed.

Near-term unfinished work is ordered in [`ROADMAP.md`](ROADMAP.md); the intended
destination and scope are in [`PLATONIC.md`](PLATONIC.md).
