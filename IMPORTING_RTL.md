# Importing RTL into Loom

Loom has a fail-closed, module-preserving Verilog/SystemVerilog import path.
Yosys is an untrusted normalization frontend: Loom validates the resulting
typed import IR before lowering it. Unsupported constructs are rejected, never
approximated silently.

## Keep the claims separate

1. **Inventory PASS**: the exact source hash elaborated and every reachable
   module/cell was classified.
2. **Import PASS**: Loom's checked IR accepted the module or hierarchy and
   emitted a typed Design/package.
3. **Compiler theorem**: imported Loom logic uses the ordinary certified
   compiler and deterministic renderer.
4. **RTL equivalence PASS**: an external tool compared original and emitted
   RTL under the recorded configuration and assumptions.
5. **Physical PASS**: synthesis, STA/CDC, extraction, DRC, and LVS are separate
   downstream evidence.

No earlier step implies a later one.

## Basic workflow

Inventory a source tree:

```console
scripts/inventory_kianv.sh SOURCE_ROOT OUTPUT_DIR
```

For the checked-in fixtures, run:

```console
scripts/test_import_adapters.sh
```

The frontend records source locations, exact input hashes, Yosys identity,
module hierarchy, ports, state, memories, clock edge, reset behavior, and every
unsupported construct. `Tools/ImportModule.lean` handles one leaf;
`Tools/ImportPackage.lean` is required for hierarchy or mixed-edge modules.
Single-module emission refuses designs with child instances.

The complete KianV conversion is:

```console
scripts/verify_kianv_conversion.sh \
  ../kianv/gf180mcu-kianv-rv32ima-sv32 \
  build/kianv-total-conversion
```

It regenerates the inventory and package, emits RTL, runs bottom-up equivalence,
and writes deterministic JSON and Markdown evidence.

## Supported semantics

The current checked path supports:

- combinational and stateful modules;
- hierarchy with exact child port expressions;
- rising- and falling-edge domains, including mixed-edge source modules;
- synchronous active-high/active-low and per-register resets;
- resetless state;
- arithmetic, comparisons, logic, reductions, muxes, shifts, and slices;
- ROM and writable memories with masked multi-port updates; and
- explicit external-component contracts.

Mixed-edge modules lower to a stateless combinational body plus one
state-owning Design per clock/edge domain. Their checked wrapper binds shared
state and ports explicitly; the importer does not pretend they are one
positive-edge Design.

Writable memories preserve ordered same-address masked-write behavior. Loom
commutes writes only when literal addresses prove them distinct. Equivalence
uses exact word relations, including base state and unbounded one-step
preservation.

## Four-state source constructs

Loom's core semantics are two-state. Stable `x`/`z` sites and unsigned
`$shiftx` may be imported only through a reviewed, hash-bound refinement
policy. The policy names each source site and chooses concrete values only for
unknown bits; the checker proves every known bit is preserved. Missing,
ambiguous, stale, signed, or otherwise unsupported cases remain blocked.

This is an explicit implementation choice, not a theorem that arbitrary
four-state RTL equals a two-state circuit. Apply the same named concretization
to both sides of any external equivalence check.

## Hierarchy and evidence

The package checker validates every module, port direction and width, child
binding, driver, state owner, expression DAG, and bottom-up combinational
dependency order. Emission preserves safe source hierarchy names and uses an
injective encoding only for names that are not portable Verilog identifiers.

Per-module equivalence evidence records:

- exact source, elaboration, package, emitted-RTL, and contract hashes;
- tool version and invocation;
- proof mode and assumptions;
- every reachable specialization; and
- explicit `PASS`, `FAIL`, or `SKIP`.

The evidence generator rejects partial reports. External equivalence is
corroboration around Loom's checked path, not a new kernel theorem.

## KianV result

For the pinned KianV checkout, the reviewed policy accepts all 74 reachable
specializations. Bottom-up closure records:

- 73 Loom-logic equivalence passes;
- one exact GF180 SRAM external contract;
- 72 compositional hierarchy proofs plus one explicit flatten fallback; and
- exact relational proofs for all memory-bearing specializations.

The CPU, `soc`, and `chip_core` boundaries pass. The five-bank associative
cache includes all 160 words (2,016 state bits); no memory bit is omitted.
The concise result is
[`Evidence/KianV/equivalence.md`](Evidence/KianV/equivalence.md), with the
machine-readable record beside it.

The separately hash-bound simulation configuration boots the pinned xv6 image
through KianV's SDRAM/SPI/UART harness and reaches the shell at the same modeled
clock as upstream RTL. Reproduce it with:

```console
scripts/boot_kianv_xv6.sh \
  ../kianv/gf180mcu-kianv-rv32ima-sv32 build/kianv-xv6-loom
```

That is dynamic evidence for one configuration, not a universal proof.

## External memories and physical handoff

The GF180 SRAM is represented by a typed behavioral contract plus exact wrapper,
GDS, LEF, blackbox, and Liberty identities. Those foundry bytes satisfying the
contract is a named external premise.

Generate the fabrication-oriented handoff with:

```console
scripts/prepare_kianv_physical.sh \
  ../kianv/gf180mcu-kianv-rv32ima-sv32 build/kianv-physical
```

The generator restores the configured pad count and foundry SRAMs, threads
power pins, translates the 21 fixed macro paths, applies recorded routing and
antenna controls, and binds every input/output byte in a manifest. Its verifier
checks the powered hierarchy, SRAM path set, floorplan correspondence, selected
diode connection, and configuration hashes before a physical flow starts.

This produces a checked handoff, not fabrication signoff. A clean pinned
LibreLane run and review of STA, CDC, DRC, LVS, antenna, PDN, and
manufacturability reports remain required. Current readiness is stated in
[`STATUS.md`](STATUS.md).

## Technology-neutral signoff records

[`Loom/Hw/Signoff.lean`](Loom/Hw/Signoff.lean) defines typed artifacts,
assumptions, tools, requirements, and ordered results for import, equivalence,
synthesis, timing/CDC, extraction, and LVS. A report passes only when it uses
the plan's exact artifacts, identifies every tool/run, covers every required
item exactly once, and contains no required non-PASS result.

The schema lets Loom fail closed at its extension boundary. It does not make an
external EDA tool part of Lean's trusted kernel.
