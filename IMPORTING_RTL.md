# Importing existing RTL into Loom

Loom's import path is deliberately fail-closed. A successful parse is not an
equivalence proof, and a successful RTL equivalence check is not physical
signoff. The workflow keeps those claims separate and binds every external
result to exact artifact hashes.

## Claim ladder

1. **Inventory PASS** means Yosys elaborated and classified the exact hashed
   sources, includes, defines, and selected top. Yosys and the inventory
   adapter remain untrusted.
2. **Neutral import accepted** means the adapter represented every encountered
   construct without a declared blocker. Loom then parses and checks the
   artifact before emission. For a schema-v2 package this includes exact child
   existence, input coverage, port directions and widths, unique drivers,
   hierarchy acyclicity, and exact bottom-up combinational dependency cycles.
   Unsupported constructs stop behavioral lowering.
3. **Loom compiler proof** connects the lowered `Design` transition to the
   emitted µVerilog AST. Clock edge, physical clock/reset names, and
   synchronous-reset polarity are explicit emission metadata; the compiler
   proves they do not change the abstract cycle/reset functions.
4. **RTL equivalence PASS** is external evidence that the original module and
   Loom-emitted module are behaviorally equivalent (sequentially when state
   exists) under the named assumptions. It is recorded per module with exact
   input/log hashes, tool version, invocation, and run ID. `FAIL` and `SKIP`
   never satisfy a required
   signoff item.
5. **Synthesis, STA/CDC, extraction, and LVS PASS** are separate downstream
   requirements. Generic Loom does not invent a PDK, standard-cell library,
   constraints, corners, or physical assumptions.

No earlier rung implies a later one.

## Supported path

For a small synthesizable module:

```console
python3 scripts/verilog_inventory.py \
  --top my_module --source-root "$PWD" --source rtl/my_module.sv \
  --json-out build/my_module.inventory.json \
  --markdown-out build/my_module.inventory.md \
  --elaborated-out build/my_module.yosys.json

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json build/my_module.yosys.json \
  --inventory build/my_module.inventory.json \
  --module my_module --output build/my_module.import.json

lake exe importModule build/my_module.import.json build/my_module.loom.v

python3 scripts/rtl_equivalence.py \
  --module-label my_module \
  --gold-top my_module --revised-top my_module \
  --gold-file rtl/my_module.sv --revised-file build/my_module.loom.v \
  --assumption "clock/reset correspondence and declared initialization contract" \
  --log build/my_module.equiv.log --output build/my_module.equiv.json
```

`scripts/test_import_adapters.sh` runs that entire path on an equivalent
fixture and verifies that an intentionally inequivalent fixture reports
`FAIL`.

For a closed elaborated hierarchy, use the package path:

```console
python3 scripts/yosys_to_loom_ir.py \
  --yosys-json build/my_soc.yosys.json \
  --inventory build/my_soc.inventory.json \
  --package-top my_soc --output build/my_soc.package.import.json

lake exe checkImportPackage build/my_soc.package.import.json
lake exe importPackage \
  build/my_soc.package.import.json build/my_soc.loom.v
```

Schema-v2 stores each module's expressions as a shared postorder table rather
than recursively duplicating its expression DAG. This keeps wide SoC package
artifacts bounded and makes every reference fail closed if it is forward or
out of range. The package emitter gives arbitrary child-input expressions to
a checked Loom body output and represents child outputs as unique body-input
nets. It emits deterministic source-module wrappers and HDL-safe names for
Yosys parameter specializations. Both stateless and stateful hierarchy
fixtures pass original-vs-emitted RTL equivalence; the equivalence adapter
flattens each selected top before constructing the miter.

`scripts/import_coverage.py` runs the same fail-closed translator over every
module in one identified elaborated artifact while loading that artifact only
once. Its `ACCEPTED` count is a conversion-progress metric, not an equivalence
or signoff claim.

The frontend also writes `build/my_module.import.json.manifest.json`. That
separate manifest avoids a self-hash paradox while binding every source,
inventory, elaborated JSON, and neutral-IR artifact to its path, byte count,
SHA-256 digest, exact invocation, tool version, and assumptions.

The neutral IR is in `Loom/Hw/ImportIR.lean`; its JSON parser is in
`Loom/Hw/ImportJson.lean`. It preserves source modules and child instances.
`lowerLocalDesign?` lowers module-owned logic into the normal `Design` graph;
`lowerComponent?` creates the checked component boundary. Checked package
assembly is in `Loom/Hw/ImportHierarchy.lean`; structural wrappers are
validated and rendered by `Loom/Hw/HierarchyEmit.lean`. The single-module CLI
explicitly refuses a module containing children, so it cannot emit dangling
symbolic nets while bypassing package checking.

Modules with no clock domains lower through `lowerStatelessDesign?` into the
same ordinary expression graph plus an executable no-state witness. Their
module kind is explicit in µVerilog, their exact text round-trips through the
checked parser, and emission has no clock/reset ports or event-control block.
`StatelessComponent.bind?` assigns nominal typed-domain ownership to the pins
without assigning any state element to that domain.

## Explicit four-state refinement

Ordinary Loom expressions are two-state. A source `x` or `z` therefore never
gets silently mapped to zero. Supply `--four-state-policy policy.json` to opt
into an implementation refinement. Every matching rule records a stable
`four_state_...` site identifier, source/module range, one of
`synthesis_dont_care`, `unreachable_decode`, `undriven_behavior`, or
`uninitialized_state_or_memory`, a zero/one fill, and a nonempty rationale.
Missing and multiply matching rules fail closed. The policy itself is included
as a hash-bound manifest artifact.

The same mechanism covers unsigned Yosys `$shiftx` variable part-selects:
out-of-range source bits use an explicit zero-fill policy, while
in-range bits are normalized to ordinary shifts and muxes. Signed `$shiftx`
and one-fill policies still fail closed: negative starting indices need a
separate exact normalization, and the current Yosys formal model only
validates the zero-fill case.

The trusted neutral-IR checker verifies that the chosen concrete value agrees
with every source-known bit before lowering it to an ordinary literal. For
external evidence, `scripts/rtl_equivalence.py --undef-policy zero|one`
applies the same named concretization to both sides. Such a PASS is evidence
for that declared implementation refinement, not unrestricted four-state RTL
equivalence. The focused fixture covers unclassified rejection, ambiguous
policy rejection, trusted known-bit checking, emission, and equivalence under
the selected policy. Generated Yosys `0.0-0.0` locations are represented as a
synthetic valid line 1; their stable site identifiers retain exact policy
selection.

For a large design, review intent in a compact source-level decision file and
expand it with `scripts/expand_four_state_policy.py`. The expander requires
every inventoried site to match exactly one decision, rejects unused or
overlapping decisions, and emits one exact `site`-bound rule per occurrence.
It records the coverage and decision SHA-256 digests in the result, so a
regenerated inventory cannot silently inherit stale classifications.

## Current fail-closed limits

The Yosys adapter handles one or more clock/edge domains, resetless state,
per-register active-high/active-low synchronous resets, both reset-dominant
and enable-dominant priority, ordinary register enables, and a basic
width-normalized combinational subset. It also accepts power-of-two `$mem_v2`
arrays with asynchronous reads, rising-edge writes, zero offset, ordinary
ordered-port collision behavior, and arbitrary per-bit write enables. ROMs
become pure mux logic. Writable words become bit-plane Loom memories, with an
explicit `memory_equivalence` relation consumed by
`scripts/rtl_equivalence.py --memory-map`; partial initial images retain a
trusted `PartialValue` refinement witness. Synchronous resets are made explicit in
each register's next-state graph and emitted in a genuinely resetless frame;
no synthetic common reset is introduced. It currently blocks:

- asynchronous reset state, including async-assert/sync-release boundaries
  (keep these behind an `ExternalComponent` reset contract);
- clocked-read, asynchronous-write, falling-edge-write, wide-continuation,
  transparent, or collision-X memory modes, and source latches;
- inout/tri-state ports and black boxes without explicit external contracts;
- signed four-state variable part-select (`$shiftx`) cells; and
- memories inside a module with more than one clock/edge domain until memory
  ownership is explicit (the current KianV mixed-edge module has no memory).

Single-domain modules lower through the ordinary local-design path. A
multi-domain package module instead emits one stateless combinational body and
one resetless state body per declared domain, then uses a checked structural
wrapper with explicit state nets. Every register must name exactly one domain.
Clock pins remain available to combinational cones, which is required for the
KianV controller's derived SDRAM clock. The package path is mandatory for this
split; the single-module CLI continues to fail closed.

Child instances remain in the neutral module and are not silently flattened
into local logic. The package checker derives exact child input-to-output
combinational summaries bottom-up, so registered-only feedback is accepted
without permitting combinational cycles. Hierarchy emission remains structural
external evidence; it does not yet claim a general kernel theorem equating an
arbitrary rendered wrapper with canonical flattening.

## KianV inventory

With the sibling KianV checkout used by this workspace:

```console
scripts/convert_kianv.sh \
  ../kianv/gf180mcu-kianv-rv32ima-sv32 build/kianv-conversion
```

This regenerates the inventory and exact-site four-state policy, checks and
emits the complete package, runs an Icarus elaboration smoke check when
available, and writes hashes for the neutral package, manifest, and emitted
RTL. To regenerate only the checked-in inventory reports:

```console
scripts/inventory_kianv.sh \
  ../kianv/gf180mcu-kianv-rv32ima-sv32 Evidence/KianV
```

Additional positional arguments are explicit Verilog defines and become part
of the elaborated artifact identity. For example, appending `SIM SYNTHESIS`
selects the fast-boot divider defaults while excluding simulation-only system
tasks from the synthesizable import. Never test a `SIM` upstream executable
against the default ASIC elaboration: in KianV those configurations reset the
UART divider to 174 and 1 respectively.

The checked-in Markdown/JSON reports identify the `chip_core` configuration,
all source hashes, 74 reachable elaborated modules, rising/falling edge use,
reset cells, six memory-bearing modules, latches, instances, and structural
precheck blockers. `Evidence/KianV/import_coverage.md` separately records the
policy-free fail-closed translator result: currently 42 of 74 modules are
accepted.
`Evidence/KianV/elaborated.json` is the exact hash-matched Yosys input for
per-module neutral translation; it is evidence, not a trusted Loom artifact.
`four_state_decisions.json` records 32 module-specific source-intent decisions;
the exact-site expander produces 279 hash-bound rules in
`four_state_policy.json`. With that policy, `import_coverage_policy.md` records
all 74 modules accepted, including the falling/rising-edge SDRAM controller.
The unrefined report remains checked
in separately so policy-dependent progress is never confused with ordinary
two-state acceptance.

The regenerated complete schema-v2 package contains all 74 reachable modules,
passes `checkImportPackage`, and emits all 150 wrapper/body artifacts. On the
current host the complete emission takes 0.67 seconds with about 241 MiB peak
RSS, and Icarus accepts the result as a complete `chip_core` syntax/elaboration
smoke check. Yosys per-bit write enables are represented exactly with ordinary
Loom word memories: each complete-word port value folds every earlier enabled
same-address mask, while provably distinct literal-address writes commute and
are grouped. The associative-cache specialization is consequently five word
memories with 180 logical writes, rather than the former 63 one-bit memories
and 4,284 ports. An iterative postorder executable lowering visits the neutral
DAG without retaining a dependent recursive `StateT` continuation per level.
Imported state names are injectively HDL-encoded and the neutral artifact
records each original-to-Loom register and memory correspondence. Internal
clock aliases select the exact matching input port at the module boundary.
These are complete import and structural-emission results, not a blanket
equivalence claim.

`scripts/kianv_bottom_up_equivalence.py` consumes the exact elaborated JSON,
neutral package, and emitted RTL and writes a SHA-256-bound result/log set. It
records register correspondence as a public source net plus bit offset, so a
Yosys-generated byte flip-flop can be related to its stable source-level slice
(for example, `mtimecmp[63:56]`). Immediate children are cut compositionally:
child outputs become common contract inputs and every child input becomes an
additional equivalence output. Thus a parent proves its local logic and exact
port binding without flattening already-proven child state at every ancestor.
`--flatten-module` is an explicit fallback for hierarchy whose direct flattened
cone is smaller than its port contract (the 32-bit logarithm specialization).

For example, after `scripts/convert_kianv.sh`:

```sh
python3 scripts/kianv_bottom_up_equivalence.py \
  --elaborated build/kianv-conversion/evidence/elaborated.json \
  --package build/kianv-conversion/chip_core.package.import.json \
  --emitted build/kianv-conversion/chip_core.loom.v \
  --external-contract Evidence/KianV/gf180_sram_external.json \
  --output-dir build/kianv-equivalence
```

The current bounded campaign proves 71 of 74 specializations directly and
records the GF180 wrapper as the exact named external contract. The logarithm
specialization also proves with the explicit flatten fallback (33/33 cells in
60 seconds). The remaining associative-cache specialization has produced no
counterexample but times out while proving its five mapped 32-word memory
banks; this is the sole open per-specialization equivalence obligation. The
compositional CPU specialization, `soc`, and whole `chip_core` boundaries all
prove. These counts are progress evidence, not total-conversion closure.

For an end-to-end xv6 check, the matched entry point is:

```sh
scripts/boot_kianv_xv6.sh \
  ../kianv/gf180mcu-kianv-rv32ima-sv32 build/kianv-xv6-loom
```

It generates a separately hash-bound `SIM SYNTHESIS` package rooted at `soc`,
checks and emits it, applies a semantics-preserving Yosys cleanup to collapse
neutral width-extension wires, compiles the result into KianV's pin-level
Verilator SDRAM/SPI/UART harness, and requires the normal xv6 shell markers.
The reference run reached the shell at exactly 222,410,634 modeled clocks, the
same cycle reported for upstream RTL. The matched `div_if` and `tx_uart`
specializations also pass the bottom-up equivalence runner. An intentional
negative differential run against the ASIC elaboration first diverged only at
the UART divider (ASIC reset 1 versus simulation reset 174), which verifies
that configuration identity is observable and enforced rather than silently
papered over.
The cleanup is operationally important: on the current host direct `-O3`
compilation of the trace-oriented neutral RTL remained in six multi-gigabyte
compiler jobs after ten minutes, whereas the cleaned model compiled in under
ten seconds. `MAX_CYCLES` and `KIANV_XV6_OBJDIR` override the simulation limit
and ignored Verilator object directory.

The GF180 512x8 SRAM is deliberately not converted into generic gates.
`Evidence.KianV.Gf180Sram.specification` gives its active-low masked,
synchronous old-data-read `ExternalComponent` contract. The accompanying
`Evidence/KianV/gf180_sram_external.json` binds the exact KianV wrapper, GDS,
LEF, blackbox, and all eight configured Liberty corners. The conversion
wrapper runs `scripts/verify_kianv_sram_external.py` and fails on a checkout,
size, or SHA-256 mismatch. Behavioral equivalence from those external bytes
to the contract remains a named signoff premise rather than a kernel theorem.

Do not describe KianV as converted until every required reachable module has
an accepted import and a per-module equivalence `PASS`, hierarchy has been
checked/emitted, and the selected downstream signoff plan has exact complete
coverage.

## Technology-neutral signoff interface

`Loom/Hw/Signoff.lean` represents artifacts, assumptions, tools, requirements,
and ordered results for import generation, RTL equivalence, compiler-to-model
checks, synthesized-netlist equivalence, STA, CDC, extraction, and LVS. A
report is complete only when it covers the plan's exact ordered requirement
list, uses the plan's exact artifact list, has complete tool identity, and
passes every required item. This is an evidence schema, not a claim that an
external EDA tool became part of Lean's trusted kernel.
