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

The first Yosys adapter handles one synchronous clock domain, either edge,
active-high or active-low synchronous reset, ordinary registers/enables, and a
basic width-normalized combinational subset. It currently blocks:

- asynchronous reset state, including async-assert/sync-release boundaries
  (keep these behind an `ExternalComponent` reset contract);
- resetless or mixed-reset state, enable-dominant synchronous-reset flops,
  inferred memories and latches;
- inout/tri-state ports and black boxes without explicit external contracts;
- signed four-state variable part-select (`$shiftx`) cells; and
- a module containing more than one clock/edge or reset domain.

Child instances remain in the neutral module and are not silently flattened
into local logic. The package checker derives exact child input-to-output
combinational summaries bottom-up, so registered-only feedback is accepted
without permitting combinational cycles. Hierarchy emission remains structural
external evidence; it does not yet claim a general kernel theorem equating an
arbitrary rendered wrapper with canonical flattening.

## KianV inventory

With the sibling KianV checkout used by this workspace:

```console
scripts/inventory_kianv.sh \
  ../kianv/gf180mcu-kianv-rv32ima-sv32 Evidence/KianV
```

The checked-in Markdown/JSON reports identify the `chip_core` configuration,
all source hashes, 74 reachable elaborated modules, rising/falling edge use,
reset cells, six memory-bearing modules, latches, instances, and structural
precheck blockers. `Evidence/KianV/import_coverage.md` separately records the
actual fail-closed translator result: currently 37 of 74 modules are accepted.
`Evidence/KianV/elaborated.json` is the exact hash-matched Yosys input for
per-module neutral translation; it is evidence, not a trusted Loom artifact.

The complete 74-module schema-v2 KianV package also serializes successfully as
a 17 MiB expression-DAG artifact and passes the trusted structural package
checker (74 modules, 134 child instances, 45,366 expression nodes). This does
not make the package behaviorally importable: 37 modules still declare at
least one blocker, so `importPackage` correctly cannot emit the complete SoC.

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
