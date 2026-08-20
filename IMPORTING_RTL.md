# Importing existing RTL into Loom

Loom's import path is deliberately fail-closed. A successful parse is not an
equivalence proof, and a successful RTL equivalence check is not physical
signoff. The workflow keeps those claims separate and binds every external
result to exact artifact hashes.

## Claim ladder

1. **Inventory PASS** means Yosys elaborated and classified the exact hashed
   sources, includes, defines, and selected top. Yosys and the inventory
   adapter remain untrusted.
2. **Neutral import accepted** means Loom parsed the JSON boundary and checked
   that every represented width, source location, clock/reset contract, and
   expression can lower to an ordinary `Loom.Hw.Design`. Unsupported
   constructs stop lowering.
3. **Loom compiler proof** connects the lowered `Design` transition to the
   emitted µVerilog AST. Clock edge, physical clock/reset names, and
   synchronous-reset polarity are explicit emission metadata; the compiler
   proves they do not change the abstract cycle/reset functions.
4. **RTL equivalence PASS** is external evidence that the original module and
   Loom-emitted module are sequentially equivalent under the named
   assumptions. It is recorded per module with exact input/log hashes, tool
   version, invocation, and run ID. `FAIL` and `SKIP` never satisfy a required
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

The frontend also writes `build/my_module.import.json.manifest.json`. That
separate manifest avoids a self-hash paradox while binding every source,
inventory, elaborated JSON, and neutral-IR artifact to its path, byte count,
SHA-256 digest, exact invocation, tool version, and assumptions.

The neutral IR is in `Loom/Hw/ImportIR.lean`; its JSON parser is in
`Loom/Hw/ImportJson.lean`. It preserves source modules and child instances.
`lowerLocalDesign?` lowers module-owned logic into the normal `Design` graph;
`lowerComponent?` creates the checked component boundary. Structural top
wrappers over exact child module artifacts are validated and rendered by
`Loom/Hw/HierarchyEmit.lean`.

## Current fail-closed limits

The first Yosys adapter handles one synchronous clock domain, either edge,
active-high or active-low synchronous reset, ordinary registers/enables, and a
basic width-normalized combinational subset. It currently blocks:

- asynchronous reset state, including async-assert/sync-release boundaries
  (keep these behind an `ExternalComponent` reset contract);
- resetless or mixed-reset state, enable-dominant synchronous-reset flops,
  inferred memories, and latches;
- clockless combinational-only module emission;
- inout/tri-state ports and black boxes without explicit external contracts;
- several Yosys logical/reduction/priority-mux/variable-shift cells; and
- a module containing more than one clock/edge or reset domain.

Child instances remain in the neutral module and are not silently flattened
into local logic. Hierarchy emission is structural external evidence; it does
not yet claim a general kernel theorem equating an arbitrary rendered wrapper
with canonical flattening.

## KianV inventory

With the sibling KianV checkout used by this workspace:

```console
scripts/inventory_kianv.sh \
  ../kianv/gf180mcu-kianv-rv32ima-sv32 Evidence/KianV
```

The checked-in Markdown/JSON reports identify the `chip_core` configuration,
all source hashes, 74 reachable elaborated modules, rising/falling edge use,
reset cells, six memory-bearing modules, latches, instances, and current
import blockers. `Evidence/KianV/elaborated.json` is the exact hash-matched
Yosys input for per-module neutral translation; it is evidence, not a trusted
Loom artifact.

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
