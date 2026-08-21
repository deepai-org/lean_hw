#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "$0")/.."

python3 -m py_compile scripts/verilog_inventory.py scripts/yosys_to_loom_ir.py \
  scripts/import_coverage.py scripts/expand_four_state_policy.py \
  scripts/rtl_equivalence.py scripts/kianv_bottom_up_equivalence.py \
  scripts/kianv_equivalence_evidence.py scripts/test_kianv_bottom_up_runner.py \
  scripts/test_kianv_equivalence_evidence.py scripts/kianv_physical_handoff.py \
  scripts/verify_kianv_physical_handoff.py

python3 scripts/test_kianv_bottom_up_runner.py
python3 scripts/test_kianv_equivalence_evidence.py

if ! command -v yosys >/dev/null 2>&1; then
  echo "import adapters: SKIP (yosys unavailable)"
  exit 0
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

python3 scripts/verilog_inventory.py \
  --top fixture_gold \
  --source-root "$PWD" \
  --source Tests/fixtures/equiv_gold.v \
  --json-out "$work/inventory.json" \
  --markdown-out "$work/inventory.md" \
  --elaborated-out "$work/elaborated.json"

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$work/elaborated.json" \
  --inventory "$work/inventory.json" \
  --module fixture_gold \
  --output "$work/fixture.import.json"

python3 scripts/import_coverage.py \
  --yosys-json "$work/elaborated.json" \
  --inventory "$work/inventory.json" \
  --json-out "$work/coverage.json" \
  --markdown-out "$work/coverage.md"

python3 - "$work/coverage.json" <<'PY'
import json
import sys
report = json.load(open(sys.argv[1], encoding="utf-8"))
assert report["summary"] == {
    "accepted_modules": 1, "blocked_modules": 0, "module_count": 1}
PY

lake exe importModule "$work/fixture.import.json" "$work/fixture.loom.v"

python3 scripts/rtl_equivalence.py \
  --module-label fixture_import \
  --gold-top fixture_gold \
  --revised-top fixture_gold \
  --gold-file Tests/fixtures/equiv_gold.v \
  --revised-file "$work/fixture.loom.v" \
  --assumption "clock and active-high synchronous reset ports correspond" \
  --log "$work/import-pass.log" \
  --output "$work/import-pass.json"

python3 scripts/verilog_inventory.py \
  --top fixture_active_low \
  --source-root "$PWD" \
  --source Tests/fixtures/equiv_active_low.v \
  --json-out "$work/active-low.inventory.json" \
  --markdown-out "$work/active-low.inventory.md" \
  --elaborated-out "$work/active-low.elaborated.json"

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$work/active-low.elaborated.json" \
  --inventory "$work/active-low.inventory.json" \
  --module fixture_active_low \
  --output "$work/active-low.import.json"

lake exe importModule "$work/active-low.import.json" "$work/active-low.loom.v"

python3 scripts/rtl_equivalence.py \
  --module-label fixture_active_low_import \
  --gold-top fixture_active_low \
  --revised-top fixture_active_low \
  --gold-file Tests/fixtures/equiv_active_low.v \
  --revised-file "$work/active-low.loom.v" \
  --assumption "falling-edge clock and active-low synchronous reset ports correspond" \
  --log "$work/active-low.equiv.log" \
  --output "$work/active-low.equiv.json"

python3 scripts/verilog_inventory.py \
  --top import_clock_alias \
  --source-root "$PWD" \
  --source Tests/fixtures/import_clock_alias.v \
  --json-out "$work/clock-alias.inventory.json" \
  --markdown-out "$work/clock-alias.inventory.md" \
  --elaborated-out "$work/clock-alias.elaborated.json"

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$work/clock-alias.elaborated.json" \
  --inventory "$work/clock-alias.inventory.json" \
  --module import_clock_alias \
  --output "$work/clock-alias.import.json"

lake exe importModule "$work/clock-alias.import.json" "$work/clock-alias.loom.v"

grep -q 'input wire clk_osc' "$work/clock-alias.loom.v"
if grep -qE '^  reg .* q;' "$work/clock-alias.loom.v"; then
  echo "import adapters: output alias reused as an internal register" >&2
  exit 1
fi
python3 - "$work/clock-alias.import.json" <<'PY'
import json
import sys
module = json.load(open(sys.argv[1], encoding="utf-8"))["module"]
assert module["register_equivalence"][0]["original"] == "q"
assert module["register_equivalence"][0]["loom"].startswith("__loom_reg_")
PY

python3 scripts/rtl_equivalence.py \
  --module-label fixture_clock_alias_import \
  --gold-top import_clock_alias \
  --revised-top import_clock_alias \
  --gold-file Tests/fixtures/import_clock_alias.v \
  --revised-file "$work/clock-alias.loom.v" \
  --assumption "the exact input-port clock alias is retained" \
  --log "$work/clock-alias.equiv.log" \
  --output "$work/clock-alias.equiv.json"

python3 scripts/verilog_inventory.py \
  --top import_logic \
  --source-root "$PWD" \
  --source Tests/fixtures/import_logic.v \
  --json-out "$work/logic.inventory.json" \
  --markdown-out "$work/logic.inventory.md" \
  --elaborated-out "$work/logic.elaborated.json"

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$work/logic.elaborated.json" \
  --inventory "$work/logic.inventory.json" \
  --module import_logic \
  --output "$work/logic.import.json"

lake exe importModule "$work/logic.import.json" "$work/logic.loom.v"

python3 scripts/rtl_equivalence.py \
  --module-label fixture_logic_import \
  --gold-top import_logic \
  --revised-top import_logic \
  --gold-file Tests/fixtures/import_logic.v \
  --revised-file "$work/logic.loom.v" \
  --assumption "clock and active-high synchronous reset ports correspond" \
  --log "$work/logic.equiv.log" \
  --output "$work/logic.equiv.json"

python3 scripts/verilog_inventory.py \
  --top import_stateless \
  --source-root "$PWD" \
  --source Tests/fixtures/import_stateless.v \
  --json-out "$work/stateless.inventory.json" \
  --markdown-out "$work/stateless.inventory.md" \
  --elaborated-out "$work/stateless.elaborated.json"

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$work/stateless.elaborated.json" \
  --inventory "$work/stateless.inventory.json" \
  --module import_stateless \
  --output "$work/stateless.import.json"

lake exe importModule "$work/stateless.import.json" "$work/stateless.loom.v"

if grep -Eq '\b(clk|rst|always)\b' "$work/stateless.loom.v"; then
  echo "import adapters: stateless artifact contains a synthetic sequential frame" >&2
  exit 1
fi

python3 scripts/rtl_equivalence.py \
  --module-label fixture_stateless_import \
  --gold-top import_stateless \
  --revised-top import_stateless \
  --gold-file Tests/fixtures/import_stateless.v \
  --revised-file "$work/stateless.loom.v" \
  --assumption "ordinary two-state combinational input correspondence" \
  --log "$work/stateless.equiv.log" \
  --output "$work/stateless.equiv.json"

python3 scripts/verilog_inventory.py \
  --top import_four_state \
  --source-root "$PWD" \
  --source Tests/fixtures/import_four_state.v \
  --json-out "$work/four-state.inventory.json" \
  --markdown-out "$work/four-state.inventory.md" \
  --elaborated-out "$work/four-state.elaborated.json"

python3 scripts/import_coverage.py \
  --yosys-json "$work/four-state.elaborated.json" \
  --inventory "$work/four-state.inventory.json" \
  --json-out "$work/four-state.coverage.json" \
  --markdown-out "$work/four-state.coverage.md"

python3 scripts/expand_four_state_policy.py \
  --coverage "$work/four-state.coverage.json" \
  --decisions Tests/fixtures/import_four_state_decisions.json \
  --output "$work/four-state-expanded-policy.json"

if python3 scripts/yosys_to_loom_ir.py \
    --yosys-json "$work/four-state.elaborated.json" \
    --inventory "$work/four-state.inventory.json" \
    --module import_four_state \
    --output "$work/four-state-unclassified.import.json"; then
  echo "import adapters: unclassified four-state value unexpectedly accepted" >&2
  exit 1
fi

if python3 scripts/yosys_to_loom_ir.py \
    --yosys-json "$work/four-state.elaborated.json" \
    --inventory "$work/four-state.inventory.json" \
    --module import_four_state \
    --four-state-policy Tests/fixtures/import_four_state_policy_ambiguous.json \
    --output "$work/four-state-ambiguous.import.json"; then
  echo "import adapters: ambiguous four-state policy unexpectedly accepted" >&2
  exit 1
fi

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$work/four-state.elaborated.json" \
  --inventory "$work/four-state.inventory.json" \
  --module import_four_state \
  --four-state-policy "$work/four-state-expanded-policy.json" \
  --output "$work/four-state.import.json"

lake exe importModule "$work/four-state.import.json" "$work/four-state.loom.v"

python3 scripts/rtl_equivalence.py \
  --module-label fixture_four_state_refinement \
  --gold-top import_four_state \
  --revised-top import_four_state \
  --gold-file Tests/fixtures/import_four_state.v \
  --revised-file "$work/four-state.loom.v" \
  --undef-policy zero \
  --assumption "the identified policy selects zero for source-unknown bits" \
  --log "$work/four-state.equiv.log" \
  --output "$work/four-state.equiv.json"

python3 - "$work/four-state.import.json" \
    "$work/four-state.import.json.manifest.json" \
    "$work/four-state.equiv.json" <<'PY'
import json
import sys

module = json.load(open(sys.argv[1], encoding="utf-8"))["module"]
manifest = json.load(open(sys.argv[2], encoding="utf-8"))
equivalence = json.load(open(sys.argv[3], encoding="utf-8"))
assert not module["unsupported"]
assert any(artifact["role"] == "four_state_policy"
           for artifact in manifest["artifacts"])
assert equivalence["status"] == "PASS"
assert equivalence["four_state_concretization"] == "zero"
PY

python3 scripts/verilog_inventory.py \
  --top import_shiftx \
  --source-root "$PWD" \
  --source Tests/fixtures/import_shiftx.v \
  --json-out "$work/shiftx.inventory.json" \
  --markdown-out "$work/shiftx.inventory.md" \
  --elaborated-out "$work/shiftx.elaborated.json"

if python3 scripts/yosys_to_loom_ir.py \
    --yosys-json "$work/shiftx.elaborated.json" \
    --inventory "$work/shiftx.inventory.json" \
    --module import_shiftx \
    --output "$work/shiftx-unclassified.import.json"; then
  echo "import adapters: unclassified variable part-select unexpectedly accepted" >&2
  exit 1
fi

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$work/shiftx.elaborated.json" \
  --inventory "$work/shiftx.inventory.json" \
  --module import_shiftx \
  --four-state-policy Tests/fixtures/import_shiftx_policy.json \
  --output "$work/shiftx.import.json"

lake exe importModule "$work/shiftx.import.json" "$work/shiftx.loom.v"

python3 scripts/rtl_equivalence.py \
  --module-label fixture_shiftx_refinement \
  --gold-top import_shiftx \
  --revised-top import_shiftx \
  --gold-file Tests/fixtures/import_shiftx.v \
  --revised-file "$work/shiftx.loom.v" \
  --undef-policy zero \
  --assumption "the identified policy selects zero for out-of-range part-select bits" \
  --log "$work/shiftx.equiv.log" \
  --output "$work/shiftx.equiv.json"

if python3 scripts/yosys_to_loom_ir.py \
    --yosys-json "$work/shiftx.elaborated.json" \
    --inventory "$work/shiftx.inventory.json" \
    --module import_shiftx \
    --four-state-policy Tests/fixtures/import_shiftx_policy_one.json \
    --output "$work/shiftx-one.import.json"; then
  echo "import adapters: unvalidated one-fill variable part-select unexpectedly accepted" >&2
  exit 1
fi

python3 scripts/verilog_inventory.py \
  --top import_hierarchy \
  --source-root "$PWD" \
  --source Tests/fixtures/import_hierarchy.v \
  --json-out "$work/hierarchy.inventory.json" \
  --markdown-out "$work/hierarchy.inventory.md" \
  --elaborated-out "$work/hierarchy.elaborated.json"

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$work/hierarchy.elaborated.json" \
  --inventory "$work/hierarchy.inventory.json" \
  --module import_hierarchy \
  --output "$work/hierarchy.import.json"

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$work/hierarchy.elaborated.json" \
  --inventory "$work/hierarchy.inventory.json" \
  --package-top import_hierarchy \
  --output "$work/hierarchy.package.import.json"

lake exe checkImportPackage "$work/hierarchy.package.import.json"

lake exe importPackage \
  "$work/hierarchy.package.import.json" "$work/hierarchy.package.loom.v"

python3 scripts/rtl_equivalence.py \
  --module-label fixture_hierarchy_import \
  --gold-top import_hierarchy \
  --revised-top import_hierarchy \
  --gold-file Tests/fixtures/import_hierarchy.v \
  --revised-file "$work/hierarchy.package.loom.v" \
  --assumption "ordinary two-state combinational input correspondence" \
  --log "$work/hierarchy.equiv.log" \
  --output "$work/hierarchy.equiv.json"

python3 - "$work/hierarchy.import.json" <<'PY'
import json
import sys

module = json.load(open(sys.argv[1], encoding="utf-8"))["module"]
assert not module["unsupported"]
assert len(module["instances"]) == 1
connections = {item["port"]: item for item in module["instances"][0]["connections"]}
assert connections["a"]["direction"] == "input"
assert connections["a"]["value"] is not None
assert connections["q"]["direction"] == "output"
assert connections["q"]["value"] is None
assert connections["a"]["signal"] != connections["q"]["signal"]
assert connections["q"]["signal"].startswith("__loom_child__h")
PY

if lake exe importModule "$work/hierarchy.import.json" "$work/hierarchy.loom.v"; then
  echo "import adapters: hierarchical module bypassed checked package lowering" >&2
  exit 1
fi

python3 scripts/verilog_inventory.py \
  --top import_hierarchy_seq \
  --source-root "$PWD" \
  --source Tests/fixtures/import_hierarchy_seq.v \
  --json-out "$work/hierarchy-seq.inventory.json" \
  --markdown-out "$work/hierarchy-seq.inventory.md" \
  --elaborated-out "$work/hierarchy-seq.elaborated.json"

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$work/hierarchy-seq.elaborated.json" \
  --inventory "$work/hierarchy-seq.inventory.json" \
  --package-top import_hierarchy_seq \
  --output "$work/hierarchy-seq.package.import.json"

lake exe importPackage \
  "$work/hierarchy-seq.package.import.json" "$work/hierarchy-seq.package.loom.v"

python3 scripts/rtl_equivalence.py \
  --module-label fixture_hierarchy_seq_import \
  --gold-top import_hierarchy_seq \
  --revised-top import_hierarchy_seq \
  --gold-file Tests/fixtures/import_hierarchy_seq.v \
  --revised-file "$work/hierarchy-seq.package.loom.v" \
  --assumption "clock and active-high synchronous reset ports correspond" \
  --log "$work/hierarchy-seq.equiv.log" \
  --output "$work/hierarchy-seq.equiv.json"

python3 scripts/verilog_inventory.py \
  --top import_mixed_edge \
  --source-root "$PWD" \
  --source Tests/fixtures/import_mixed_edge.v \
  --json-out "$work/mixed-edge.inventory.json" \
  --markdown-out "$work/mixed-edge.inventory.md" \
  --elaborated-out "$work/mixed-edge.elaborated.json"

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$work/mixed-edge.elaborated.json" \
  --inventory "$work/mixed-edge.inventory.json" \
  --package-top import_mixed_edge \
  --output "$work/mixed-edge.package.import.json"

lake exe importPackage \
  "$work/mixed-edge.package.import.json" "$work/mixed-edge.package.loom.v"

python3 scripts/rtl_equivalence.py \
  --module-label fixture_mixed_edge_import \
  --gold-top import_mixed_edge \
  --revised-top import_mixed_edge \
  --gold-file Tests/fixtures/import_mixed_edge.v \
  --revised-file "$work/mixed-edge.package.loom.v" \
  --assumption "the same physical clock drives distinct rising- and falling-edge state bodies" \
  --log "$work/mixed-edge.equiv.log" \
  --output "$work/mixed-edge.equiv.json"

python3 - "$work/mixed-edge.package.import.json" \
    "$work/mixed-edge.package.loom.v" <<'PY'
import json
import sys

module = json.load(open(sys.argv[1], encoding="utf-8"))["package"]["modules"][0]
text = open(sys.argv[2], encoding="utf-8").read()
assert not module["unsupported"]
assert len(module["domains"]) == 2
assert {domain["edge"] for domain in module["domains"]} == {"rising", "falling"}
assert "always @(posedge clk)" in text and "always @(negedge clk)" in text
PY

python3 scripts/verilog_inventory.py \
  --top import_resetless \
  --source-root "$PWD" \
  --source Tests/fixtures/import_resetless.v \
  --json-out "$work/resetless.inventory.json" \
  --markdown-out "$work/resetless.inventory.md" \
  --elaborated-out "$work/resetless.elaborated.json"

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$work/resetless.elaborated.json" \
  --inventory "$work/resetless.inventory.json" \
  --module import_resetless \
  --output "$work/resetless.import.json"

lake exe importModule "$work/resetless.import.json" "$work/resetless.loom.v"

python3 scripts/rtl_equivalence.py \
  --module-label fixture_resetless_import \
  --gold-top import_resetless \
  --revised-top import_resetless \
  --gold-file Tests/fixtures/import_resetless.v \
  --revised-file "$work/resetless.loom.v" \
  --assumption "clock correspondence with unconstrained initial register state" \
  --log "$work/resetless.equiv.log" \
  --output "$work/resetless.equiv.json"

python3 - "$work/resetless.import.json" "$work/resetless.loom.v" <<'PY'
import json
import sys

report = json.load(open(sys.argv[1], encoding="utf-8"))
text = open(sys.argv[2], encoding="utf-8").read()
assert not report["module"]["unsupported"]
assert "always @(posedge clk)" in text
assert "input wire rst" not in text
assert "if (rst)" not in text
PY

python3 scripts/verilog_inventory.py \
  --top import_multi_reset \
  --source-root "$PWD" \
  --source Tests/fixtures/import_multi_reset.v \
  --json-out "$work/multi-reset.inventory.json" \
  --markdown-out "$work/multi-reset.inventory.md" \
  --elaborated-out "$work/multi-reset.elaborated.json"

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$work/multi-reset.elaborated.json" \
  --inventory "$work/multi-reset.inventory.json" \
  --module import_multi_reset \
  --output "$work/multi-reset.import.json"

lake exe importModule "$work/multi-reset.import.json" "$work/multi-reset.loom.v"

python3 scripts/rtl_equivalence.py \
  --module-label fixture_multi_reset_import \
  --gold-top import_multi_reset \
  --revised-top import_multi_reset \
  --gold-file Tests/fixtures/import_multi_reset.v \
  --revised-file "$work/multi-reset.loom.v" \
  --assumption "clock and per-register synchronous reset inputs correspond" \
  --log "$work/multi-reset.equiv.log" \
  --output "$work/multi-reset.equiv.json"

python3 - "$work/multi-reset.elaborated.json" "$work/multi-reset.loom.v" <<'PY'
import json
import sys

elaborated = json.load(open(sys.argv[1], encoding="utf-8"))
text = open(sys.argv[2], encoding="utf-8").read()
kinds = {cell["type"] for cell in elaborated["modules"]["import_multi_reset"]["cells"].values()}
assert "$sdff" in kinds
assert "$sdffce" in kinds
assert "input wire [0:0] rst_a" in text and "input wire [0:0] rst_bn" in text
assert "if (rst_a)" not in text and "if (rst_bn)" not in text
PY

python3 scripts/verilog_inventory.py \
  --top import_memory \
  --source-root "$PWD" \
  --source Tests/fixtures/import_memory.v \
  --json-out "$work/memory.inventory.json" \
  --markdown-out "$work/memory.inventory.md" \
  --elaborated-out "$work/memory.elaborated.json"

python3 scripts/import_coverage.py \
  --yosys-json "$work/memory.elaborated.json" \
  --inventory "$work/memory.inventory.json" \
  --json-out "$work/memory.coverage.json" \
  --markdown-out "$work/memory.coverage.md"

python3 scripts/expand_four_state_policy.py \
  --coverage "$work/memory.coverage.json" \
  --decisions Tests/fixtures/import_memory_decisions.json \
  --output "$work/memory.policy.json"

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$work/memory.elaborated.json" \
  --inventory "$work/memory.inventory.json" \
  --module import_memory \
  --four-state-policy "$work/memory.policy.json" \
  --output "$work/memory.import.json"

lake exe importModule "$work/memory.import.json" "$work/memory.loom.v"

python3 scripts/rtl_equivalence.py \
  --module-label fixture_memory_import \
  --gold-top import_memory \
  --revised-top import_memory \
  --gold-file Tests/fixtures/import_memory.v \
  --revised-file "$work/memory.loom.v" \
  --memory-map "$work/memory.import.json" \
  --undef-policy zero \
  --assumption "rising clock, exact initial image, async reads, masks, and ordered writes correspond" \
  --log "$work/memory.equiv.log" \
  --output "$work/memory.equiv.json"

python3 - "$work/memory.import.json" "$work/memory.loom.v" <<'PY'
import json
import sys

module = json.load(open(sys.argv[1], encoding="utf-8"))["module"]
text = open(sys.argv[2], encoding="utf-8").read()
assert not module["unsupported"]
assert len(module["memories"]) == 1
assert module["memories"][0]["data_width"] == 8
assert len(module["memories"][0]["writes"]) == 3
assert all(memory["init_refinement"] is not None for memory in module["memories"])
assert "initial begin" in text and "always @(posedge clk)" in text
PY

python3 - "$work/inventory.json" <<'PY'
import json
import sys

report = json.load(open(sys.argv[1], encoding="utf-8"))
assert report["frontend"]["status"] == "PASS"
assert report["summary"]["module_count"] == 1
assert report["summary"]["rising_edge_modules"] == 1
PY

python3 - "$work/fixture.import.json.manifest.json" <<'PY'
import json
import sys

manifest = json.load(open(sys.argv[1], encoding="utf-8"))
roles = [artifact["role"] for artifact in manifest["artifacts"]]
assert "source" in roles
assert roles[-3:] == ["inventory", "elaborated_yosys_json", "neutral_import_ir"]
assert all(len(artifact["sha256"]) == 64 for artifact in manifest["artifacts"])
assert manifest["invocation"]
assert manifest["assumptions"]
PY

python3 scripts/rtl_equivalence.py \
  --module-label fixture \
  --gold-top fixture_gold \
  --revised-top fixture_revised \
  --gold-file Tests/fixtures/equiv_gold.v \
  --revised-file Tests/fixtures/equiv_revised.v \
  --assumption "clock and reset ports correspond" \
  --log "$work/pass.log" \
  --output "$work/pass.json"

if python3 scripts/rtl_equivalence.py \
    --module-label fixture_bad \
    --gold-top fixture_gold \
    --revised-top fixture_bad \
    --gold-file Tests/fixtures/equiv_gold.v \
    --revised-file Tests/fixtures/equiv_bad.v \
    --assumption "clock and reset ports correspond" \
    --log "$work/fail.log" \
    --output "$work/fail.json"; then
  echo "import adapters: inequivalent fixture unexpectedly passed" >&2
  exit 1
fi

python3 - "$work/pass.json" "$work/fail.json" "$work/import-pass.json" \
    "$work/active-low.equiv.json" "$work/logic.equiv.json" \
    "$work/stateless.equiv.json" <<'PY'
import json
import sys

passed = json.load(open(sys.argv[1], encoding="utf-8"))
failed = json.load(open(sys.argv[2], encoding="utf-8"))
imported = json.load(open(sys.argv[3], encoding="utf-8"))
active_low = json.load(open(sys.argv[4], encoding="utf-8"))
logic = json.load(open(sys.argv[5], encoding="utf-8"))
stateless = json.load(open(sys.argv[6], encoding="utf-8"))
assert passed["status"] == "PASS"
assert failed["status"] == "FAIL"
assert imported["status"] == "PASS"
assert active_low["status"] == "PASS"
assert logic["status"] == "PASS"
assert stateless["status"] == "PASS"
assert all(len(item["sha256"]) == 64 for item in passed["artifacts"])
assert passed["run"]["version"]
assert passed["run"]["invocation"]
PY

echo "import adapters: PASS"
