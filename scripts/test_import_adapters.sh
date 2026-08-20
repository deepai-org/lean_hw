#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "$0")/.."

python3 -m py_compile scripts/verilog_inventory.py scripts/yosys_to_loom_ir.py \
  scripts/import_coverage.py \
  scripts/rtl_equivalence.py

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
  --top import_resetless \
  --source-root "$PWD" \
  --source Tests/fixtures/import_resetless.v \
  --json-out "$work/resetless.inventory.json" \
  --markdown-out "$work/resetless.inventory.md" \
  --elaborated-out "$work/resetless.elaborated.json"

if python3 scripts/yosys_to_loom_ir.py \
    --yosys-json "$work/resetless.elaborated.json" \
    --inventory "$work/resetless.inventory.json" \
    --module import_resetless \
    --output "$work/resetless.import.json"; then
  echo "import adapters: resetless state unexpectedly accepted" >&2
  exit 1
fi

python3 - "$work/resetless.import.json" <<'PY'
import json
import sys

report = json.load(open(sys.argv[1], encoding="utf-8"))
kinds = [item["kind"] for item in report["module"]["unsupported"]]
assert "resetless_state" in kinds
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
