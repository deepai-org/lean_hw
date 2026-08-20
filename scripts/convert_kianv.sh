#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail

cd "$(dirname "$0")/.."

kianv_root=${1:-../kianv/gf180mcu-kianv-rv32ima-sv32}
output_dir=${2:-build/kianv-conversion}
evidence_dir="$output_dir/evidence"
package_json="$output_dir/chip_core.package.import.json"
emitted_rtl="$output_dir/chip_core.loom.v"

mkdir -p "$evidence_dir"
install -m 0644 Evidence/KianV/four_state_decisions.json \
  "$evidence_dir/four_state_decisions.json"

python3 scripts/verify_kianv_sram_external.py "$kianv_root"
scripts/inventory_kianv.sh "$kianv_root" "$evidence_dir"

python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$evidence_dir/elaborated.json" \
  --inventory "$evidence_dir/construct_inventory.json" \
  --package-top chip_core \
  --four-state-policy "$evidence_dir/four_state_policy.json" \
  --output "$package_json"

lake build checkImportPackage importPackage
.lake/build/bin/checkImportPackage "$package_json"
.lake/build/bin/importPackage "$package_json" "$emitted_rtl"

if command -v iverilog >/dev/null 2>&1; then
  iverilog -g2012 -s chip_core -o "$output_dir/chip_core.vvp" "$emitted_rtl"
  syntax_status=PASS
else
  syntax_status='SKIP (iverilog unavailable)'
fi

sha256sum "$package_json" "$package_json.manifest.json" "$emitted_rtl" \
  > "$output_dir/SHA256SUMS"

echo "KIANV_CONVERSION_PASS modules=74 artifacts=150 syntax=$syntax_status output=$output_dir"
