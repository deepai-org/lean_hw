#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail

cd "$(dirname "$0")/.."

kianv_root=${1:-../kianv/gf180mcu-kianv-rv32ima-sv32}
output_dir=${2:-build/kianv-total-conversion}
conversion_dir="$output_dir/conversion"
equivalence_dir="$output_dir/equivalence"
logarithm_module="\$paramod\\Logarithm_of_Powers_of_Two\\WORD_WIDTH=s32'00000000000000000000000000100000"

scripts/convert_kianv.sh "$kianv_root" "$conversion_dir"

python3 scripts/kianv_bottom_up_equivalence.py \
  --elaborated "$conversion_dir/evidence/elaborated.json" \
  --package "$conversion_dir/chip_core.package.import.json" \
  --emitted "$conversion_dir/chip_core.loom.v" \
  --external-contract Evidence/KianV/gf180_sram_external.json \
  --flatten-module "$logarithm_module" \
  --output-dir "$equivalence_dir"

python3 scripts/kianv_equivalence_evidence.py \
  --report "$equivalence_dir/report.json" \
  --json-out "$output_dir/equivalence.json" \
  --markdown-out "$output_dir/equivalence.md"

echo "KIANV_TOTAL_CONVERSION_PASS evidence=$output_dir/equivalence.json"
