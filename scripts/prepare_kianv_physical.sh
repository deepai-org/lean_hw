#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail

cd "$(dirname "$0")/.."

kianv_root=${1:-../kianv/gf180mcu-kianv-rv32ima-sv32}
output_dir=${2:-build/kianv-physical}
conversion_dir="$output_dir/conversion"
rtl="$output_dir/chip_core.loom.v"
config="$output_dir/config.loom.yaml"
manifest="$output_dir/physical-handoff.json"
pdn="$output_dir/pdn_cfg.loom.tcl"

scripts/convert_kianv.sh "$kianv_root" "$conversion_dir"
python3 scripts/kianv_physical_handoff.py \
  --emitted "$conversion_dir/chip_core.loom.v" \
  --package "$conversion_dir/chip_core.package.import.json" \
  --kianv-root "$kianv_root" \
  --output-rtl "$rtl" \
  --output-config "$config" \
  --output-pdn "$pdn" \
  --manifest "$manifest"
python3 scripts/verify_kianv_physical_handoff.py \
  --rtl "$rtl" --config "$config" --manifest "$manifest" \
  --kianv-root "$kianv_root"

echo "KIANV_PHYSICAL_PREPARE_PASS output=$output_dir"
