#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail

cd "$(dirname "$0")/.."

kianv_root=${1:-../kianv/gf180mcu-kianv-rv32ima-sv32}
output_dir=${2:-Evidence/KianV}

if [[ ! -d "$kianv_root/src" ]]; then
  echo "KianV source directory not found: $kianv_root/src" >&2
  exit 2
fi

mkdir -p "$output_dir"

mapfile -t sources < <(
  find "$kianv_root/src" -type f \( -name '*.v' -o -name '*.sv' \) \
    ! -name 'chip_top.sv' -printf '%P\n' | sort
)

arguments=()
for source in "${sources[@]}"; do
  arguments+=(--source "src/$source")
done

python3 scripts/verilog_inventory.py \
  --top chip_core \
  --source-root "$kianv_root" \
  "${arguments[@]}" \
  --include src \
  --include src/kianv_harris_edition \
  --define SYSTEM_CLK=20000000 \
  --define TRP_NS=15 \
  --define TRCD_NS=15 \
  --define TRFC_NS=66 \
  --define TWR_NS=15 \
  --define CAS=2 \
  --define TREFI_NS=7800 \
  --define SDRAM_SIZE=33554432 \
  --define NUM_ENTRIES_ITLB=32 \
  --define NUM_ENTRIES_DTLB=32 \
  --define "BYPASS_CACHES=1'b0" \
  --json-out "$output_dir/construct_inventory.json" \
  --markdown-out "$output_dir/construct_inventory.md" \
  --elaborated-out "$output_dir/elaborated.json"
