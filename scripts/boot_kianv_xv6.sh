#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail

cd "$(dirname "$0")/.."

kianv_root=${1:-../kianv/gf180mcu-kianv-rv32ima-sv32}
output_dir=${2:-build/kianv-xv6-loom}
chip_dir="$output_dir/chip"
soc_dir="$output_dir/soc"
obj_dir=${KIANV_XV6_OBJDIR:-build/loom-obj}
max_cycles=${MAX_CYCLES:-300000000}

if [[ ! -f "$kianv_root/sim/xv6/Makefile" ]]; then
  echo "KianV xv6 harness not found: $kianv_root/sim/xv6" >&2
  exit 2
fi

# The xv6 fast-boot harness uses KianV's SIM divider defaults. SYNTHESIS only
# removes a simulation watchdog containing a system task unsupported by Yosys;
# it does not select the taped-out configuration.
scripts/convert_kianv.sh "$kianv_root" "$chip_dir" SIM SYNTHESIS

mkdir -p "$soc_dir"
python3 scripts/yosys_to_loom_ir.py \
  --yosys-json "$chip_dir/evidence/elaborated.json" \
  --inventory "$chip_dir/evidence/construct_inventory.json" \
  --package-top soc \
  --four-state-policy "$chip_dir/evidence/four_state_policy.json" \
  --output "$soc_dir/soc.package.import.json"

.lake/build/bin/checkImportPackage "$soc_dir/soc.package.import.json"
.lake/build/bin/importPackage "$soc_dir/soc.package.import.json" \
  "$soc_dir/soc.loom.v"

# Neutral emission is intentionally simple and traceable. Collapsing its
# redundant width-extension wires before Verilator reduces compilation from
# minutes to seconds and substantially improves simulation throughput.
yosys -Q -p "read_verilog $soc_dir/soc.loom.v; hierarchy -check -top soc; \
  proc; opt -full; clean -purge; \
  write_verilog -noattr $soc_dir/soc.loom.opt.v" \
  > "$soc_dir/yosys-opt.log" 2>&1

sha256sum "$soc_dir/soc.package.import.json" \
  "$soc_dir/soc.package.import.json.manifest.json" \
  "$soc_dir/soc.loom.v" "$soc_dir/soc.loom.opt.v" \
  > "$soc_dir/SHA256SUMS"

loom_rtl=$(realpath "$soc_dir/soc.loom.opt.v")
make -C "$kianv_root/sim/xv6" verify \
  OBJDIR="$obj_dir" RTL="$loom_rtl" \
  EXTRA_CFLAGS=-DLOOM_IMPORTED_RTL MAX_CYCLES="$max_cycles"

echo "KIANV_LOOM_XV6_PASS rtl=$loom_rtl hashes=$soc_dir/SHA256SUMS"
