#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
work_dir=$(mktemp -d /tmp/loom-surface-registered-bram.XXXXXX)
trap 'rm -rf "$work_dir"' EXIT

lake -d "$repo_root" exe surfaceRegisteredBramEvidence "$work_dir/evidence"
(
  cd "$work_dir/evidence"
  sha256sum -c SHA256SUMS
)
grep -q 'XILINX7_BLOCK_RAM width=32 depth=4' "$work_dir/evidence/system.v"
grep -q 'ram_style = "block"' "$work_dir/evidence/system.v"
iverilog -g2012 -Wall -s surface_registered_bram_tb \
  -o "$work_dir/registered-bram.vvp" \
  "$work_dir/evidence/system.v" "$repo_root/Tests/rtl/SurfaceRegisteredBramTb.v"
vvp "$work_dir/registered-bram.vvp" | tee "$work_dir/simulation.log"
grep -q '^SURFACE_REGISTERED_BRAM_RTL_PASS ' "$work_dir/simulation.log"
