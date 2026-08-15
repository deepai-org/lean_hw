#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
work_dir=$(mktemp -d /tmp/loom-surface-bscan.XXXXXX)
trap 'rm -rf "$work_dir"' EXIT
iverilog -g2012 -Wall -DSURFACE_MATRIX_RTL_SHA_PREFIX=32\'h89abcdef \
  -s surface_matrix_bscan_tb \
  -o "$work_dir/bscan.vvp" \
  "$repo_root/fpga/zc702/surface_matrix/surface_matrix_bscan.v" \
  "$repo_root/Tests/rtl/SurfaceMatrixBscanTb.v"
vvp "$work_dir/bscan.vvp" | tee "$work_dir/simulation.log"
grep -q '^SURFACE_MATRIX_BSCAN_RTL_PASS ' "$work_dir/simulation.log"
