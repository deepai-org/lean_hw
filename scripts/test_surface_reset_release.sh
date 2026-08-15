#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
work_dir=$(mktemp -d /tmp/loom-surface-reset-release.XXXXXX)
trap 'rm -rf "$work_dir"' EXIT
iverilog -g2012 -Wall -s surface_reset_release_tb \
  -o "$work_dir/reset-release.vvp" \
  "$repo_root/fpga/zc702/surface_matrix/surface_reset_release.v" \
  "$repo_root/Tests/rtl/SurfaceResetReleaseTb.v"
vvp "$work_dir/reset-release.vvp" | tee "$work_dir/simulation.log"
grep -q '^SURFACE_RESET_RELEASE_RTL_PASS ' "$work_dir/simulation.log"
