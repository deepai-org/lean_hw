#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
work_dir=$(mktemp -d /tmp/loom-surface-matrix-test.XXXXXX)
trap 'rm -rf "$work_dir"' EXIT

LOOM_ROOT="$repo_root" lake -d "$repo_root" exe surfaceMatrixEvidence "$work_dir/evidence"
(
  cd "$work_dir/evidence"
  sha256sum -c SHA256SUMS
)
python3 -m json.tool "$work_dir/evidence/matrix-manifest.json" >/dev/null
iverilog -g2012 -Wall -s surface_matrix_tb \
  -o "$work_dir/surface-matrix.vvp" \
  "$work_dir/evidence/system.v" "$repo_root/Tests/rtl/SurfaceMatrixTb.v"
vvp "$work_dir/surface-matrix.vvp" | tee "$work_dir/simulation.log"
grep -q '^SURFACE_MATRIX_RTL_PASS ' "$work_dir/simulation.log"
