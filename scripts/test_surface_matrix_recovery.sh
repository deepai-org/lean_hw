#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
work_dir=$(mktemp -d /tmp/loom-surface-matrix-recovery.XXXXXX)
trap 'rm -rf "$work_dir"' EXIT

(
  cd "$repo_root"
  lake exe surfaceMatrixRecoveryEvidence "$work_dir/evidence"
)
(
  cd "$work_dir/evidence"
  sha256sum -c system.v.sha256
)
[[ $(grep -c 'Preserve and identify the ordered synchronizer chain' \
  "$work_dir/evidence/clock_constraints.md") == 8 ]]
[[ $(grep -c '^system_recovery_completion_synchronizer u_recovery_sync_' \
  "$work_dir/evidence/system.v") == 2 ]]
grep -q '\.raw_completion(__loom_recovery_surface_full_rate_d8_dst_done)' \
  "$work_dir/evidence/system.v"
grep -q '\.raw_completion(__loom_recovery_surface_full_rate_d8_src_done)' \
  "$work_dir/evidence/system.v"
if grep -q 'u_recovery_source_full_rate_d8_1 .*\.right(__loom_recovery_surface_full_rate_d8_dst_done)' \
    "$work_dir/evidence/system.v"; then
  echo "raw remote completion still feeds the source recovery fold" >&2
  exit 1
fi
if grep -q 'u_recovery_sink_full_rate_d8_0 .*\.right(__loom_recovery_surface_full_rate_d8_src_done)' \
    "$work_dir/evidence/system.v"; then
  echo "raw remote completion still feeds the sink recovery fold" >&2
  exit 1
fi
iverilog -g2012 -Wall -s surface_matrix_recovery_tb \
  -o "$work_dir/recovery.vvp" \
  "$work_dir/evidence/system.v" "$repo_root/Tests/rtl/SurfaceMatrixRecoveryTb.v"
vvp "$work_dir/recovery.vvp" | tee "$work_dir/recovery.log"
grep -q '^SURFACE_MATRIX_RECOVERY_RTL_PASS ' "$work_dir/recovery.log"
