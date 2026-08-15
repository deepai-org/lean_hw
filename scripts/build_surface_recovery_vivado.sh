#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
if (($# < 1 || $# > 2)); then
  echo "usage: $0 OUTPUT_DIRECTORY [SEED]" >&2
  exit 2
fi
output_dir=$(realpath -m "$1")
route_seed=${2:-1}
case "$route_seed" in ''|*[!0-9]*) echo "SEED must be a positive natural number" >&2; exit 2 ;; esac
if ((route_seed < 1)); then echo "SEED must be positive" >&2; exit 2; fi
vivado_bin=${LOOM_VIVADO_BIN:-vivado}
command -v "$vivado_bin" >/dev/null || {
  echo "Vivado is required (set LOOM_VIVADO_BIN if it is not on PATH)" >&2
  exit 1
}

mkdir -p "$output_dir"
evidence_dir="$output_dir/canonical"
route_dir="$output_dir/route-seed-$route_seed"
lake -d "$repo_root" exe surfaceMatrixRecoveryEvidence "$evidence_dir"
mkdir -p "$route_dir"
input_manifest="$route_dir/route-inputs.sha256"
sha256sum \
  "$evidence_dir/system.v" \
  "$evidence_dir/clock_constraints.md" \
  "$repo_root/fpga/zc702/surface_matrix/surface_recovery_top.v" \
  "$repo_root/fpga/zc702/surface_matrix/surface_matrix_bscan.v" \
  "$repo_root/fpga/zc702/surface_matrix/surface_reset_release.v" \
  "$repo_root/fpga/zc702/surface_matrix/surface_matrix.xdc" \
  "$repo_root/fpga/zc702/surface_matrix/surface_matrix_cdc.tcl" \
  "$repo_root/fpga/zc702/surface_matrix/build_vivado.tcl" >"$input_manifest"
rtl_sha256=$(sha256sum "$evidence_dir/system.v" | awk '{print $1}')
route_inputs_sha256=$(sha256sum "$input_manifest" | awk '{print $1}')

LOOM_ROOT="$repo_root" \
LOOM_EVIDENCE_DIR="$evidence_dir" \
LOOM_VIVADO_OUT="$route_dir" \
LOOM_ROUTE_SEED="$route_seed" \
LOOM_PHYSICAL_NEGATIVE=none \
LOOM_SURFACE_VARIANT=recovery \
LOOM_RTL_SHA256="$rtl_sha256" \
LOOM_ROUTE_INPUTS_SHA256="$route_inputs_sha256" \
  "$vivado_bin" -mode batch -nojournal -nolog \
    -source "$repo_root/fpga/zc702/surface_matrix/build_vivado.tcl" \
    | tee "$route_dir/vivado.log"

sha256sum "$route_dir/routed.dcp" "$route_dir/surface_recovery.bit" \
  >"$route_dir/output-artifacts.sha256"
run_id=${LOOM_RUN_ID:-surface-recovery-seed-$route_seed}
lake -d "$repo_root" exe surfaceMatrixVivadoSignoff recovery \
  "$evidence_dir" "$route_dir" "$run_id" "$route_seed"
echo "SURFACE_RECOVERY_VIVADO_PASS seed=$route_seed directory=$route_dir"
