#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
if (($# < 1 || $# > 3)); then
  echo "usage: $0 OUTPUT_DIRECTORY [SEED] [none|omit-gray|unresolved-object|forbidden-fanout|alter-route-input-hash]" >&2
  exit 2
fi
output_dir=$(realpath -m "$1")
route_seed=${2:-1}
negative_control=${3:-none}
case "$route_seed" in
  ''|*[!0-9]*) echo "SEED must be a natural number" >&2; exit 2 ;;
esac
if ((route_seed < 1)); then
  echo "SEED must be positive" >&2
  exit 2
fi
case "$negative_control" in
  none|omit-gray|unresolved-object|forbidden-fanout|alter-route-input-hash) ;;
  *) echo "unknown negative control: $negative_control" >&2; exit 2 ;;
esac

vivado_bin=${LOOM_VIVADO_BIN:-vivado}
if ! command -v "$vivado_bin" >/dev/null 2>&1; then
  echo "Vivado is required (set LOOM_VIVADO_BIN if it is not on PATH)" >&2
  exit 1
fi
mkdir -p "$output_dir"
evidence_dir="$output_dir/canonical"
route_dir="$output_dir/route-seed-$route_seed-$negative_control"
LOOM_ROOT="$repo_root" lake -d "$repo_root" exe surfaceMatrixEvidence "$evidence_dir"
mkdir -p "$route_dir"

input_manifest="$route_dir/route-inputs.sha256"
sha256sum \
  "$evidence_dir/system.v" \
  "$evidence_dir/clock_constraints.md" \
  "$repo_root/fpga/zc702/surface_matrix/surface_matrix_top.v" \
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
LOOM_PHYSICAL_NEGATIVE="$negative_control" \
LOOM_SURFACE_VARIANT=matrix \
LOOM_RTL_SHA256="$rtl_sha256" \
LOOM_ROUTE_INPUTS_SHA256="$route_inputs_sha256" \
  "$vivado_bin" -mode batch -nojournal -nolog \
    -source "$repo_root/fpga/zc702/surface_matrix/build_vivado.tcl" \
    | tee "$route_dir/vivado.log"

if [[ "$negative_control" != none && "$negative_control" != alter-route-input-hash ]]; then
  echo "negative control unexpectedly reached PASS: $negative_control" >&2
  exit 1
fi
sha256sum "$route_dir/routed.dcp" "$route_dir/surface_matrix.bit" \
  >"$route_dir/output-artifacts.sha256"
run_id=${LOOM_RUN_ID:-surface-matrix-seed-$route_seed}
if [[ "$negative_control" == alter-route-input-hash ]]; then
  if lake -d "$repo_root" exe surfaceMatrixVivadoSignoff \
      "$evidence_dir" "$route_dir" "$run_id" "$route_seed"; then
    echo "altered route-input hash unexpectedly passed signoff" >&2
    exit 1
  fi
  echo "SURFACE_MATRIX_PHYSICAL_NEGATIVE_PASS control=$negative_control"
  exit 0
fi
lake -d "$repo_root" exe surfaceMatrixVivadoSignoff \
  "$evidence_dir" "$route_dir" "$run_id" "$route_seed"
echo "SURFACE_MATRIX_VIVADO_ARTIFACT_PASS seed=$route_seed directory=$route_dir"
