#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
if (($# != 1)); then
  echo "usage: $0 OUTPUT_DIRECTORY" >&2
  exit 2
fi
output_dir=$(realpath -m "$1")
mkdir -p "$output_dir"

run_expected_vivado_failure() {
  local control=$1 marker=$2
  local log="$output_dir/$control.log"
  if "$repo_root/scripts/build_surface_matrix_vivado.sh" \
      "$output_dir/$control" 1 "$control" >"$log" 2>&1; then
    echo "$control unexpectedly succeeded" >&2
    exit 1
  fi
  if ! grep -q "$marker" "$log"; then
    echo "$control failed for the wrong reason; expected marker: $marker" >&2
    exit 1
  fi
  echo "SURFACE_MATRIX_PHYSICAL_NEGATIVE_PASS control=$control"
}

run_expected_vivado_failure omit-gray "Gray constraint deliberately omitted"
run_expected_vivado_failure unresolved-object "resolved to 0 cells"
run_expected_vivado_failure forbidden-fanout "forbidden fanout"
"$repo_root/scripts/build_surface_matrix_vivado.sh" \
  "$output_dir/alter-route-input-hash" 1 alter-route-input-hash \
  | tee "$output_dir/alter-route-input-hash.log"
grep -q 'SURFACE_MATRIX_PHYSICAL_NEGATIVE_PASS control=alter-route-input-hash' \
  "$output_dir/alter-route-input-hash.log"
echo "SURFACE_MATRIX_PHYSICAL_NEGATIVES_PASS controls=4"
