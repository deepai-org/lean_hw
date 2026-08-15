#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
if (($# < 2 || $# > 3)); then
  echo "usage: $0 ROUTE_DIRECTORY OUTPUT_DIRECTORY [short|soak]" >&2
  exit 2
fi
route_dir=$(realpath "$1")
output_dir=$(realpath -m "$2")
mode=${3:-short}
case "$mode" in short|soak) ;; *) echo "mode must be short or soak" >&2; exit 2 ;; esac

bitstream="$route_dir/surface_matrix.bit"
status="$route_dir/route-status.tsv"
signoff="$route_dir/vivado-signoff.md"
for artifact in "$bitstream" "$status" "$signoff" "$route_dir/routed.dcp"; do
  test -s "$artifact" || { echo "missing routed artifact: $artifact" >&2; exit 1; }
done
grep -q $'^status\tPASS$' "$status" || { echo "route status is not PASS" >&2; exit 1; }
if grep -Eq '^- (FAIL|SKIP|UNCONSTRAINED):' "$signoff"; then
  echo "physical signoff contains a non-PASS requirement" >&2
  exit 1
fi
rtl_sha256=$(awk -F '\t' '$1 == "rtl_sha256" {print $2}' "$status")
route_inputs_sha256=$(awk -F '\t' '$1 == "route_inputs_sha256" {print $2}' "$status")
test ${#rtl_sha256} -eq 64 || { echo "invalid RTL hash in route status" >&2; exit 1; }
test ${#route_inputs_sha256} -eq 64 || { echo "invalid route-input hash in route status" >&2; exit 1; }
actual_route_inputs_sha256=$(sha256sum "$route_dir/route-inputs.sha256" | awk '{print $1}')
[[ "$actual_route_inputs_sha256" == "$route_inputs_sha256" ]] || {
  echo "route-input manifest changed after signoff" >&2
  exit 1
}
signed_routed_sha256=$(awk '$1 == "-" && $2 == "routed-design" && $3 == "SHA-256:" {print $4}' "$signoff")
signed_bitstream_sha256=$(awk '$1 == "-" && $2 == "bitstream" && $3 == "SHA-256:" {print $4}' "$signoff")
[[ "$signed_routed_sha256" == "$(sha256sum "$route_dir/routed.dcp" | awk '{print $1}')" ]] || {
  echo "routed design changed after signoff" >&2
  exit 1
}
[[ "$signed_bitstream_sha256" == "$(sha256sum "$bitstream" | awk '{print $1}')" ]] || {
  echo "bitstream changed after signoff" >&2
  exit 1
}
command -v xsdb >/dev/null || { echo "xsdb is required on the board host" >&2; exit 1; }

mkdir -p "$output_dir"
LOOM_ROOT="$repo_root" \
SURFACE_BITSTREAM="$bitstream" \
SURFACE_RTL_SHA256="$rtl_sha256" \
SURFACE_MODE="$mode" \
  xsdb "$repo_root/fpga/zc702/surface_matrix/silicon_campaign.tcl" \
  | tee "$output_dir/silicon.log"
grep -q "^SURFACE_MATRIX_SILICON_PASS mode=$mode " "$output_dir/silicon.log"

sha256sum "$bitstream" "$route_dir/routed.dcp" "$status" "$signoff" \
  "$output_dir/silicon.log" >"$output_dir/artifacts.sha256"
{
  echo -e "field\tvalue"
  echo -e "result\tPASS"
  echo -e "mode\t$mode"
  echo -e "rtl_sha256\t$rtl_sha256"
  echo -e "route_inputs_sha256\t$route_inputs_sha256"
  echo -e "routed_dcp_sha256\t$(sha256sum "$route_dir/routed.dcp" | awk '{print $1}')"
  echo -e "bitstream_sha256\t$(sha256sum "$bitstream" | awk '{print $1}')"
  echo -e "silicon_log_sha256\t$(sha256sum "$output_dir/silicon.log" | awk '{print $1}')"
} >"$output_dir/silicon-status.tsv"
echo "SURFACE_MATRIX_SILICON_ARTIFACT_PASS mode=$mode directory=$output_dir"
