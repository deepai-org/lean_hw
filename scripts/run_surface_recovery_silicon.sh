#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
if (($# != 2)); then
  echo "usage: $0 ROUTE_DIRECTORY OUTPUT_DIRECTORY" >&2
  exit 2
fi
route_dir=$(realpath "$1")
output_dir=$(realpath -m "$2")
bitstream="$route_dir/surface_recovery.bit"
status="$route_dir/route-status.tsv"
signoff="$route_dir/vivado-signoff.md"
for artifact in "$bitstream" "$status" "$signoff" "$route_dir/routed.dcp"; do
  test -s "$artifact" || { echo "missing routed recovery artifact: $artifact" >&2; exit 1; }
done
grep -q $'^status\tPASS$' "$status" || { echo "recovery route status is not PASS" >&2; exit 1; }
grep -q $'^variant\trecovery$' "$status" || { echo "route is not the recovery variant" >&2; exit 1; }
if grep -Eq '^- (FAIL|SKIP|UNCONSTRAINED):' "$signoff"; then
  echo "recovery physical signoff contains a non-PASS requirement" >&2
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
  echo "routed recovery design changed after signoff" >&2
  exit 1
}
[[ "$signed_bitstream_sha256" == "$(sha256sum "$bitstream" | awk '{print $1}')" ]] || {
  echo "recovery bitstream changed after signoff" >&2
  exit 1
}
command -v xsdb >/dev/null || { echo "xsdb is required on the board host" >&2; exit 1; }

mkdir -p "$output_dir"
LOOM_ROOT="$repo_root" \
SURFACE_BITSTREAM="$bitstream" \
SURFACE_RTL_SHA256="$rtl_sha256" \
  xsdb "$repo_root/fpga/zc702/surface_matrix/silicon_recovery_campaign.tcl" \
  | tee "$output_dir/silicon-recovery.log"
grep -q '^SURFACE_RECOVERY_SILICON_PASS ' "$output_dir/silicon-recovery.log"

sha256sum "$bitstream" "$route_dir/routed.dcp" "$status" "$signoff" \
  "$output_dir/silicon-recovery.log" >"$output_dir/artifacts.sha256"
{
  echo -e "field\tvalue"
  echo -e "result\tPASS"
  echo -e "variant\trecovery"
  echo -e "rtl_sha256\t$rtl_sha256"
  echo -e "route_inputs_sha256\t$route_inputs_sha256"
  echo -e "routed_dcp_sha256\t$(sha256sum "$route_dir/routed.dcp" | awk '{print $1}')"
  echo -e "bitstream_sha256\t$(sha256sum "$bitstream" | awk '{print $1}')"
  echo -e "silicon_log_sha256\t$(sha256sum "$output_dir/silicon-recovery.log" | awk '{print $1}')"
} >"$output_dir/silicon-status.tsv"
echo "SURFACE_RECOVERY_SILICON_ARTIFACT_PASS directory=$output_dir"
