#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
if (($# != 2)); then
  echo "usage: $0 VIVADO_SEED_DIRECTORY OUTPUT_DIRECTORY" >&2
  exit 2
fi
seed_root=$(realpath "$1")
output_dir=$(realpath -m "$2")
seed_table="$seed_root/seed-artifacts.tsv"
selection="$seed_root/long-soak-selection.env"
test -s "$seed_table" || { echo "missing seed artifact table: $seed_table" >&2; exit 1; }
test -s "$selection" || { echo "missing long-soak selection: $selection" >&2; exit 1; }

mapfile -t seeds < <(awk -F '\t' 'NR > 1 {print $1}' "$seed_table")
((${#seeds[@]} >= 2)) || { echo "at least two routed implementations are required" >&2; exit 1; }
mapfile -t input_hashes < <(awk -F '\t' 'NR > 1 {print $5}' "$seed_table" | sort -u)
((${#input_hashes[@]} == 1)) || { echo "routed implementations do not share exact inputs" >&2; exit 1; }
long_seed=$(awk -F '=' '$1 == "LONG_SOAK_SEED" {print $2}' "$selection")
[[ "$long_seed" =~ ^[1-9][0-9]*$ ]] || { echo "invalid long-soak seed selection" >&2; exit 1; }
printf '%s\n' "${seeds[@]}" | grep -qx "$long_seed" || {
  echo "long-soak seed is absent from seed artifact table" >&2
  exit 1
}
minimum_slack_seed=$(awk -F '\t' 'NR == 2 || $3 < minimum {minimum=$3; seed=$1} END {print seed}' \
  "$seed_table")
[[ "$long_seed" == "$minimum_slack_seed" ]] || {
  echo "long-soak selection is not the minimum-slack implementation" >&2
  exit 1
}

mkdir -p "$output_dir"
for seed in "${seeds[@]}"; do
  route_dir="$seed_root/implementation-$seed/route-seed-$seed-none"
  "$repo_root/scripts/run_surface_matrix_silicon.sh" \
    "$route_dir" "$output_dir/seed-$seed-short" short
done
long_route="$seed_root/implementation-$long_seed/route-seed-$long_seed-none"
"$repo_root/scripts/run_surface_matrix_silicon.sh" \
  "$long_route" "$output_dir/seed-$long_seed-soak" soak

{
  echo -e "seed\tmode\tresult\troute_inputs_sha256\tbitstream_sha256\tsilicon_log_sha256"
  for seed in "${seeds[@]}"; do
    short_status="$output_dir/seed-$seed-short/silicon-status.tsv"
    echo -e "$seed\tshort\t$(awk -F '\t' '$1 == "result" {print $2}' "$short_status")\t$(awk -F '\t' '$1 == "route_inputs_sha256" {print $2}' "$short_status")\t$(awk -F '\t' '$1 == "bitstream_sha256" {print $2}' "$short_status")\t$(awk -F '\t' '$1 == "silicon_log_sha256" {print $2}' "$short_status")"
  done
  soak_status="$output_dir/seed-$long_seed-soak/silicon-status.tsv"
  echo -e "$long_seed\tsoak\t$(awk -F '\t' '$1 == "result" {print $2}' "$soak_status")\t$(awk -F '\t' '$1 == "route_inputs_sha256" {print $2}' "$soak_status")\t$(awk -F '\t' '$1 == "bitstream_sha256" {print $2}' "$soak_status")\t$(awk -F '\t' '$1 == "silicon_log_sha256" {print $2}' "$soak_status")"
} >"$output_dir/silicon-campaigns.tsv"

if awk -F '\t' 'NR > 1 && $3 != "PASS" {bad=1} END {exit bad}' \
    "$output_dir/silicon-campaigns.tsv"; then
  echo "SURFACE_MATRIX_SEED_SILICON_PASS seeds=${seeds[*]} long_soak_seed=$long_seed route_inputs_sha256=${input_hashes[0]}"
else
  echo "one or more seed silicon campaigns did not pass" >&2
  exit 1
fi
