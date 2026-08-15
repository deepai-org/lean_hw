#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
if (($# < 1)); then
  echo "usage: $0 OUTPUT_DIRECTORY [SEED ...]" >&2
  exit 2
fi
output_dir=$(realpath -m "$1")
shift
seeds=("$@")
if ((${#seeds[@]} == 0)); then seeds=(1 2 3); fi
mkdir -p "$output_dir"

reference_inputs=
worst_seed=
worst_slack=
for seed in "${seeds[@]}"; do
  run_root="$output_dir/implementation-$seed"
  "$repo_root/scripts/build_surface_matrix_vivado.sh" "$run_root" "$seed" none
  route_dir="$run_root/route-seed-$seed-none"
  digest=$(sha256sum "$route_dir/route-inputs.sha256" | awk '{print $1}')
  if [[ -z "$reference_inputs" ]]; then
    reference_inputs=$digest
  elif [[ "$digest" != "$reference_inputs" ]]; then
    echo "route inputs differ between implementation seeds" >&2
    exit 1
  fi
  test -s "$route_dir/vivado-signoff.md"
  if grep -Eq '^- (FAIL|SKIP|UNCONSTRAINED):' "$route_dir/vivado-signoff.md"; then
    echo "seed $seed contains a non-PASS physical requirement" >&2
    exit 1
  fi
  slack=$(awk -F '\t' '$1 == "worst_setup_slack_ns" {print $2}' "$route_dir/route-status.tsv")
  if [[ -z "$slack" ]]; then
    echo "seed $seed has no routed worst-slack metric" >&2
    exit 1
  fi
  if [[ -z "$worst_seed" ]] || awk -v candidate="$slack" -v current="$worst_slack" \
      'BEGIN {exit !(candidate < current)}'; then
    worst_seed=$seed
    worst_slack=$slack
  fi
done

{
  echo -e "seed\tplace_directive\tworst_setup_slack_ns\tmax_sync_manhattan\troute_inputs_sha256\trouted_dcp_sha256\tbitstream_sha256"
  for seed in "${seeds[@]}"; do
    route_dir="$output_dir/implementation-$seed/route-seed-$seed-none"
    directive=$(awk -F '\t' '$1 == "place_directive" {print $2}' "$route_dir/route-status.tsv")
    slack=$(awk -F '\t' '$1 == "worst_setup_slack_ns" {print $2}' "$route_dir/route-status.tsv")
    max_distance=$(awk -F '\t' 'NR > 1 && $7 > max {max=$7} END {print max+0}' \
      "$route_dir/synchronizer-placement.tsv")
    echo -e "$seed\t$directive\t$slack\t$max_distance\t$reference_inputs\t$(sha256sum "$route_dir/routed.dcp" | awk '{print $1}')\t$(sha256sum "$route_dir/surface_matrix.bit" | awk '{print $1}')"
  done
} >"$output_dir/seed-artifacts.tsv"
{
  echo "LONG_SOAK_SEED=$worst_seed"
  echo "LONG_SOAK_WORST_SETUP_SLACK_NS=$worst_slack"
  echo "LONG_SOAK_SELECTION_REASON=minimum_routed_setup_slack"
} >"$output_dir/long-soak-selection.env"
echo "SURFACE_MATRIX_VIVADO_SEEDS_PASS seeds=${seeds[*]} route_inputs_sha256=$reference_inputs long_soak_seed=$worst_seed"
