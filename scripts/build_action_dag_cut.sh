#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Generate and kernel-check one hash-consed LNP64-u action cut.
set -euo pipefail

cut_index=${1:-0}
# Twelve workers keep the measured peak below the 123 GiB publication host's
# memory ceiling even when large leaves and join modules overlap.
jobs=${2:-12}

if [[ ! "$cut_index" =~ ^[0-9]+$ || "$cut_index" -gt 999 ]]; then
  echo "cut index must be an integer from 0 through 999" >&2
  exit 2
fi
if [[ ! "$jobs" =~ ^[1-9][0-9]*$ ]]; then
  echo "jobs must be a positive integer" >&2
  exit 2
fi

printf -v suffix '%03d' "$cut_index"
src=GeneratedRelease/Lnp64u
lib=.lake/build/lib/lean/GeneratedRelease/Lnp64u
runtime="$src/Runtime.tsv"
root="$src/DagCut$suffix.lean"

if [[ ! -f "$runtime" ]]; then
  echo "missing $runtime; generate the LNP64-u release witness first" >&2
  exit 1
fi

run_phase() {
  local label=$1
  shift
  local started=$SECONDS
  echo "==> $label"
  "$@"
  echo "<== $label: $((SECONDS - started))s"
}

compile_generated() {
  local source=$1
  local stem=${source%.lean}
  local output=".lake/build/lib/lean/$stem.olean"
  local rebuild=0
  if [[ ! -f "$output" || "$source" -nt "$output" ]]; then
    rebuild=1
  else
    while read -r _ module _; do
      local dependency=".lake/build/lib/lean/${module//./\/}.olean"
      if [[ -f "$dependency" && "$dependency" -nt "$output" ]]; then
        rebuild=1
        break
      fi
    done < <(grep '^import ' "$source")
  fi
  if [[ "$rebuild" == 1 ]]; then
    lake env lean "$(realpath "$source")" -o "$output"
  fi
}
export -f compile_generated

compile_parallel() {
  xargs -0 -r -n1 -P "$jobs" bash -c 'compile_generated "$1"' _
}

compile_node_shards() {
  find "$src" -maxdepth 1 -name "DagCut${suffix}Nodes*.lean" -print0 | \
    sort -z | compile_parallel
}

compile_resolver_shards() {
  find "$src" -maxdepth 1 -name "DagCut${suffix}Resolvers*.lean" -print0 | \
    sort -z | compile_parallel
}

compile_parallel_proofs() {
  find "$src" -maxdepth 1 \
    \( -name "DagCut${suffix}Leaf*.lean" -o \
       -name "DagCut${suffix}ConnectorCheck*.lean" -o \
       -name "DagCut${suffix}Lookup*.lean" \) \
    -print0 | sort -z | compile_parallel
}

compile_join_lookups() {
  find "$src" -maxdepth 1 -name "DagCut${suffix}JoinLookup*.lean" -print0 | \
    sort -z | compile_parallel
}

mkdir -p "$lib"
run_phase "action DAG prerequisites" lake build actionwidegen \
  Loom.Release.SymbolicDecide Machines.Lnp64u.Theorems.ReleaseOrder
run_phase "generate action cut $suffix" lake exe actionwidegen lnp64u-dag-cut \
  "$runtime" "$root" "$cut_index"

# The state shards are independent. Resolvers depend on them, and the balanced
# data root depends on both sets, so keep these three stages explicit.
run_phase "state node shards" compile_node_shards
run_phase "state resolver shards" compile_resolver_shards
run_phase "state DAG root" compile_generated "$src/DagCut${suffix}Data.lean"

# Connector checks import these named mux facts. Check each global wire lookup
# once in a small shard instead of reopening the indexed-wire rope at every
# action node.
run_phase "named join lookups" compile_join_lookups

# Leaves and outer conditional checks share only the immutable data roots, so
# run them in one worker pool. This overlaps the two dominant proof workloads.
run_phase "action leaves and join checks" compile_parallel_proofs

# Connector batches are postorder and may import their predecessor.
while IFS= read -r -d '' connector; do
  run_phase "$(basename "${connector%.lean}")" compile_generated "$connector"
done < <(find "$src" -maxdepth 1 -name "DagCut${suffix}Connector*.lean" \
  ! -name '*ConnectorCheck*' -print0 | sort -z)
run_phase "action cut root" compile_generated "$root"

echo "LNP64-u action cut $suffix kernel-checked"
