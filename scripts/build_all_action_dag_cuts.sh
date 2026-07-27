#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Generate and kernel-check every LNP64-u action cut through one worker pool.
set -euo pipefail

jobs=${1:-}
if [[ -z "$jobs" ]]; then
  cores=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)
  if [[ -r /proc/meminfo ]]; then
    available_kb=$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo)
    memory_jobs=$((available_kb / 4000000))
  else
    memory_jobs=1
  fi
  ((memory_jobs < 1)) && memory_jobs=1
  jobs=$cores
  ((jobs > memory_jobs)) && jobs=$memory_jobs
  ((jobs > 32)) && jobs=32
fi

if [[ ! "$jobs" =~ ^[1-9][0-9]*$ ]]; then
  echo "jobs must be a positive integer" >&2
  exit 2
fi

src=GeneratedRelease/Lnp64u
lib=.lake/build/lib/lean/GeneratedRelease/Lnp64u
runtime="$src/Runtime.tsv"
cut_count=12

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
    mkdir -p "$(dirname "$output")"
    lake env lean -j 1 "$(realpath "$source")" -o "$output"
  fi
}
export -f compile_generated

compile_stream() {
  xargs -0 -r -n1 -P "$jobs" bash -c 'compile_generated "$1"' _
}
export jobs
export -f compile_stream

generate_cut() {
  local index=$1
  local suffix
  printf -v suffix '%03d' "$index"
  lake exe actionwidegen lnp64u-dag-cut "$runtime" \
    "$src/DagCut${suffix}.lean" "$index"
}
export runtime src
export -f generate_cut

mkdir -p "$lib"
echo "all action cuts: using one pool of $jobs checker workers"

run_phase "action DAG prerequisites" lake build actionwidegen \
  Loom.Release.SymbolicDecide Machines.Lnp64u.Theorems.ReleaseOrder

# These compact wire views are emitted by gen_release_witness.py and are the
# only wire objects used by the action checker.  Build their dependency layers
# explicitly so this script works after deleting the entire generated olean
# tree; previously a clean run silently depended on stale objects.
run_phase "fast indexed wire blocks" bash -c \
  "find '$src' -maxdepth 1 -name 'FastIndexedBatch*.lean' -print0 | sort -z | compile_stream"
run_phase "fast indexed wire root" compile_generated "$src/FastIndexedRoot.lean"
run_phase "fast lookup evidence" bash -c \
  "find '$src' -maxdepth 1 -name 'FastLookupEvidenceBatch*.lean' -print0 | sort -z | compile_stream"
run_phase "fast lookup root" compile_generated "$src/FastLookupEvidenceRoot.lean"

# Generate one action certificate in O(actions), not one traversal per
# register.  Join payloads are grouped into data-only modules; their local
# acceptance theorems were unused because every join is checked again by the
# action/cut evidence below.
run_phase "generate shared join data" lake exe actionwidegen \
  lnp64u-local-joins "$runtime" "$src"
run_phase "shared join data" bash -c \
  "find '$src' -maxdepth 1 -name 'ActionJoinBatch*.lean' -print0 | sort -z | compile_stream"
run_phase "generate shared action certificate" lake exe actionwidegen \
  lnp64u-named-cert "$runtime" "$src/ActionCert.lean"
run_phase "shared action certificate" compile_generated "$src/ActionCert.lean"

generation_jobs=$jobs
((generation_jobs > 8)) && generation_jobs=8
run_phase "generate all action cuts" bash -c \
  "seq 0 $((cut_count - 1)) | xargs -n1 -P $generation_jobs bash -c 'generate_cut \"\$1\"' _"

# Remove shards from older cut layouts so broad phase globs cannot compile a
# retired experiment (notably the former monolithic whole-core cut).
for generated in "$src"/DagCut[0-9][0-9][0-9]*.lean; do
  base=${generated##*/}
  index=${base:6:3}
  if ((10#$index >= cut_count)); then
    rm -f "$generated"
  fi
done
for generated in "$lib"/DagCut[0-9][0-9][0-9]*.olean \
    "$lib"/DagCut[0-9][0-9][0-9]*.ilean; do
  [[ -e "$generated" ]] || continue
  base=${generated##*/}
  index=${base:6:3}
  if ((10#$index >= cut_count)); then
    rm -f "$generated"
  fi
done

# Source pruning is performed by the generator. Remove compiled objects whose
# source disappeared so retries cannot silently consume an ever-growing cache.
while IFS= read -r -d '' compiled; do
  relative=${compiled#".lake/build/lib/lean/"}
  source=${relative%.olean}.lean
  if [[ ! -f "$source" ]]; then
    rm -f "$compiled" "${compiled%.olean}.ilean"
  fi
done < <(find "$lib" -maxdepth 1 -name 'DagCut*.olean' -print0)

run_phase "action cut metadata" bash -c \
  "find '$src' -maxdepth 1 -name 'DagCut???Meta.lean' -print0 | sort -z | compile_stream"
run_phase "named join lookups" bash -c \
  "find '$src' -maxdepth 1 -name 'DagCut???JoinLookup*.lean' -print0 | sort -z | compile_stream"
run_phase "action leaves and join checks" bash -c \
  "find '$src' -maxdepth 1 \\
    \( -name 'DagCut???Leaf*.lean' -o -name 'DagCut???ConnectorCheck*.lean' \) \\
    -print0 | sort -z | compile_stream"

# Connector batches are ordered within a cut. Compile equal batch numbers
# together, then advance globally; this preserves dependencies without running
# ten independent worker pools.
batch=0
while :; do
  printf -v suffix '%03d' "$batch"
  mapfile -d '' connectors < <(find "$src" -maxdepth 1 \
    -name "DagCut???Connector${suffix}.lean" ! -name '*ConnectorCheck*' -print0)
  ((${#connectors[@]} == 0)) && break
  printf '%s\0' "${connectors[@]}" | compile_stream
  batch=$((batch + 1))
done

run_phase "action cut roots" bash -c \
  "find '$src' -maxdepth 1 -name 'DagCut???.lean' -print0 | sort -z | compile_stream"

echo "all LNP64-u action cuts kernel-checked"
