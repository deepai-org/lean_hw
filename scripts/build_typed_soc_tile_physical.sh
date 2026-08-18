#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
if (($# != 2)); then
  echo "usage: $0 NEUTRAL_EVIDENCE_DIRECTORY OUTPUT_DIRECTORY" >&2
  exit 2
fi
neutral_dir=$(realpath "$1")
output_dir=$(realpath -m "$2")
neutral_rtl="$neutral_dir/system.v"
neutral_manifest="$neutral_dir/tile-manifest.json"
test -s "$neutral_rtl" || { echo "missing neutral system.v" >&2; exit 1; }
test -s "$neutral_manifest" || { echo "missing neutral tile-manifest.json" >&2; exit 1; }

grep -Fq 'reg [31:0] internal_memory [0:511];' "$neutral_rtl" || {
  echo "internal Loom memory lane is missing" >&2
  exit 1
}

(
  cd "$repo_root"
  LOOM_ROOT="$repo_root" lake exe typedSoCTileEvidence --physical "$output_dir"
)

[[ $(grep -Fc '(* ram_style = "block" *) reg [31:0] contract_memory [0:511];' \
  "$output_dir/system.v") == 1 ]] || {
  echo "physical BRAM selection marker is missing or duplicated" >&2
  exit 1
}
if grep -Fq 'ram_style = "block" *) reg [31:0] internal_memory' "$output_dir/system.v"; then
  echo "internal Loom lane was unexpectedly target-bound" >&2
  exit 1
fi
test -s "$output_dir/external_islands.md" || {
  echo "Loom did not emit external_islands.md" >&2
  exit 1
}
grep -Fq '`tile_memory_rtl_contract`' "$output_dir/external_islands.md" || {
  echo "external-island report omitted the exact RTL contract assumption" >&2
  exit 1
}
grep -Fq '`tile_memory_physical_ram`' "$output_dir/external_islands.md" || {
  echo "external-island report omitted the physical RAM assumption" >&2
  exit 1
}
grep -Fq '"physical_contract_binding": "external_application"' \
  "$output_dir/tile-manifest.json" || {
  echo "physical manifest did not record ExternalApplication selection" >&2
  exit 1
}

neutral_sha=$(sha256sum "$neutral_rtl" | awk '{print $1}')
physical_sha=$(sha256sum "$output_dir/system.v" | awk '{print $1}')
printf 'TYPED_SOC_TILE_PHYSICAL_OK neutral_sha256=%s physical_sha256=%s directory=%s\n' \
  "$neutral_sha" "$physical_sha" "$output_dir"
