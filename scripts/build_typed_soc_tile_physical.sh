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

expected='  reg [31:0] contract_memory [0:511];'
matches=$(grep -Fxc "$expected" "$neutral_rtl" || true)
[[ "$matches" == 1 ]] || {
  echo "expected exactly one contract_memory declaration, found $matches" >&2
  exit 1
}
grep -Fq 'module typed_soc_tile_memory_contract(' "$neutral_rtl" || {
  echo "contract memory island module is missing" >&2
  exit 1
}
grep -Fq 'reg [31:0] internal_memory [0:511];' "$neutral_rtl" || {
  echo "internal Loom memory lane is missing" >&2
  exit 1
}

mkdir -p "$output_dir"
sed 's/^  reg \[31:0\] contract_memory \[0:511\];$/  (* ram_style = "block" *) reg [31:0] contract_memory [0:511];/' \
  "$neutral_rtl" > "$output_dir/system.v"
cp "$neutral_dir/crossings.md" "$neutral_dir/clock_constraints.md" "$output_dir/"

[[ $(grep -Fc '(* ram_style = "block" *) reg [31:0] contract_memory [0:511];' \
  "$output_dir/system.v") == 1 ]] || {
  echo "physical BRAM selection marker is missing or duplicated" >&2
  exit 1
}
if grep -Fq 'ram_style = "block" *) reg [31:0] internal_memory' "$output_dir/system.v"; then
  echo "internal Loom lane was unexpectedly target-bound" >&2
  exit 1
fi

neutral_sha=$(sha256sum "$neutral_rtl" | awk '{print $1}')
physical_sha=$(sha256sum "$output_dir/system.v" | awk '{print $1}')
{
  printf '# Typed SoC tile physical memory binding\n\n'
  printf '%s\n' '- logical island: `tile_memory_contract`'
  printf '%s\n' '- logical memory: `contract_memory`'
  printf '%s\n' '- target implementation: inferred Xilinx 7-series single-clock 512x32 block RAM'
  printf '%s\n' "- neutral RTL SHA-256: \`$neutral_sha\`"
  printf '%s\n' "- physical RTL SHA-256: \`$physical_sha\`"
  printf '%s\n' '- evidence classification: external assumption, checked by target inference/routing/silicon'
  printf '%s\n' '- assumption: the selected physical RAM implements the neutral synchronous-read,'
  printf '%s\n' '  byte-masked-write behavior for all transactions admitted by the memory island.'
  printf '%s\n' '- unchanged lane: `internal_memory` remains the ordinary Loom-generated memory.'
  printf '%s\n' '- CDC boundary: neither memory is dual-clock; only the four generated channel FIFOs'
  printf '%s\n' '  cross between `tile_core_clk` and `tile_memory_clk`.'
} > "$output_dir/contract-binding.md"

sha256sum "$output_dir/system.v" "$output_dir/crossings.md" \
  "$output_dir/clock_constraints.md" "$output_dir/contract-binding.md" \
  > "$output_dir/SHA256SUMS"
printf 'TYPED_SOC_TILE_PHYSICAL_OK neutral_sha256=%s physical_sha256=%s directory=%s\n' \
  "$neutral_sha" "$physical_sha" "$output_dir"
