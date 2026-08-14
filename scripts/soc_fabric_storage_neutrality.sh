#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 OUTPUT_DIRECTORY" >&2
  exit 2
fi

output_dir=$1
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$script_dir/.." && pwd)
neutral_dir="$output_dir/neutral"
bram_dir="$output_dir/bram"
mkdir -p "$neutral_dir" "$bram_dir"

cd "$repo_root"
lake exe socFabricStorageNeutralityEmit "$neutral_dir" "$bram_dir"
cp fpga/zc702/tb_soc_fabric_storage_neutrality.v "$output_dir/testbench.v"

[[ $(grep -c '^module .*_registered_target_storage(' "$bram_dir/system.v") -eq 5 ]]
[[ $(grep -c '^assign read_launch = fifo_sink_valid && !payload_ready;$' \
  "$bram_dir/system.v") -eq 5 ]]
[[ $(grep -c '^assign fifo_pop = payload_ready && dst_pop;$' \
  "$bram_dir/system.v") -eq 5 ]]
[[ $(grep -c 'ram_style = "block"' "$bram_dir/system.v") -eq 5 ]]

iverilog -g2005 -s tb_soc_fabric_storage_neutrality \
  -o "$neutral_dir/simulation.vvp" \
  "$neutral_dir/system.v" "$output_dir/testbench.v"
vvp "$neutral_dir/simulation.vvp" >"$neutral_dir/simulation.log"

iverilog -g2005 -s tb_soc_fabric_storage_neutrality \
  -o "$bram_dir/simulation.vvp" \
  "$bram_dir/system.v" "$output_dir/testbench.v"
vvp "$bram_dir/simulation.vvp" >"$bram_dir/simulation.log"

grep '^STORAGE_NEUTRALITY_PASS$' "$neutral_dir/simulation.log" >/dev/null
grep '^STORAGE_NEUTRALITY_PASS$' "$bram_dir/simulation.log" >/dev/null
grep '^METRICS ' "$neutral_dir/simulation.log" >"$neutral_dir/metrics.txt"
grep '^METRICS ' "$bram_dir/simulation.log" >"$bram_dir/metrics.txt"
diff -u "$neutral_dir/metrics.txt" "$bram_dir/metrics.txt" \
  >"$output_dir/metrics.diff"

yosys -p "read_verilog $bram_dir/system.v; hierarchy -check -top loom_system; synth_xilinx -family xc7 -top loom_system; stat" \
  >"$bram_dir/yosys-xc7.log" 2>&1
grep -E 'RAMB36E1[[:space:]]+5$' "$bram_dir/yosys-xc7.log" >/dev/null

neutral_sha=$(sha256sum "$neutral_dir/system.v" | awk '{print $1}')
bram_sha=$(sha256sum "$bram_dir/system.v" | awk '{print $1}')
testbench_sha=$(sha256sum "$output_dir/testbench.v" | awk '{print $1}')
metrics_sha=$(sha256sum "$neutral_dir/metrics.txt" | awk '{print $1}')

cat >"$output_dir/manifest.json" <<EOF
{
  "schema": 1,
  "experiment": "soc-fabric-storage-neutrality",
  "loom_system": "Machines.Multiclock.SoCFabricGauntlet.system",
  "neutral_system_v_sha256": "$neutral_sha",
  "bram_system_v_sha256": "$bram_sha",
  "testbench_sha256": "$testbench_sha",
  "identical_metrics_sha256": "$metrics_sha",
  "transactions_per_client": 256,
  "registered_leaf_count": 5,
  "registered_leaf_read_stages": 1,
  "registered_leaf_sink_issue_interval_ticks": 3,
  "synthesized_xc7_cell": "RAMB36E1",
  "synthesized_xc7_cell_count": 5,
  "result": "PASS"
}
EOF

cat >"$output_dir/RESULT.md" <<EOF
# SoC Fabric storage-realization neutrality

- **EXACT SYSTEM: PASS.** Both artifacts instantiate the definition
  \`Machines.Multiclock.SoCFabricGauntlet.system\`; Lean checks this equality by
  reflexivity in \`StorageNeutrality.lean\`.
- **TRANSACTION RESULTS: PASS.** The same public-top testbench completed 256
  transactions per client in both artifacts. Accepted/delivered counts, grants,
  commits, audit records, digests, expected digest, and sticky errors are
  byte-identical in \`neutral/metrics.txt\` and \`bram/metrics.txt\`.
- **ZYNQ STORAGE: PASS.** Yosys \`synth_xilinx -family xc7\` maps the five
  registered target leaves to exactly five \`RAMB36E1\` cells.
- **ARTIFACT BINDING: PASS.** Exact hashes are recorded in \`manifest.json\`
  and \`SHA256SUMS\`.

This is RTL and XC7 synthesis evidence. A ZC702 silicon replay is a separate
target corroboration step.
EOF

(
  cd "$output_dir"
  sha256sum \
    RESULT.md manifest.json testbench.v metrics.diff \
    neutral/system.v neutral/clock_constraints.md neutral/crossings.md \
    neutral/simulation.log neutral/metrics.txt \
    bram/system.v bram/clock_constraints.md bram/crossings.md \
    bram/simulation.log bram/metrics.txt bram/yosys-xc7.log \
    >SHA256SUMS
)

echo "SOC_FABRIC_STORAGE_NEUTRALITY_OK neutral=$neutral_sha bram=$bram_sha"
