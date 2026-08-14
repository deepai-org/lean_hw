#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 OUTPUT_DIRECTORY" >&2
  exit 2
fi

output_dir=$1
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$script_dir/.." && pwd)
mkdir -p "$output_dir"

cd "$repo_root"
lake exe socFabricRecoveryEmit "$output_dir"
cp fpga/zc702/tb_soc_fabric_recovery.v "$output_dir/testbench.v"

iverilog -g2005 -s tb_soc_fabric_recovery \
  -o "$output_dir/simulation.vvp" \
  "$output_dir/system.v" "$output_dir/testbench.v"
vvp "$output_dir/simulation.vvp" >"$output_dir/simulation.log"

grep '^SOC_RECOVERY_PASS$' "$output_dir/simulation.log" >/dev/null
grep '^RECOVERY_CUT ' "$output_dir/simulation.log" >"$output_dir/recovery-cut.txt"
grep '^RECOVERY_COMPLETE ' "$output_dir/simulation.log" >"$output_dir/recovery-complete.txt"
grep '^RESTART_METRICS ' "$output_dir/simulation.log" >"$output_dir/restart-metrics.txt"

grep 'lost_requests=1 lost_responses=1 unaffected_audit=1' \
  "$output_dir/recovery-cut.txt" >/dev/null
grep 'endpoints=12 discarded=2 incident_occupancy=0' \
  "$output_dir/recovery-complete.txt" >/dev/null
grep 'cpu_accepted=256 cpu_responses=256' \
  "$output_dir/restart-metrics.txt" >/dev/null
grep 'dma_accepted=256 dma_responses=256' \
  "$output_dir/restart-metrics.txt" >/dev/null
grep 'total_grants=512 routed=512 commits=512 records=512' \
  "$output_dir/restart-metrics.txt" >/dev/null
grep 'errors=0000$' "$output_dir/restart-metrics.txt" >/dev/null

rtl_sha=$(sha256sum "$output_dir/system.v" | awk '{print $1}')
testbench_sha=$(sha256sum "$output_dir/testbench.v" | awk '{print $1}')
cut_sha=$(sha256sum "$output_dir/recovery-cut.txt" | awk '{print $1}')
complete_sha=$(sha256sum "$output_dir/recovery-complete.txt" | awk '{print $1}')
restart_sha=$(sha256sum "$output_dir/restart-metrics.txt" | awk '{print $1}')

cat >"$output_dir/manifest.json" <<EOF
{
  "schema": 1,
  "experiment": "soc-fabric-recovery-under-load",
  "loom_system": "Machines.Multiclock.SoCFabricGauntlet.Recovery.recoveryFabric",
  "system_v_sha256": "$rtl_sha",
  "testbench_sha256": "$testbench_sha",
  "recovery_cut_sha256": "$cut_sha",
  "recovery_complete_sha256": "$complete_sha",
  "restart_metrics_sha256": "$restart_sha",
  "requested_island": "fabric",
  "incident_crossings": 6,
  "completion_endpoints": 12,
  "discarded_values": 2,
  "retained_unrelated_audit_values": 1,
  "restart_transactions_per_client": 256,
  "result": "PASS"
}
EOF

cat >"$output_dir/RESULT.md" <<EOF
# SoC Fabric recovery under load

- **REACHABLE LOADED CUT: PASS.** Requests, responses, and audit traffic are
  simultaneously resident in three distinct physical crossings. The exact cut
  is recorded in \`recovery-cut.txt\`.
- **LOSS ACCOUNTING: PASS.** Requesting recovery only for \`fabric\` discards
  one incident request and one incident response. The unrelated audit value is
  retained.
- **COORDINATED COMPLETION: PASS.** Recovery reports complete only after all
  twelve endpoint halves belonging to the six incident crossings acknowledge;
  their resulting physical occupancy is zero.
- **RESTART AND FORWARD PROGRESS: PASS.** After recovery, the supported common
  reset begins a fresh application epoch. Both clients complete 256
  transactions and all counts, ordering/digest checks, and sticky errors pass.
- **ARTIFACT BINDING: PASS.** Exact RTL, testbench, cut, completion, and restart
  hashes are recorded in \`manifest.json\` and \`SHA256SUMS\`.

The cut intentionally does not claim all seven FIFOs can be occupied at once:
the application permits one outstanding request per client and one outstanding
fabric transaction. It does put every traffic class through a real crossing at
the recovery boundary.
EOF

(
  cd "$output_dir"
  sha256sum \
    RESULT.md manifest.json testbench.v system.v \
    clock_constraints.md crossings.md simulation.log \
    recovery-cut.txt recovery-complete.txt restart-metrics.txt \
    >SHA256SUMS
)

echo "SOC_FABRIC_RECOVERY_OK rtl=$rtl_sha testbench=$testbench_sha"
