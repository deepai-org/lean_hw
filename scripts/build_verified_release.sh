#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Build, byte-bind, and audit both publication release artifacts.
set -euo pipefail

jobs=${1:-8}
monitor_pid=

stop_monitor() {
  if [[ -n "${monitor_pid:-}" ]]; then
    kill "$monitor_pid" 2>/dev/null || true
    wait "$monitor_pid" 2>/dev/null || true
  fi
}
trap stop_monitor EXIT

metrics_dir=".lake/release-metrics/lnp64u-$(date -u +%Y%m%dT%H%M%SZ)"
done_file="$metrics_dir/full-release-complete"
if [[ -r /proc/uptime && -r /proc/meminfo ]]; then
  python3 scripts/monitor_release_build.py Lnp64u --output "$metrics_dir" \
    --done-file "$done_file" &
monitor_pid=$!
else
  echo "release metrics: /proc unavailable; proof build continues without Linux telemetry"
fi

python3 scripts/test_release_binding.py
lake build
scripts/build_release_witness.sh acc8 "$jobs"
scripts/build_release_witness.sh lnp64u "$jobs"
scripts/check_xfree_rtl.py rtl/acc8.v rtl/lnp64u.v
lake exe audit
mkdir -p .lake/build/lib/lean/Tools
lake env lean "$(realpath Tools/VerifiedRelease.lean)" \
  -o "$(realpath .lake/build/lib/lean/Tools)/VerifiedRelease.olean"
lake env lean --run "$(realpath Tools/ReleaseAudit.lean)"
if [[ -n "${monitor_pid:-}" ]]; then
  touch "$done_file"
  wait "$monitor_pid"
  monitor_pid=
  echo "Release verification metrics: $metrics_dir"
fi
echo "VERIFIED: rtl/acc8.v and rtl/lnp64u.v are the exact bound renderings in"
echo "Loom.Release.Theorems.verifiedReleases; kernel axiom closure is exactly"
echo "propext, Classical.choice, and Quot.sound. Yosys interpretation remains"
echo "the documented boundary."
