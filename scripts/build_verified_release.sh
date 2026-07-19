#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Build, byte-bind, and audit both publication release artifacts.
set -euo pipefail

jobs=${1:-8}
monitor_pid=

run_phase() {
  local label=$1
  shift
  local started=$SECONDS
  echo "==> $label"
  "$@"
  echo "<== $label: $((SECONDS - started))s"
}

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

run_phase "source/package quality" scripts/quality.sh
run_phase "release-binding self-tests" python3 scripts/test_release_binding.py

# Each witness builder declares and builds its precise Lean prerequisites.
# `lake build` with no target rebuilds every development theorem, executable,
# and test in the repository; that is the comprehensive CI gate, not part of
# the dependency closure of the publication theorem.
run_phase "Acc8 release witness" scripts/build_release_witness.sh acc8 "$jobs"
run_phase "LNP64-u release witness" scripts/build_release_witness.sh lnp64u "$jobs"
run_phase "RTL X/Z hygiene" scripts/check_xfree_rtl.py rtl/acc8.v rtl/lnp64u.v
mkdir -p .lake/build/lib/lean/Tools
run_phase "combined release theorem" lake env lean \
  "$(realpath Tools/VerifiedRelease.lean)" \
  -o "$(realpath .lake/build/lib/lean/Tools)/VerifiedRelease.olean"
run_phase "release theorem axiom closure" lake env lean --run \
  "$(realpath Tools/ReleaseAudit.lean)"
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
