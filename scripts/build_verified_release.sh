#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Build, byte-bind, and audit both publication release artifacts.
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
  # Generated proof modules can consume several GiB each. Eight workers is a
  # deliberate host-safety ceiling; callers may request fewer, never more.
  ((jobs > 8)) && jobs=8
fi
if [[ ! "$jobs" =~ ^[1-9][0-9]*$ ]]; then
  echo "jobs must be a positive integer" >&2
  exit 2
fi
if ((jobs > 8)); then
  echo "jobs must be at most 8 (release proofs are memory-heavy)" >&2
  exit 2
fi
monitor_pid=

source "$(dirname "${BASH_SOURCE[0]}")/phase_timing.sh"

stop_monitor() {
  if [[ -n "${monitor_pid:-}" ]]; then
    kill "$monitor_pid" 2>/dev/null || true
    wait "$monitor_pid" 2>/dev/null || true
  fi
}
trap stop_monitor EXIT

metrics_dir=".lake/release-metrics/lnp64u-$(date -u +%Y%m%dT%H%M%SZ)"
done_file="$metrics_dir/full-release-complete"

# Per-phase wall/CPU timings for the whole run, including the child witness and
# action-cut scripts, land in one CSV. Exported so those children append to the
# same file instead of each inventing its own.
export LOOM_PHASE_LOG="$PWD/$metrics_dir/phases.csv"
export LOOM_PHASE_SCOPE=release
loom_phase_log_init
echo "release phase timings: $LOOM_PHASE_LOG"
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
run_phase "certified multiclock artifact" lake exe emitCertifiedMulticlock
run_phase "multiclock theorem axiom closure" scripts/audit_multiclock_release.sh
run_phase "RTL X/Z hygiene" scripts/check_xfree_rtl.py \
  rtl/acc8.v rtl/lnp64u.v rtl/certified_multiclock/system.v
mkdir -p .lake/build/lib/lean/Tools

# VerifiedRelease.lean and ReleaseAudit.lean are compiled directly with
# `lean`, outside Lake's module graph, so their Loom/Machines imports have no
# objects on a clean checkout unless built explicitly. Derive the set by
# scanning rather than naming it: the hand-maintained list in
# build_release_witness.sh named 7 of 18 and failed once per missing entry.
build_theorem_prerequisites() {
  local -a targets
  mapfile -t targets < <(
    grep -h '^import \(Loom\|Machines\)\.' \
      Tools/VerifiedRelease.lean Tools/ReleaseAudit.lean 2>/dev/null |
      awk '{print $2}' | sort -u)
  ((${#targets[@]} == 0)) && return 0
  lake build "${targets[@]}"
}
run_phase "release theorem prerequisites" build_theorem_prerequisites

run_release_axiom_audit() {
  # Collecting the generated processor closure is intentionally serialized
  # but peaks near 22 GiB resident. On cgroup-v2/systemd hosts contain that
  # phase so a regression kills only the audit rather than invoking earlyoom
  # against the whole interactive machine. Keep a little measured headroom.
  if command -v systemd-run >/dev/null 2>&1 &&
      systemctl --user show-environment >/dev/null 2>&1; then
    systemd-run --user --wait --collect --pipe \
      --working-directory="$PWD" \
      -p MemoryMax=28G -p MemorySwapMax=0 \
      lake exe releaseAudit
  else
    echo "release audit: cgroup containment unavailable; running serially" >&2
    lake exe releaseAudit
  fi
}

run_phase "combined release theorem" lake env lean \
  "$(realpath Tools/VerifiedRelease.lean)" \
  -o "$(realpath .lake/build/lib/lean/Tools)/VerifiedRelease.olean"
# Compiled walker (builds in <1 s from cold; only imports Lean). Measured
# 698 s interpreted -> 607 s compiled: the phase is dominated by olean
# deserialization of the release closure, not interpretation.
run_phase "release theorem axiom closure" run_release_axiom_audit
if [[ -n "${monitor_pid:-}" ]]; then
  touch "$done_file"
  wait "$monitor_pid"
  monitor_pid=
  echo "Release verification metrics: $metrics_dir"
fi
echo "VERIFIED: rtl/acc8.v, rtl/lnp64u.v, and rtl/certified_multiclock/system.v"
echo "are the exact bound renderings in"
echo "Loom.Release.Theorems.verifiedReleases; kernel axiom closure is exactly"
echo "propext, Classical.choice, and Quot.sound. Yosys interpretation remains"
echo "the documented boundary."
