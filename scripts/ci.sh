#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# CI = build everything + the audit gate (PLAN §10).
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Loom Machines Tests iss audit emit bookgen rtlroundtrip
lake build Tests.Acc8Bmc
lake build Tests.Lnp64uWitnesses
scripts/downstream_smoke.sh
lake exe audit
lake exe bookgen >/dev/null
lake exe emit acc8 >/dev/null
lake exe emit lnp64u >/dev/null
scripts/check_xfree_rtl.py rtl/acc8.v rtl/lnp64u.v
# The round trip on the emitted *files*: every rtl/*.v parses and reprints
# byte-identically (skips are printed with their reason).
lake exe rtlroundtrip rtl/*.v
scripts/test_release_binding.py
# --- the two silicon-boundary gates -------------------------------------
# These were standalone scripts until 2026-08-01, i.e. they only protected
# anyone who remembered to run them: D30 (yosys silently dropping a memory's
# reset image for LUTRAM-mapped banks) was caught by HARDWARE, not by its own
# guard. Both self-SKIP when their tools are absent, so CI still runs on a
# host without yosys/cadical -- but on a host that HAS them, a change that
# breaks synthesis equivalence or a memory reset image now fails here rather
# than on a board weeks later.
#
# Scope note: eqcheck runs the small designs inline (seconds). The SoC-scale
# run (~18 s + synthesis) belongs to scripts/nightly_gates.sh, not to every CI
# invocation; that split is deliberate and is why this loop names its designs.
if command -v yosys >/dev/null 2>&1 && command -v cadical >/dev/null 2>&1; then
  for d in s0blinky satcounter pingpong s13soak; do
    scripts/eqcheck.sh "$d"
  done
  scripts/eqcheck.sh --negative-control satcounter   # the checker must still bite
  scripts/check_mem_init.py
else
  echo "ci: SKIP eqcheck + mem-init gates (yosys and/or cadical not installed)"
fi
# Independent-checker cross-validation (self-SKIPs if cadical/python3 absent,
# so CI does not depend on a SAT solver being installed).
scripts/crosscheck_lrat.sh
# Standing-gate visibility (no scheduler on this host by design; the gates
# run inline in every release build, and on demand via nightly_gates.sh).
# This reports the last bundle run's verdict and age so staleness is seen at
# the natural checkpoint instead of silently accumulating.
latest_gates=$(ls -dt .lake/release-metrics/nightly-*/gates.csv 2>/dev/null | head -1)
if [[ -n "$latest_gates" ]]; then
  age_days=$(( ($(date +%s) - $(stat -c %Y "$latest_gates")) / 86400 ))
  if grep -q FAIL "$latest_gates"; then
    echo "ci: WARNING last gate bundle ($latest_gates, ${age_days}d old) has FAILING rows"
  else
    echo "ci: last gate bundle all-PASS ($latest_gates, ${age_days}d old)"
  fi
else
  echo "ci: NOTE no gate-bundle run recorded (scripts/nightly_gates.sh)"
fi
echo "ci: OK"
