#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# CI = build the standing targets and run the audit/reproduction gates.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Loom Machines Tests iss audit emit bookgen rtlroundtrip
# The Epoch bounded-model-check development is intentionally not imported by
# the default `Machines` umbrella: it is a large proof artifact, not a public
# API dependency. CI still checks it explicitly.
lake build Machines.Epoch.Bmc
lake build Tests.Acc8Bmc
lake build Tests.Lnp64uWitnesses
scripts/downstream_smoke.sh
lake exe audit
lake exe bookgen >/dev/null
lake exe emit acc8 >/dev/null
lake exe emit lnp64u >/dev/null
scripts/check_xfree_rtl.py rtl/acc8.v rtl/lnp64u.v
scripts/debugmap.sh
# The round trip on the emitted *files*: every rtl/*.v parses and reprints
# byte-identically (skips are printed with their reason).
lake exe rtlroundtrip rtl/*.v
scripts/test_release_binding.py
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
echo "ci: RESULT PASS"
