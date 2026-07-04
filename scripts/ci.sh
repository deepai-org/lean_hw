#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# CI = build everything + the audit gate (PLAN §10).
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Loom Machines Tests iss audit emit bookgen
lake build Tests.Acc8Bmc
lake build Tests.Lnp64uWitnesses
lake exe audit
lake exe bookgen >/dev/null
lake exe emit acc8 >/dev/null
lake exe emit lnp64u >/dev/null
scripts/check_xfree_rtl.py rtl/acc8.v rtl/lnp64u.v
# Independent-checker cross-validation (self-SKIPs if cadical/python3 absent,
# so CI does not depend on a SAT solver being installed).
scripts/crosscheck_lrat.sh
echo "ci: OK"
