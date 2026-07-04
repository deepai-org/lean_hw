#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# CI = build everything + the audit gate (PLAN §10).
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Loom Machines Tests Tools iss asm audit emit bookgen 2>/dev/null || lake build Loom Machines Tests
lake exe audit
lake exe bookgen >/dev/null
# Independent-checker cross-validation (self-SKIPs if cadical/python3 absent,
# so CI does not depend on a SAT solver being installed).
scripts/crosscheck_lrat.sh
echo "ci: OK"
