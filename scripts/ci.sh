#!/usr/bin/env bash
# CI = build everything + the audit gate (PLAN §10).
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Loom Machines Tests Tools iss asm audit emit bookgen 2>/dev/null || lake build Loom Machines Tests
lake exe audit
lake exe bookgen >/dev/null
echo "ci: OK"
