#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "$0")/.."

# This is deliberately evidence-layer corroboration with an accessible generic
# synthesis tool. It is not part of Loom's semantics, compiler theorem, or TCB.
if ! command -v yosys >/dev/null 2>&1; then
  echo "multiclock-synthesis: RESULT SKIP (yosys not installed)"
  exit 0
fi

work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT

lake exe emitCertifiedMulticlock
yosys -q -l "$work_dir/yosys.log" -p \
  "read_verilog -sv rtl/certified_multiclock/system.v; hierarchy -check -top loom_system; proc; opt; check; synth -top loom_system; check"

echo "multiclock-synthesis: RESULT PASS (technology-neutral RTL accepted and synthesized)"
