#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "$0")/.."

if ! command -v iverilog >/dev/null 2>&1 ||
   ! command -v vvp >/dev/null 2>&1; then
  echo "multiclock-recovery: RESULT SKIP (iverilog/vvp not installed)"
  exit 0
fi

out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT

lake exe emitMulticlockRecoverySmoke "$out"
iverilog -g2012 -s tb_multiclock_recovery -o "$out/test.vvp" \
  "$out/system.v" rtl/tb_multiclock_recovery.v
vvp "$out/test.vvp"
