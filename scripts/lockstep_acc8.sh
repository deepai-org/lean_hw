#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Corroborate the emitted Acc8 µVerilog against the ISS golden (task 2.6,
# pathfinder). Emits, simulates with iverilog, and checks the final state.
set -euo pipefail
cd "$(dirname "$0")/.."
lake exe emit >/dev/null
iverilog -g2012 -o rtl/acc8.vvp rtl/acc8.v rtl/tb_acc8.v
OUT=$(vvp rtl/acc8.vvp | grep '^acc=')
echo "RTL: $OUT"
EXPECT="acc=40 pc=4 halted=1 mem3=40"
if [ "$OUT" = "$EXPECT" ]; then
  echo "lockstep_acc8: OK (RTL matches ISS golden)"
else
  echo "lockstep_acc8: DIVERGENCE — expected '$EXPECT'"; exit 1
fi
