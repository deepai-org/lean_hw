#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Corroborate the Part-B ergonomics demo (typed Reg/RegArray handles, act!
# notation, balanced Trees builders): emit the RTL, simulate 512 cycles with
# iverilog, and compare the whole register state against the prediction of
# the *verified fast evaluator* running the Lean Design itself.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean --run Machines/Substrate/Emit.lean >/dev/null
lake env lean --run Machines/Substrate/Emit.lean s1check
lake env lean --run Machines/Substrate/Emit.lean s1predict | sort > /tmp/s1_lean.txt
iverilog -g2012 -o rtl/s1counters.vvp rtl/s1counters.v rtl/tb_s1counters.v
vvp rtl/s1counters.vvp | grep '=' | sort > /tmp/s1_rtl.txt
if diff -u /tmp/s1_lean.txt /tmp/s1_rtl.txt; then
  echo "s1counters_demo: OK (iverilog RTL == fastCycle prediction, 512 cycles, 15 regs)"
else
  echo "s1counters_demo: DIVERGENCE"; exit 1
fi
