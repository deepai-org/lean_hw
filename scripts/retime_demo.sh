#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Corroborate the registered-output split (retimeReg) demo: emit the baseline
# and retimed designs plus a combined testbench, simulate with iverilog, and
# assert the retimed `obs` stream is the baseline `obs` stream delayed by
# exactly one cycle (40 cycles). Also runs the EDSL-level self-check.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean --run Machines/Substrate/Emit.lean retime
iverilog -g2012 -o rtl/retime.vvp \
  rtl/retime_base.v rtl/retime_retimed.v rtl/tb_retime.v
OUT=$(vvp rtl/retime.vvp | grep '^retime_demo:')
echo "RTL: $OUT"
if [ "$OUT" = "retime_demo: OK (rt.obs == base.obs delayed 1 cycle, 40 cycles)" ]; then
  echo "retime_demo: OK (iverilog confirms 1-cycle registered-output split)"
else
  echo "retime_demo: DIVERGENCE"; exit 1
fi
