#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# External-tool corroboration: every shipped design elaborates and
# synthesizes under yosys (read_verilog -sv, hierarchy, proc, opt, synth
# statistics). This is the repeatable form of the one-off three-port
# collision experiment recorded in Loom/Hw/DESIGN.md — an independent
# parser and synthesizer accepting the verified printer's output.
# On-demand; run after `lake exe emit`. Fails on any yosys error.
set -euo pipefail
cd "$(dirname "$0")/.."
command -v yosys >/dev/null || { echo "corroborate_yosys: SKIP (yosys not installed)"; exit 0; }
echo "corroborate_yosys: $(yosys -V)"
status=0
for v in rtl/*.v; do
  case "$v" in rtl/tb_*) continue;; esac
  top=$(basename "$v" .v)
  log=$(mktemp)
  if yosys -p "read_verilog -sv $v; hierarchy -auto-top; proc; opt; stat" >"$log" 2>&1; then
    cells=$( (grep -E "Number of cells:" "$log" || true) | tail -1 | awk '{print $NF}')
    echo "corroborate_yosys: OK $top (cells: ${cells:-?})"
  else
    echo "corroborate_yosys: FAIL $top"
    cat "$log"
    status=1
  fi
  rm -f "$log"
done
exit $status
