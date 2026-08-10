#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Check the generated LNP64mini board-only debug surface. This does not claim
# semantic equivalence: it checks source/artifact freshness and, when Icarus is
# available, elaborates the actual emitted dual + wrapper port integration.
set -euo pipefail
cd "$(dirname "$0")/.."

lake exe debugmap --check

if ! command -v iverilog >/dev/null 2>&1; then
  echo "debugmap: RESULT SKIP wrapper elaboration (map freshness passed; iverilog not installed)"
  exit 0
fi

iverilog -g2012 -i -tnull -s lnp64mini_dual_top \
  -I fpga/zc702 -I fpga/zc702/board \
  rtl/lnp64mini_dual.v fpga/zc702/lnp64mini_dual_top.v
echo "debugmap: OK — Icarus elaborates generated ports + dual board wrapper"

DEBUGMAP_SIM=$(mktemp)
trap 'rm -f "$DEBUGMAP_SIM"' EXIT
iverilog -g2012 -o "$DEBUGMAP_SIM" -s tb_lnp64mini_debug_halt \
  -I fpga/zc702 -I fpga/zc702/board fpga/zc702/tb_lnp64mini_debug_halt.v
DEBUGMAP_RESULT=$(vvp "$DEBUGMAP_SIM")
case "$DEBUGMAP_RESULT" in
  *"debug halt: OK"*) echo "debugmap: OK — $DEBUGMAP_RESULT" ;;
  *) echo "$DEBUGMAP_RESULT"; exit 1 ;;
esac
echo "debugmap: RESULT PASS"
