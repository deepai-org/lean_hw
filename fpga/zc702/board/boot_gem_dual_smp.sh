#!/bin/bash
# boot_gem_dual_smp.sh -- §64 NetBSD + native GEM0 on the DUAL bitstream with
# BOTH cores in the guest kernel.
#
# Differences from boot_gem_dual.sh (which ran NetBSD on core 0 with core 1
# held, running a standalone counter):
#   * the servicer is lnp64_rump_run_dual.tcl -- two trap surfaces, core-1
#     start, per-core retire counters in every progress line;
#   * there is no preload_c1.tcl: core 1 boots the SAME rump image at
#     LNP64_CORE1_ENTRY (nm lnp64_core1_entry) with r31 = LNP64_CORE1_STACK,
#     so both cores execute one kernel out of one DDR image;
#   * CORE1_HOLD is cleared by the servicer, not here.
set -u
source "$(dirname "${BASH_SOURCE[0]}")/board_env.sh"
cd "$LOOM_BOARD_ROOT"
# The §17 gate/cap table roots are the LINKED addresses of lnp64_mini_gate_table
# / lnp64_mini_cap_table -- they SHIFT every image build, so a hardcoded value
# silently reads an empty gate table and every gated write faults -MALFORMED
# (the 2026-08-10 telnet-reply bug). build_rump_shmif_image.py emits them,
# derived by `nm`, into mini_domains.env; it is deployed beside the hex.
# Sourcing it makes the roots ALWAYS match the deployed guest -- never hardcode.
LNP64_IMAGE_ROOTS="${LNP64_IMAGE_ROOTS:-$LOOM_BOARD_TEST_DIR/mini_domains.env}"
if [ -f "$LNP64_IMAGE_ROOTS" ]; then
  # shellcheck disable=SC1090
  source "$LNP64_IMAGE_ROOTS"
  export LNP64_MINI_GATE_TBL LNP64_MINI_CAP_TBL
  echo "== image roots: GATE_TBL=${LNP64_MINI_GATE_TBL:-unset} CAP_TBL=${LNP64_MINI_CAP_TBL:-unset} (from mini_domains.env, nm-derived) =="
else
  echo "== WARN: no mini_domains.env beside the hex; gate/cap roots may be stale (gated writes will -MALFORMED) =="
fi
mkdir -p /tmp/rumpns /tmp/rumpns2
pkill -x xsdb 2>/dev/null; pkill -f "lnp64 trap-server" 2>/dev/null
pkill -f "[r]ing_pump" 2>/dev/null
sleep 3
# The maintained mission workload defaults to the dual top. Override
# `LNP64_BIT` to program another accounted bitstream.
echo "== program dual bitstream =="
FPGA_LOG="$LOOM_BOARD_STATE_DIR/dual_fpga.log"
FASTLOAD_LOG="$LOOM_BOARD_STATE_DIR/dual_fastload.log"
timeout 300 xsdb -eval "connect -url tcp:127.0.0.1:3121; after 300; targets -set -filter {name =~ \"xc7z*\"}; fpga -file ${LNP64_BIT:-$LOOM_OXC7_DIR/out/lnp64mini_dual_top.bit}; puts PROGRAMMED" > "$FPGA_LOG" 2>&1
grep -q PROGRAMMED "$FPGA_LOG" || { echo "FPGA PROGRAM FAILED"; exit 1; }
rm -f "$LOOM_STOP_FILE"
date +%s > /tmp/rump_start
echo "== PS-DAP fastload =="
export LNP64_FASTLOADED=0
if timeout 300 xsdb "$LOOM_BOARD_TEST_DIR/fastload.tcl" > "$FASTLOAD_LOG" 2>&1 && grep -q FASTLOAD_DONE "$FASTLOAD_LOG"; then
  export LNP64_FASTLOADED=1
else
  echo "fastload failed; BSCAN path will handle it" >> "$FASTLOAD_LOG"
fi
echo "== dual-core servicer (core1 entry=${LNP64_CORE1_ENTRY:-unset}) =="
export LNP64_CORE1_ENTRY="${LNP64_CORE1_ENTRY:-0}"
export LNP64_CORE1_STACK="${LNP64_CORE1_STACK:-0x01700000}"
timeout 14400 xsdb "$LOOM_BOARD_TEST_DIR/lnp64_rump_run_dual.tcl" > "$LOOM_SERVICER_LOG" 2>&1
