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
export PATH=/opt/Xilinx/2025.2/Vivado/bin:$PATH
cd /home/kevin/substrate0
mkdir -p /tmp/rumpns /tmp/rumpns2
pkill -x xsdb 2>/dev/null; pkill -f "lnp64 trap-server" 2>/dev/null
pkill -f "[r]ing_pump" 2>/dev/null
sleep 3
echo "== program dual bitstream =="
timeout 300 xsdb -eval "connect -url tcp:127.0.0.1:3121; after 300; targets -set -filter {name =~ \"xc7z*\"}; fpga -file /home/kevin/substrate0/oxc7/out/lnp64mini_epoch_top.bit; puts PROGRAMMED" > /home/kevin/dual_fpga.log 2>&1
grep -q PROGRAMMED /home/kevin/dual_fpga.log || { echo "FPGA PROGRAM FAILED"; exit 1; }
rm -f /tmp/stop_servicer
date +%s > /tmp/rump_start
echo "== PS-DAP fastload =="
export LNP64_FASTLOADED=0
if timeout 300 xsdb test/fastload.tcl > /home/kevin/dual_fastload.log 2>&1 && grep -q FASTLOAD_DONE /home/kevin/dual_fastload.log; then
  export LNP64_FASTLOADED=1
else
  echo "fastload failed; BSCAN path will handle it" >> /home/kevin/dual_fastload.log
fi
echo "== dual-core servicer (core1 entry=${LNP64_CORE1_ENTRY:-unset}) =="
export LNP64_CORE1_ENTRY="${LNP64_CORE1_ENTRY:-0}"
export LNP64_CORE1_STACK="${LNP64_CORE1_STACK:-0x01700000}"
timeout 14400 xsdb test/lnp64_rump_run_dual.tcl > /home/kevin/smp_servicer.log 2>&1
