#!/bin/bash
# e2e.sh -- the full NetBSD-on-fabric demo, end to end, as a single regression:
# power-cycle -> verify image md5 (a5b8afb3) + bit -> boot the dual core ->
# wait for DOMAINS -> let rump+shmif settle -> ping over GEM0 -> telnet
# `uname` + `echo` back through the §17 write gate. A pass proves boot,
# domains, the shmif driver in domain 2, and gated syscall replies all survive
# the current bitstream together. Deployed to substrate0/test/ by board_sync.
set -u
cd /home/kevin/substrate0
export PATH=/opt/Xilinx/2025.2/Vivado/bin:$PATH
export LNP64_MINI_GATE_TBL=0x913000 LNP64_MINI_CAP_TBL=0x913100
export LNP64_CORE1_ENTRY=0x8cae00 LNP64_CORE1_STACK=0x1700000
echo "=== power cycle for a clean path ==="
bash test/power_cycle.sh 2>&1 | tail -2
sleep 5
echo "=== md5 (want a5b8afb3) + bit ==="; md5sum test/rump_shmif_telnet_text.hex | cut -c1-12; ls -l oxc7/out/lnp64mini_dual_top.bit | awk '{print $6,$7,$8}'
touch /tmp/stop_servicer; pkill -x xsdb 2>/dev/null; sleep 4; rm -f /tmp/stop_servicer /home/kevin/smp_servicer.log
( test/boot_gem_dual_smp.sh > /home/kevin/boot_e2e.log 2>&1 ) &
echo "=== wait for DOMAINS ==="
for i in $(seq 1 20); do sleep 15; grep -qa "DOMAINS: core0 cap_tbl_base" /home/kevin/smp_servicer.log 2>/dev/null && { echo "DOMAINS @ ${i}x15s"; break; }; done
grep -aE "DOMAINS|CORE1|HWTRAP|panic" /home/kevin/smp_servicer.log 2>/dev/null | tail -4
echo "=== let rump + shmif come up (90s) ==="; sleep 90
echo "=== ping over GEM0 ==="; ping -c 4 -W 4 10.106.0.2 2>&1 | tail -2
echo "=== telnet: uname + echo through the write gate ==="
(sleep 8; printf 'uname\r\n'; sleep 24; printf 'echo e2e-ok-through-gate\r\n'; sleep 24) | timeout 100 nc 10.106.0.2 23 2>&1 | tr -d '\0' | grep -aE 'micro-shell|NetBSD|e2e-ok' | head -6
