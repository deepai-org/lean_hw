#!/bin/bash
# Boot the accounted SMP image (text c4cf0f96) on the CAUSE-LATCH bitstream and
# read the new generated debug map. Event-driven (no mid-JTAG kills).
# NEW READ MAP (DebugMap-generated; replaces the hand map):
#   47 trace_pc_lo  48 trace_wb_lo (wr 69 <i> selects ring entry)
#   49/50 gret_noop_pc  51 gret_noop_cur  52 gret_noop_cnt  53 gret_noop_trapped
#   54 running_and_halted (sticky)  55/56 ig_fall_pc  57 ig_fall_info
#   ig_fall_info = {15:valid, 13:9 free_slot, 8:4 cur, 3:retlast, 2:exit, 1:clone, 0:gatecall}
set -u
cd /home/kevin/substrate0
export PATH=/opt/Xilinx/2025.2/Vivado/bin:$PATH
export LNP64_MINI_GATE_TBL=0x913000 LNP64_MINI_CAP_TBL=0x913100
export LNP64_CORE1_ENTRY=0x8cae00 LNP64_CORE1_STACK=0x1700000

touch /tmp/stop_servicer; sleep 10; pkill -x xsdb 2>/dev/null; sleep 5; pkill -9 -x xsdb 2>/dev/null; sleep 3
rm -f /tmp/stop_servicer /home/kevin/smp_servicer.log
echo "=== image md5 (want a23acd8e) ==="; md5sum test/rump_shmif_telnet_text.hex | cut -c1-12
echo "=== bit timestamp ==="; ls -l oxc7/out/lnp64mini_dual_top.bit | awk '{print $6,$7,$8}'

echo "=== zero console ring ==="
timeout 180 xsdb -eval '
  connect -url tcp:127.0.0.1:3121; after 400; targets -set -filter {name =~ "xc7z*"};
  source test/jtag_lib.tcl; set DB 0x10000000;
  for {set off 0} {$off < 0x1000} {incr off 8} { gwrite [expr {0x03000000+$off}] 0 0 }
  puts "console zeroed"
' 2>&1 | grep -a "console zeroed" || echo "WARN: zeroing did not confirm"
sleep 2

( test/boot_gem_dual_smp.sh > /home/kevin/boot_igfall.log 2>&1 ) &

echo "=== phase 1: wait for %READY (fastload ~12s, BSCAN delta minutes) ==="
for i in $(seq 1 60); do
  sleep 15
  L=$(grep -aE "DELTA|LOADPATH|READY|DOMAINS" /home/kevin/smp_servicer.log 2>/dev/null | tail -1)
  echo "[t=$((i*15))s] $L"
  grep -qa "%READY" /home/kevin/smp_servicer.log 2>/dev/null && break
done
echo "=== phase 2: wait for DOMAINS ==="
for i in $(seq 1 16); do
  sleep 15
  grep -qaE "DOMAINS: core0 cap_tbl_base" /home/kevin/smp_servicer.log 2>/dev/null && { echo "DOMAINS @ ${i}x15s"; break; }
done
echo "=== phase 3: settle 150s (the drvspawn stall window; latch fires in it) ==="
sleep 150
grep -aE "DOMAINS|CORE1|HWTRAP|panic" /home/kevin/smp_servicer.log 2>/dev/null | tail -5

echo "=== phase 4: graceful stop, read console + latches ==="
touch /tmp/stop_servicer
for i in $(seq 1 12); do
  sleep 10
  grep -qa "STOPPED" /home/kevin/smp_servicer.log 2>/dev/null && { echo "servicer stopped cleanly"; break; }
  pgrep -x xsdb >/dev/null || { echo "xsdb exited"; break; }
done
pgrep -x xsdb >/dev/null && { echo "WARN: grace expired; killing"; pkill -x xsdb; sleep 5; }
sleep 2
timeout 90 xsdb -eval '
  connect -url tcp:127.0.0.1:3121; after 400; targets -set -filter {name =~ "xc7z*"};
  source test/jtag_lib.tcl; set DB 0x10000000;
  set s {}; foreach w [bulk_gread 0x03000008 128] { for {set k 0} {$k<8} {incr k} { set c [expr {($w>>($k*8))&0xff}]; if {$c>=32 && $c<127} {append s [format %c $c]} elseif {$c==10} {append s " | "} } }
  puts "CONSOLE: $s"
  set nplo [rd 49]; set nphi [rd 50]; set ncur [rd 51]; set ncnt [rd 52]; set ntr [rd 53]
  puts [format "GRET_NOOP cnt=%d pc=0x%08x%08x cur=%d trapped=%d" $ncnt $nphi $nplo $ncur $ntr]
  set fplo [rd 55]; set fphi [rd 56]; set inf [rd 57]
  puts [format "IG_FALL pc=0x%08x%08x info=0x%04x" $fphi $fplo $inf]
  puts [format "  valid=%d free_slot=%d cur=%d retlast=%d exit=%d clone=%d gatecall=%d" \
    [expr {($inf>>15)&1}] [expr {($inf>>9)&0x1f}] [expr {($inf>>4)&0x1f}] \
    [expr {($inf>>3)&1}] [expr {($inf>>2)&1}] [expr {($inf>>1)&1}] [expr {$inf&1}]]
  puts [format "RUN_AND_HALT sticky=0x%08x" [rd 54]]
' 2>&1 | grep -aE "CONSOLE|GRET_NOOP|IG_FALL|valid=|RUN_AND_HALT"
