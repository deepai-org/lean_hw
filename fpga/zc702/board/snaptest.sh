#!/bin/bash
# snaptest.sh -- the on-silicon proof for Loom.Hw.CdcSnapshot: on a running,
# servicer-detached core, HOLD_OK checks that one debug_capture holds the
# trace-PC snapshot constant across 4 reads while the live source moves under
# us (coherence, holdStable), and ADVANCE_OK checks that 8 fresh captures show
# the source genuinely running (>1 distinct PC). Together they witness the
# snapshot crossing is coherent-not-torn on the board. Synced by board_sync.
set -u
cd /home/kevin/substrate0
export PATH=/opt/Xilinx/2025.2/Vivado/bin:$PATH
export LNP64_MINI_GATE_TBL=0x913000 LNP64_MINI_CAP_TBL=0x913100
export LNP64_CORE1_ENTRY=0x8cae00 LNP64_CORE1_STACK=0x1700000
touch /tmp/stop_servicer; pkill -x xsdb 2>/dev/null; sleep 4
rm -f /tmp/stop_servicer /home/kevin/smp_servicer.log
( test/boot_gem_dual_smp.sh > /home/kevin/boot_snap.log 2>&1 ) &
for i in $(seq 1 20); do sleep 15; grep -qa "DOMAINS: core0 cap_tbl_base" /home/kevin/smp_servicer.log 2>/dev/null && break; done
echo "=== domains reached; let core run 20s ==="; sleep 20
# stop servicer; core keeps running autonomously in the fabric
touch /tmp/stop_servicer; sleep 3; pkill -9 -x xsdb 2>/dev/null; sleep 3
timeout 90 xsdb -eval '
  connect -url tcp:127.0.0.1:3121; after 400; targets -set -filter {name =~ "xc7z*"};
  source test/jtag_lib.tcl; source test/lnp64mini_debug_map.tcl
  puts [format "core: status=0x%x pc=0x%08x" [rd 20] [rd 22]]
  wr 69 15
  # HOLD: capture once, then read 4x with NO capture -- must all match while
  # the live source is moving under us.
  debug_capture
  set held {}
  for {set i 0} {$i < 4} {incr i} { lappend held [debug_trace_rd_pc_lo]; after 60 }
  set allsame 1; foreach v $held { if {$v != [lindex $held 0]} {set allsame 0} }
  puts "HELD reads: $held"
  puts "HOLD_OK=$allsame (want 1: snapshot constant while source moves)"
  # ADVANCE: 8 fresh captures -- must show >1 distinct value (source is running)
  set caps {}
  for {set i 0} {$i < 8} {incr i} { debug_capture; lappend caps [debug_trace_rd_pc_lo]; after 40 }
  set uniq [lsort -unique $caps]
  puts "CAPTURED: $caps"
  puts "ADVANCE_OK=[expr {[llength $uniq] > 1}] (distinct=[llength $uniq], want >1)"
' 2>&1 | grep -aE "core:|HELD|HOLD_OK|CAPTURED|ADVANCE_OK"
