# Read the frozen board: §9.2/op-0 fault record, core0 status, trace ring (last
# 16 retired PCs), core0 register file. Zero boot attempts -- pure BSCAN snapshot.
#
# The fault quartet decode is NOT hand-maintained here: it is sourced from the
# generated lnp64mini_debug_map.tcl (produced by Loom.Hw.DebugMap, --check
# guarded), so index drift can never silently mislabel a register the way the
# retired gret_noop/ig_fall latch layout once did. That file also carries the
# debug_capture (cmd 76) coherence latch, so the reads below are snapshot-
# coherent rather than torn live values (Loom.Hw.Cdc.holdStable).
connect -url tcp:127.0.0.1:3121
after 400
targets -set -filter {name =~ "xc7z*"}
source [file join [file dirname [info script]] board_env.tcl]
source $LOOM_JTAG_LIB
source $LOOM_DEBUG_MAP

puts "==== FAULT RECORD (core0, §9.2/op-0 -- 0 = clean) ===="
debug_capture
puts [format "fault_pc=0x%016x  fault_cause=0x%02x  fault_cur=%d" \
  [debug_fault_pc] [debug_fault_cause] [debug_fault_cur]]

puts "==== CORE0 STATUS ===="
puts [format "status(rd20)=0x%08x  s_pc(rd22)=0x%08x  s_rt(rd21)=0x%08x" [rd 20] [rd 22] [rd 21]]

puts "==== CORE0 TRACE RING (last 16 retired PCs; entry 15 = most recent-ish) ===="
for {set i 0} {$i < 16} {incr i} {
  wr 69 $i; after 2
  set lo [rd 47]; set hi [rd 48]
  set op [expr {($hi >> 24) & 0xff}]
  puts [format "  trace\[%2d\] pc=0x%08x op=0x%02x" $i $lo $op]
}

puts "==== CORE0 REGISTER FILE ===="
for {set r 0} {$r < 32} {incr r} {
  set v [regv $r]
  puts [format "  x%-2d = 0x%016x" $r $v]
}
puts "==== DONE ===="
