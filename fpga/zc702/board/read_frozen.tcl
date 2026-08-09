# Read the frozen latch-bit board: loud-latch, core0 status, trace ring (last 16
# retired PCs), core0 register file. Zero boot attempts -- pure BSCAN snapshot.
connect -url tcp:127.0.0.1:3121
after 400
targets -set -filter {name =~ "xc7z*"}
source /home/kevin/substrate0/test/jtag_lib.tcl

puts "==== LOUD-LATCH (core0) ===="
set cnt [rd 49]; set plo [rd 50]; set phi [rd 51]; set ght [rd 52]; set tc [rd 53]
puts [format "gret_noop_cnt=%d  pc=0x%08x%08x  gate_had_trap=0x%08x  trapped=%d  cur=%d" \
  $cnt $phi $plo $ght [expr {($tc>>5)&1}] [expr {$tc & 0x1f}]]

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
