# smp_sample.tcl -- read the two cores' retire counters / status / pc from a
# SECOND xsdb while the dual servicer holds the primary one.  Touches only
# BSCAN registers (no DDR window, no bus_req), so it cannot disturb either
# core: reads are captures on the wrapper's readback mux.
source /home/kevin/substrate0/test/jtag_lib.tcl
connect -url tcp:127.0.0.1:3121
after 300
proc c1 {i} { return [expr {0x80 | $i}] }
set n 6
if {[info exists ::env(SAMPLES)]} { set n $::env(SAMPLES) }
set gap 5000
if {[info exists ::env(GAPMS)]} { set gap $::env(GAPMS) }
puts [format "ID=0x%08x CORE1_HOLD=%d" [rd 0] [expr {([rd 43]>>5)&1}]]
set p0 -1; set p1 -1
for {set i 0} {$i < $n} {incr i} {
  set r0 [rd 21]; set r1 [rd [c1 21]]
  set s0 [rd 20]; set s1 [rd [c1 20]]
  set d0 "-"; set d1 "-"
  if {$p0 >= 0} { set d0 [expr {$r0-$p0}]; set d1 [expr {$r1-$p1}] }
  puts [format "SAMPLE t=%ds retire0=%u (+%s) retire1=%u (+%s) status0=0x%x status1=0x%x pc0=0x%x pc1=0x%x" \
        [expr {$i*$gap/1000}] $r0 $d0 $r1 $d1 $s0 $s1 [rd 22] [rd [c1 22]]]
  flush stdout
  set p0 $r0; set p1 $r1
  after $gap
}
puts "SAMPLE_DONE"
