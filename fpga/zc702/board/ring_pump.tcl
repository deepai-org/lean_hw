# ring_pump.tcl -- DEDICATED shmif ring R/W pump (separate xsdb from the trap
# servicer). Rationale: Tcl socket code inside the trap-servicing xsdb wedged
# its interpreter twice (brk storm on a giant R; futex storm at first ring op).
# This process does ONLY: bridge socket line -> JTAG DDR op -> response.
# Blocking I/O, restart-safe. Launched by e2e.sh (and netbsd_up.sh) after the
# servicer's bridge socket (9099) is open; it retries the connect until then.
# Shares the JTAG with the servicer through the hardware bus arbiter
# (wr 55 = request, rd 20 bit 3 = grant), so two xsdb can drive one TAP.
set RING 0x20e000
set DB   0x10000000
connect -url tcp:127.0.0.1:3121
after 300
source [file join [file dirname [info script]] jtag_lib.tcl]
proc bus_acquire {} {
  wr 55 1
  for {set i 0} {$i<200} {incr i} { if {([rd 20]>>3)&1} return }
}
proc bus_release {} { wr 55 0 }

while {1} {
  if {[catch {socket 127.0.0.1 9099} sk]} { after 1000; continue }
  fconfigure $sk -buffering line -blocking 1 -translation lf
  puts "PUMP: connected"; flush stdout
  while {1} {
    if {[catch {gets $sk line} n] || $n < 0} break
    set f [split $line]
    switch -- [lindex $f 0] {
      R { set off [lindex $f 1]; set nw [lindex $f 2]
          if {$nw <= 0 || $nw > 4096} { puts $sk "D"; continue }
          bus_acquire
          set out {}
          foreach w [bulk_gread [expr {$RING+$off}] $nw] { lappend out [format %016x $w] }
          bus_release
          puts $sk "D [join $out { }]" }
      W { set off [lindex $f 1]; set tri {}; set ga [expr {$RING+$off}]
          foreach hx [lrange $f 2 end] { set v [expr 0x$hx]
            lappend tri $ga [expr {($v>>32)&0xffffffff}] [expr {$v&0xffffffff}]; incr ga 8 }
          bus_acquire; bulk_write $tri 0x10000000; bus_release }
      default {}
    }
  }
  catch {close $sk}
  puts "PUMP: socket lost; retrying"; flush stdout
  after 1000
}
