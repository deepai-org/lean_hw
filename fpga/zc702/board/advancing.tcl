# Is core0 still advancing (spinning in-fabric) or halted? Read the core0 trace
# ring + regfile-ish state twice, ~4s apart. Changing trace PCs => core0 is
# retiring instructions autonomously (guest-side spin); identical => frozen.
connect -url tcp:127.0.0.1:3121
after 400
targets -set -filter {name =~ "xc7z*"}
source [file join [file dirname [info script]] board_env.tcl]
source $LOOM_JTAG_LIB

proc ring {} {
  set out ""
  for {set i 0} {$i < 16} {incr i} { wr 69 $i; after 1; append out [format "%08x " [rd 47]] }
  return $out
}
puts "status(rd20)=0x[format %08x [rd 20]]  s_pc(rd22)=0x[format %08x [rd 22]]"
set a [ring]
after 4000
set b [ring]
puts "ring_A: $a"
puts "ring_B: $b"
if {$a eq $b} { puts ">>> CORE0 FROZEN (ring identical over 4s) -- halted/blocked on a trap" } \
else { puts ">>> CORE0 ADVANCING (ring changed) -- spinning in-fabric, guest-side deadlock" }
puts "status2(rd20)=0x[format %08x [rd 20]]  s_pc2(rd22)=0x[format %08x [rd 22]]"
