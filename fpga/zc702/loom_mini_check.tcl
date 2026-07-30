# loom_mini_check.tcl -- loomcheck.s on the Loom-emitted lnp64mini (ZC702).
# Program the bit, load the program over the core's JTAG DDR window, start,
# poll halt, read rf/retire/pc over the mini3-compatible BSCAN map.
source /home/kevin/substrate0/test/jtag_lib.tcl
connect
targets -set -filter {name =~ "xc7z*"}
fpga -file /home/kevin/substrate0/oxc7/out/lnp64mini_top.bit
after 2000
puts "ID=[format 0x%08x [rd 0]]"
set h1 [rd 2]; after 200; set h2 [rd 2]; puts "HB_TICKING=[expr {$h2 != $h1}]"
puts "FCLK_1=[rd 27]"; after 100; puts "FCLK_2=[rd 27]"
# --- load program at DDR 0x10001000 (DATA_BASE + 0x1000) ---
wr 40 [expr {0x10001000 - 8}]; wr 41 0x18000; wr 42 0xa0080000
wr 40 [expr {0x10001008 - 8}]; wr 41 0x1c000; wr 42 0xa0100000
wr 40 [expr {0x10001010 - 8}]; wr 41 0x0; wr 42 0x12184400
wr 40 [expr {0x10001018 - 8}]; wr 41 0x3fc000; wr 42 0xa0200000
wr 40 [expr {0x10001020 - 8}]; wr 41 0x0; wr 42 0x13290400
wr 40 [expr {0x10001028 - 8}]; wr 41 0x0; wr 42 0x1630ca00
wr 40 [expr {0x10001030 - 8}]; wr 41 0x20000; wr 42 0x33000600
wr 40 [expr {0x10001038 - 8}]; wr 41 0x400000; wr 42 0x30380000
wr 40 [expr {0x10001040 - 8}]; wr 41 0x0; wr 42 0x1041cc00
wr 40 [expr {0x10001048 - 8}]; wr 41 0x0; wr 42 0xa0480000
wr 40 [expr {0x10001050 - 8}]; wr 41 0x8000; wr 42 0xa04a4000
wr 40 [expr {0x10001058 - 8}]; wr 41 0xfffffe00; wr 42 0x22024dff
wr 40 [expr {0x10001060 - 8}]; wr 41 0x0; wr 42 0x3a000000
# verify first + last words back
wr 40 0x10001000; wr 43 1; after 10
puts "W0=[format 0x%08x%08x [rd 46] [rd 45]]"
wr 40 [expr {0x10001000 + 8*12}]; wr 43 1; after 10
puts "WLAST=[format 0x%08x%08x [rd 46] [rd 45]]"
# --- reset (zeroing sweep) then start ---
wr 13 1
after 300
wr 13 2
# --- poll for halt (STATUS bit1) ---
for {set i 0} {$i < 100} {incr i} {
  set stx [rd 20]
  if {$stx & 2} break
  after 100
}
puts "STATUS=[format 0x%x [rd 20]]"
puts "RETIRE=[rd 21]"
puts "PC=[rd 22]"
puts "TRAP=[format 0x%x [rd 40]]"
for {set i 1} {$i <= 9} {incr i} {
  wr 14 $i; after 5
  puts "r$i=[expr {([rd 24]<<32) | [rd 23]}]"
}
puts "MINI_CHECK_DONE"
