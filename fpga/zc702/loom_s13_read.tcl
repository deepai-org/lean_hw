# loom_s13_read.tcl -- program the Loom s13soak bitstream, wait for freeze,
# read the full engine state over BSCAN (jtag_lib.tcl rd protocol).
source /home/kevin/substrate0/test/jtag_lib.tcl
connect
targets -set -filter {name =~ "xc7z*"}
fpga -file /home/kevin/substrate0/oxc7/out/s13soak_top.bit
after 2000
puts "ID=[format 0x%08x [rd 0]]"
set hb1 [rd 2]; after 200; set hb2 [rd 2]
puts "HB_TICKING=[expr {$hb2 != $hb1}]"
wr 1 0x1EAD5E13
puts "SCRATCH=[format 0x%08x [rd 1]]"
# engine state (frozen at K)
foreach {n a} {cyc 81 injected 82 serviced 83 err 84 maxout 85 dma_sub 86 dma_comp 87 tmr_exp 88 lfsr 90 ptr 91 tmr 92 dmacd_busy 93 pending 94} {
  puts "$n=[rd $a]"
}
for {set i 0} {$i<8} {incr i} { puts "age$i=[rd [expr {100+$i}]]" }
puts "READ_DONE"
