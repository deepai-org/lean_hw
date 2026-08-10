source [file join [file dirname [info script]] board_env.tcl]
source $LOOM_JTAG_LIB
connect
targets -set -filter {name =~ "xc7z*"}
# re-arm: hold the core in reset, release, let it re-run K cycles (4 ms)
wr 3 1
puts "MIDRESET_CYC=[rd 81]"
wr 3 0
after 500
foreach {n a} {cyc 81 injected 82 serviced 83 err 84 maxout 85 dma_sub 86 dma_comp 87 tmr_exp 88 lfsr 90 tmr 92 pending 94} { puts "$n=[rd $a]" }
for {set i 0} {$i<8} {incr i} { puts "age$i=[rd [expr {100+$i}]]" }
puts "REARM_DONE"
