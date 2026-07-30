# loom_s0bscan_accept.tcl -- run the S0BscanRegs acceptance trace on the
# ZC702 over the jtag_lib.tcl protocol and print each response, in the same
# "k rd_reg=<dec>" format as `Emit.lean predict-s0bscan` (step 3, the
# heartbeat read, is dynamic on silicon: printed as HB and checked ticking).
source /home/kevin/substrate0/test/jtag_lib.tcl
connect
targets -set -filter {name =~ "xc7z*"}
fpga -file /home/kevin/substrate0/oxc7/out/s0bscan_top.bit
after 2000

set k 0
proc chk {v} { global k; puts "$k rd_reg=$v"; incr k }

chk [rd 0]                                   ;# 0 ID
wr 1 0x1EAD5E13; chk 0                       ;# 1 write scratch (no readback slot)
chk [rd 1]                                   ;# 2 scratch
set hb1 [rd 2]; puts "$k HB=$hb1"; incr k    ;# 3 heartbeat (dynamic)
wr 3 0xA; chk 0                              ;# 4 write LED
chk [rd 3]                                   ;# 5 LED
for {set i 0} {$i < 21} {incr i} { chk [rd 5] }   ;# 6..26 banner drain
chk [rd 4]                                   ;# 27 remaining (0)
wr 4 0; chk 0                                ;# 28 re-arm
chk [rd 4]                                   ;# 29 remaining (19)
wr 0x85 0xB00051E5; chk 0                    ;# 30 BRAM[5] write
chk [rd 0x85]                                ;# 31 BRAM[5]
puts "$k rd_reg=idle"; incr k                ;# 32 idle
set hb2 [rd 2]
puts "HB_TICKING=[expr {$hb2 != $hb1}]"
puts "ACCEPT_DONE"
