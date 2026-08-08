# epoch_bump_demo.tcl -- Goal 4 on silicon: revocation is a §3 epoch bump.
# Runs on the EPOCH TOP bit (core + fabric epoch engine at 0x0A0E0000) via
# BSCAN; no NetBSD boot needed. A program presents epoch 1 (the reset epoch)
# and CHECKs it -> OK; then BUMPs the cell (the §3 bump); then re-presents the
# SAME epoch 1 and CHECKs -> STALE. The engine owns the cell; software only
# presents a handle, so the bump -- not a host poke -- is what revokes.
source /home/kevin/substrate0/test/jtag_lib.tcl
connect
targets -set -filter {name =~ "xc7z*"}
set DB 0x10000000
puts "ID=[format 0x%08x [rd 0]]"
proc wd {addr hi lo} { wr 40 [expr {$addr-8}]; wr 41 $lo; wr 42 $hi }
proc load_prog {} {
  wd 0x10001000 0x48080283 0x80000000
  wd 0x10001008 0x48180000 0x00000000
  wd 0x10001010 0x48200000 0x00004000
  wd 0x10001018 0x48280000 0x0001c000
  wd 0x10001020 0x75104000 0x00070000
  wd 0x10001028 0x79004600 0x00000000
  wd 0x10001030 0x79004800 0x00000800
  wd 0x10001038 0x79004a00 0x00001000
  wd 0x10001040 0x79004600 0x00001800
  wd 0x10001048 0x75304000 0x00040000
  wd 0x10001050 0x79004600 0x00002800
  wd 0x10001058 0x75384000 0x00060000
  wd 0x10001060 0x79004800 0x00000800
  wd 0x10001068 0x79004600 0x00001800
  wd 0x10001070 0x75404000 0x00040000
  wd 0x10001078 0xfc000000 0x00000000
}
wr 13 1 ; after 300
load_prog
wr 53 0x1000
wr 13 2 ; after 1500
set id [regv 2]; set r6 [regv 6]; set lat [regv 7]; set r8 [regv 8]
puts [format "engine ID   r2=0x%x (want 0xe90c0001)" $id]
puts [format "check BEFORE bump r6=0x%x  (0x100 = valid|OK)" $r6]
puts [format "bump latency     r7=%d cycles" $lat]
puts [format "check AFTER bump  r8=0x%x  (0x103 = valid|STALE)" $r8]
if {$id == 0xe90c0001 && ($r6 & 0xff) == 0 && ($r8 & 0xff) == 3} {
  puts "EPOCH_REVOKE_OK: the same reference checked OK, then a §3 bump made it STALE"
} else {
  puts "EPOCH_REVOKE_FAIL: id=$id before=$r6 after=$r8"
}
