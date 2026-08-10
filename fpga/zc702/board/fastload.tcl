# fastload.tcl -- load the rump image into DDR via the PS DAP (A9 `dow`),
# ~12 s for the whole image vs ~17 min over BSCAN (measured 491 KB/s, and the
# mini3 HP view sees the words bit-exactly).
#
# Requirements: ps7_init has run ONCE this power-on (ddr_bringup.tcl /
# power_cycle.sh), the PL was just reprogrammed (old core stopped -- never
# overwrite a live core's text), bins staged by dev_cycle next to the hexes.
# The servicer tcl still spot-verifies text AND data before trusting this:
# a dead/uninitialized DAP just fails verification and the BSCAN full-load
# path runs instead -- fastload is an accelerator, not a correctness gate.
source [file join [file dirname [info script]] board_env.tcl]
set TESTD $LOOM_TEST_DIR
set HEX     $TESTD/rump_shmif_telnet_text.hex
set TEXTBIN $TESTD/rump_shmif_telnet_text.bin
set DATABIN $TESTD/rump_shmif_telnet_data.bin
set DB   0x10000000
set RING 0x20e000

# geometry from the hex header (# entry / text-base / data-base / data-len)
set tbase 0; set dbase 0; set dlen 0
set fh [open $HEX]
foreach line [split [read $fh] "\n"] {
  set line [string trim $line]
  if {[string index $line 0] ne "#"} break
  set p [lrange [split $line] 1 end]
  switch -- [lindex $p 0] {
    text-base { set tbase [expr [lindex $p 1]] }
    data-base { set dbase [expr [lindex $p 1]] }
    data-len  { set dlen  [expr [lindex $p 1]] }
  }
}
close $fh
if {$tbase == 0 || $dbase == 0 || $dlen == 0} { puts "FASTLOAD_FAIL: bad hex header"; exit 1 }

connect -url tcp:127.0.0.1:3121
after 200
targets -set -filter {name =~ {*Cortex-A9*#0*}}
catch {stop}
set t0 [clock milliseconds]
# EXT-7 stage B (LNP64_RELOC=1): the data/bss span lives at physical +0x800000.
# This is the PS-DAP half of the same map gphys implements on the BSCAN side
# and install_vma_reloc installs in the cores; three implementations of one
# constant, and the servicer's data spot-verify (which reads through gphys) is
# what catches them disagreeing -- a fastload that wrote data at the identity
# address under RELOC fails the spot-verify and falls back to the BSCAN load,
# loudly, instead of booting a guest whose data is somewhere else.
set DDELTA 0
if {[info exists ::env(LNP64_RELOC)] && $::env(LNP64_RELOC) == 1} {
  set DDELTA 0x800000
  puts [format "FASTLOAD: stage-B reloc, data at physical +0x%x" $DDELTA]
}
# ring header (4KB) -- an empty bus needs only first/last/gen/lock zeroed.
# The ring is a pinned carve-out (delta 0) in every mode.
mwr -force [expr {$DB+$RING}] 0 1024
# bss+data span zeroed, then the data image over the front of it
mwr -force [expr {$DB+$dbase+$DDELTA}] 0 [expr {$dlen/4}]
dow -data $DATABIN [expr {$DB+$dbase+$DDELTA}]
dow -data $TEXTBIN [expr {$DB+$tbase}]
set t1 [clock milliseconds]
# record: DDR now holds exactly this hex (servicer's PRELOADED path verifies)
if {![catch {exec md5sum $HEX} m]} {
  set mfh [open /tmp/lnp64_text_loaded.md5 w]; puts $mfh [lindex $m 0]; close $mfh
  catch {file copy -force $HEX /tmp/lnp64_text_loaded.hex}
}
puts [format "FASTLOAD_DONE in %d ms (text+data+zeroing via PS DAP)" [expr {$t1-$t0}]]
