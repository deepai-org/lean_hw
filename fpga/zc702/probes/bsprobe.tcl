# bsprobe.tcl -- byte-store placement probe on silicon.
#
# One question: when the mini executes `sb`, do consecutive byte stores land
# PACKED in DDR, or one-per-64-bit-word?
#
# The guest's console ring is written by `buf[i] = c` (a byte store) and reads
# back from the board with every character occupying eight bytes, while the
# same image in the emulator produces packed text. subwordselftest and iverilog
# both say the DESIGN merges a byte into its lane correctly, so this asks the
# silicon directly, with no NetBSD in the way.
#
# The program seeds one 64-bit word with a recognisable pattern, then stores
# 'A'..'H' into byte lanes 0..7 of that same word, then EXITs.
#
#   packed (correct) : 0x13200000 = 0x44434241  0x13200004 = 0x48474645
#   one-per-word     : lane 0 holds 'H' (or 'A'), neighbouring words hold the
#                      other characters, i.e. the chars are 8 bytes apart
#
connect -url tcp:127.0.0.1:3121
after 300
set DB 0x10000000
source /home/kevin/substrate0/test/jtag_lib.tcl

# The core fetches from DDR (ddrPc = DATA_BASE + pc), so the program goes in
# with gwrite -- the same path the rump servicer's %INITMEM uses -- NOT with
# loadw (regs 10/11/12), which targets an IMEM this SoC does not fetch from and
# leaves the core running with retire=0 and pc pinned at TEXT_BASE.
wr 13 1
after 50

# Prove the write path works before trusting anything it reports.
gwrite 0x3200000 0xCAFEBABE 0x12345678
after 20
wr 40 0x13200000; after 5; wr 43 1; after 30
puts [format "PROBE: gwrite check 0x13200000 = 0x%08X%08X (want 0xCAFEBABE12345678)" [rd 46] [rd 45]]

set fh [open /home/kevin/bsprobe_words.txt r]
set i 0
foreach line [split [read $fh] "\n"] {
  set line [string trim $line]
  if {$line eq ""} continue
  set w [expr 0x$line]
  gwrite [expr {0x1000 + $i*8}] [expr {($w>>32)&0xffffffff}] [expr {$w & 0xffffffff}]
  incr i
}
close $fh
puts "PROBE: wrote $i program words to guest 0x1000"

gwrite 0x3200000 0 0
gwrite 0x3200008 0 0

wr 13 2
set halted 0
for {set k 0} {$k < 300} {incr k} {
  after 100
  set s [rd 20]
  if {($s>>1)&1} { set halted 1; break }
  if {$k % 100 == 0} { puts [format "  ...t=%ds status=0x%x retire=%d pc=0x%x" [expr {$k/10}] $s [rd 21] [rd 22]] }
}
puts [format "PROBE: status=0x%x halted=%d retire=%d pc=0x%x" [rd 20] $halted [rd 21] [rd 22]]

# --- read the target back BOTH ways
foreach a {0x13200000 0x13200004 0x13200008 0x1320000c 0x13200010} {
  wr 40 $a; after 5; wr 43 1; after 30
  puts [format "MINI-VIEW  %s = 0x%08X%08X" $a [rd 46] [rd 45]]
}
targets -set -filter {name =~ {*Cortex-A9*#0*}}
puts "DAP-VIEW   [mrd -force 0x13200000 6]"
puts "PROBE_DONE"
