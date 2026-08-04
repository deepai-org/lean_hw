# bsprobe.tcl -- byte-store placement probe on silicon.
#
# One question: when the mini executes `sb`, do consecutive byte stores land
# PACKED in DDR, or one character per 64-bit word?
#
# The guest's console ring is written by `buf[i] = c` (a byte store). It reads
# back from the board with every character occupying eight bytes, while the
# SAME image in the emulator produces packed text. `subwordselftest` and
# iverilog both say the DESIGN merges a byte into its lane correctly, so this
# asks the silicon directly, with no NetBSD in the way.
#
# The program seeds one 64-bit word, then stores 'A'..'H' into byte lanes 0..7
# of that word, then EXITs.
#
#   packed (correct) : 0x13200000 = 0x4847464544434241
#   one-per-word     : the characters land 8 bytes apart
#
# Writes go through bulk_write_v, NOT the bare `gwrite` helper. Two details in
# jtag_lib.tcl's bulk_write are load-bearing and gwrite has neither, which is
# why a standalone gwrite reads back unchanged:
#   * register 40 takes `addr - 8` -- the auto-increment bitstream latches the
#     address post-increment;
#   * each word needs an idle dwell or the HP write is dropped.
# bulk_write_v also reads back and re-writes dropped words, which its own
# comment says is needed because ~30% of raw loads otherwise corrupt the image.
#
connect -url tcp:127.0.0.1:3121
after 300
set DB 0x10000000
set LOADOK 1
source /home/kevin/substrate0/test/jtag_lib.tcl

wr 13 1
after 50

# --- prove the write path before trusting anything it reports
bulk_write_v [list 0x3200000 0xCAFEBABE 0x12345678] $DB 64
set chk [bulk_gread 0x3200000 1 64]
puts [format "PROBE: write-path check = 0x%016X (want 0xCAFEBABE12345678)" [lindex $chk 0]]

# --- load the program at guest 0x1000 (TEXT_BASE); the core fetches from DDR
set triples {}
set fh [open /home/kevin/bsprobe_words.txt r]
set i 0
foreach line [split [read $fh] "\n"] {
  set line [string trim $line]
  if {$line eq ""} continue
  set w [expr 0x$line]
  lappend triples [expr {0x1000 + $i*8}] [expr {($w>>32)&0xffffffff}] [expr {$w & 0xffffffff}]
  incr i
}
close $fh
bulk_write_v $triples $DB 64
puts "PROBE: loaded $i program words at guest 0x1000 (LOADOK=$LOADOK)"

# --- clear the target so a stale value cannot be mistaken for a result
bulk_write_v [list 0x3200000 0 0 0x3200008 0 0] $DB 64

# --- run
wr 13 2
set halted 0
for {set k 0} {$k < 300} {incr k} {
  after 100
  set s [rd 20]
  if {($s>>1)&1} { set halted 1; break }
  if {$k % 100 == 0} {
    puts [format "  ...t=%ds status=0x%x retire=%d pc=0x%x" [expr {$k/10}] $s [rd 21] [rd 22]]
  }
}
puts [format "PROBE: status=0x%x halted=%d retire=%d pc=0x%x" [rd 20] $halted [rd 21] [rd 22]]

# --- read the result back through the mini's own port and the PS DAP
set res [bulk_gread 0x3200000 2 64]
puts [format "MINI-VIEW  0x13200000 = 0x%016X" [lindex $res 0]]
puts [format "MINI-VIEW  0x13200008 = 0x%016X" [lindex $res 1]]
targets -set -filter {name =~ {*Cortex-A9*#0*}}
puts "DAP-VIEW   [mrd -force 0x13200000 4]"
puts "VERDICT: packed if 0x13200000 = 0x4847464544434241"
puts "PROBE_DONE"
