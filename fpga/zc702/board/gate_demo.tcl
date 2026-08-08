# gate_demo.tcl -- Goal 1 on silicon: a program crosses a §17 gate, and the
# zero-descriptor negative test makes that crossing stop (the gate is
# load-bearing). Runs on the loaded dual bit; no NetBSD boot needed.
source /home/kevin/substrate0/test/jtag_lib.tcl
connect
targets -set -filter {name =~ "xc7z*"}
set DB 0x10000000
set GTB 0x2000
puts "ID=[format 0x%08x [rd 0]]"

# DDR word write. The auto-increment latches the POST-increment address, so a
# write lands one word later than the address written -> use addr-8 (matches
# bulk_write / conformance_board.tcl).
proc wd {addr hi lo} { wr 40 [expr {$addr-8}]; wr 41 $lo; wr 42 $hi }

proc load_prog {} {
  wd 0x10001000 0x48500000 0x00004000   ;# r10 = 1 (gate id)
  wd 0x10001008 0xfa028000 0x00000000   ;# GATE_CALL rs1=r10
  wd 0x10001010 0x48300000 0x037bc000   ;# r6 = 0xDEF
  wd 0x10001018 0xfc000000 0x00000000   ;# EXIT
  wd 0x10001020 0x48280000 0x02af0000   ;# handler: r5 = 0xABC
  wd 0x10001028 0xf9000000 0x00000000   ;# GATE_RETURN
}
proc load_desc {flags} {
  wd 0x10002010 0x00000000 0x00001020   ;# gate 1 entry PC = 0x1020
  wd 0x10002018 0x00000000 $flags       ;# gate 1 flags word
}
proc rdw {addr} { return [lindex [bulk_gread [expr {$addr-$::DB}] 1] 0] }
proc run_once {tag} {
  wr 13 1 ; after 300                   ;# reset (pc=TEXT_BASE, rf=0)
  load_prog
  wr 53 0x1000                          ;# start pc = TEXT_BASE
  wr 74 $::GTB                          ;# install gate table root
  wr 13 2 ; after 800                   ;# run
  set r5 [regv 5]; set r6 [regv 6]
  set st [rd 20]; set pc [rd 22]; set ret [rd 21]
  puts [format "%-9s r5=0x%x (0xabc=crossed) r6=0x%x (0xdef=ran) st=0x%x pc=0x%x retire=%d" \
        $tag $r5 $r6 $st $pc $ret]
  return [list $r5 $r6]
}

# sanity: load once, read back the program + descriptor
wr 13 1; after 300; load_prog; load_desc 0x00000101
puts "verify w0=[format 0x%016x [rdw 0x10001000]] (want ...4000) w4=[format 0x%016x [rdw 0x10001020]]"
puts "verify desc.entry=[format 0x%x [rdw 0x10002010]] desc.flags=[format 0x%x [rdw 0x10002018]]"

puts "== POSITIVE: valid gate 1 descriptor =="
load_desc 0x00000101
set pos [run_once "positive"]
puts "== NEGATIVE: zero the descriptor flags (revoke) =="
load_desc 0x00000000
set neg [run_once "negative"]
puts "== RESTORE =="
load_desc 0x00000101
set res [run_once "restored"]

set p5 [lindex $pos 0]; set n5 [lindex $neg 0]; set r5b [lindex $res 0]
if {$p5 == 0xabc && $n5 != 0xabc && $r5b == 0xabc} {
  puts "GATE_LOADBEARING_OK: crossed(0xabc) -> revoked(no cross) -> restored(0xabc)"
} else {
  puts "GATE_LOADBEARING_FAIL: pos=$p5 neg=$n5 res=$r5b"
}
