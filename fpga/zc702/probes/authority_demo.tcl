# authority_demo.tcl -- the authority mechanisms, exercised TOGETHER under a
# live NetBSD, on silicon.
#
# Each of EXT-1..EXT-7 was proven separately. This runs them against a guest
# that is actually serving traffic, and checks the property that makes them
# authority rather than decoration: revocation is SCOPED TO THE EPOCH CELL.
#
#   1. baseline          -- the guest is retiring instructions
#   2. install a VMA in ANOTHER domain (dom 3, cell 2)
#                        -- the running guest (dom 0, cell 1) is undisturbed
#   3. bump cell 2       -- that mapping dies; the guest keeps running
#   4. bump cell 1       -- the guest's OWN mapping; it must fail closed
#
# Step 4 is destructive by design: it is the proof that translation is really
# in the path. A guest that kept running after its mapping was revoked would
# mean the MMU was decorative. Run this AFTER a PASS; the next netbsd_up
# rebuilds the world.
#
# Command indices (Core.lean): 63 MMU_EN, 64 TLB_SEL, 65 base|dom<<24,
# 66 limit (also VALIDATES), 67 MAP_PROTECT (revoke by cell), 68 delta|cell<<24
connect -url tcp:127.0.0.1:3121
after 300
set DB 0x10000000
source /home/kevin/substrate0/test/jtag_lib.tcl

proc retire {} { return [rd 21] }
proc advancing {label} {
  set a [retire] ; after 700 ; set b [retire]
  set d [expr {$b - $a}]
  puts [format "  %-34s retire %d -> %d  (delta %d)  %s" $label $a $b $d \
        [expr {$d > 0 ? "ADVANCING" : "STOPPED"}]]
  return $d
}

puts "=== authority demo: mechanisms together, under a live guest ==="
set d1 [advancing "1. baseline"]

# 2. A VMA belonging to a DIFFERENT domain. tlbMatch requires dom == domCur,
#    so this must not affect the running guest at all.
wr 64 1                       ;# select entry 1
wr 65 [expr {0x03000000 | 0x00100000}]   ;# base 0x100000, domain 3
wr 68 [expr {0x02000000 | 0}]            ;# delta 0, epoch cell 2
wr 66 0x00200000                         ;# limit -> validates entry 1
puts "  installed VMA#1: base 0x100000 limit 0x200000 dom 3 cell 2"
set d2 [advancing "2. after installing dom-3 VMA"]

# 3. Revoke cell 2. Entry 1 dies; the guest's entry 0 is on cell 1 and lives.
wr 67 2
puts "  bumped epoch cell 2 (revokes VMA#1 only)"
set d3 [advancing "3. after revoking cell 2"]

# 4. Revoke the guest's OWN cell. Every access must now fail closed.
wr 67 1
puts "  bumped epoch cell 1 (revokes the GUEST's mapping)"
set d4 [advancing "4. after revoking cell 1"]

puts ""
puts "=== verdict ==="
set ok1 [expr {$d1 > 0}]
set ok2 [expr {$d2 > 0}]
set ok3 [expr {$d3 > 0}]
set ok4 [expr {$d4 == 0}]
puts [format "  guest alive at baseline .................. %s" [expr {$ok1 ? "yes" : "NO"}]]
puts [format "  unaffected by another domain's VMA ....... %s" [expr {$ok2 ? "yes" : "NO"}]]
puts [format "  SURVIVES revocation of a foreign cell .... %s" [expr {$ok3 ? "yes" : "NO"}]]
puts [format "  FAILS CLOSED when its own cell is bumped . %s" [expr {$ok4 ? "yes" : "NO"}]]
if {$ok1 && $ok2 && $ok3 && $ok4} {
  puts "AUTHORITY_DEMO_OK -- revocation is scoped to the epoch cell, and the"
  puts "guest's own mapping is genuinely load-bearing (it stops without it)."
} else {
  puts "AUTHORITY_DEMO_FAILED"
}
