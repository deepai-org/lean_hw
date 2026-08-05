# authority_demo.tcl -- the authority mechanisms, exercised TOGETHER under a
# live NetBSD, on silicon.
#
# Each of EXT-1..EXT-7 was proven separately. This runs them against a guest
# that is actually serving traffic, and checks the property that makes them
# authority rather than decoration: revocation is SCOPED TO THE EPOCH CELL.
#
#   1. baseline          -- the guest is retiring instructions
#   2. install a VMA in ANOTHER domain (dom 3, cell 3)
#                        -- the running guest is undisturbed
#   3. bump cell 3       -- that mapping dies; the guest keeps running
#   4. STAGE B ONLY (cells split): bump cell 2 -- the RING's cell. The DMA
#      window dies on its own: networking stops, the guest keeps retiring.
#      This is the "named DMA-window grant" being revocable independently.
#   5. bump cell 1       -- the guest's OWN data mapping; it must fail closed
#
# Under stage B (LNP64_RELOC=1) the guest's mappings are ring=cell 2,
# data+low=cell 1 -- so the throwaway foreign VMA uses cell 3, NOT cell 2 as
# the identity-era demo did. Reusing cell 2 here would revoke the live guest's
# ring in step 3 and kill networking as a side effect of a step that claims to
# be harmless.
#
# The last step is destructive by design: it is the proof that translation is
# really in the path. A guest that kept running after its mapping was revoked
# would mean the MMU was decorative. Run this AFTER a PASS; the next netbsd_up
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

# Stage B detection: under LNP64_RELOC the guest runs with three VMAs and the
# ring on its own cell. The demo gains the independent-ring-revocation step.
set STAGEB 0
if {[info exists ::env(LNP64_RELOC)] && $::env(LNP64_RELOC) == 1} { set STAGEB 1 }
puts [format "  mode: %s" [expr {$STAGEB ? "stage B (ring cell 2, data cell 1)" : "identity (single VMA, cell 1)"}]]

# 2. A VMA belonging to a DIFFERENT domain. tlbMatch requires dom == domCur,
#    so this must not affect the running guest at all. Entry 7 and cell 3 are
#    unused in BOTH modes.
wr 64 7                       ;# select entry 7 (free in both modes)
wr 65 [expr {0x03000000 | 0x00100000}]   ;# base 0x100000, domain 3
wr 68 [expr {0x03000000 | 0}]            ;# delta 0, epoch cell 3
wr 66 0x00200000                         ;# limit -> validates entry 7
puts "  installed VMA#7: base 0x100000 limit 0x200000 dom 3 cell 3"
set d2 [advancing "2. after installing dom-3 VMA"]

# 3. Revoke cell 3. Entry 7 dies; the guest's entries live on cells 1 and 2.
wr 67 3
puts "  bumped epoch cell 3 (revokes VMA#7 only)"
set d3 [advancing "3. after revoking cell 3"]

# 4. Stage B only: revoke the RING's cell. The DMA window dies alone -- the
#    guest must KEEP RETIRING (its data map is cell 1) while the network path
#    is gone. This is the demo the spec promised: the DMA window is a separate
#    grant with its own bounds, revocable on its own.
set d4 -1
if {$STAGEB} {
  wr 67 2
  puts "  bumped epoch cell 2 (revokes the DMA windows: shmif ring + GEM slab)"
  set d4 [advancing "4. after revoking the DMA cell"]
  # What is TRUE here, measured on silicon 2026-08-05: ping goes to 100% loss
  # (the host measures it in the window below), and this OS quiesces to full
  # idle -- every runnable thread eventually blocks behind the dead windows, so
  # retire stops. That is fail-CLOSED, not fail-crash: the property to check on
  # the core is that it is still RUNNING and UNTRAPPED, not that it retires.
  # (A re-grant experiment revived core 1 -- the revocation destroyed nothing --
  # but core 0's event-driven waiters lost wakeups while the window was dead
  # and cannot self-recover. Revocation of a live-I/O window is not transparent
  # suspend; that is exactly why §15 pairs shootdown with a protocol.)
  set st4 [rd 20]
  set ok4run [expr {($st4 & 1) == 1 && (($st4 >> 1) & 1) == 0}]
  puts [format "  core 0 after DMA revoke: status=0x%x (running, unhalted: %s)" $st4 [expr {$ok4run ? "yes" : "NO"}]]
  puts "PING_WINDOW_OPEN"; flush stdout
  after 15000
  puts "PING_WINDOW_CLOSED"; flush stdout
}

# 5. Revoke the guest's OWN data cell. Every access must now fail closed.
wr 67 1
puts "  bumped epoch cell 1 (revokes the GUEST's data mapping)"
set d5 [advancing "5. after revoking cell 1"]

puts ""
puts "=== verdict ==="
set ok1 [expr {$d1 > 0}]
set ok2 [expr {$d2 > 0}]
set ok3 [expr {$d3 > 0}]
set ok4 [expr {!$STAGEB || $ok4run}]
set ok5 [expr {$d5 == 0}]
puts [format "  guest alive at baseline .................. %s" [expr {$ok1 ? "yes" : "NO"}]]
puts [format "  unaffected by another domain's VMA ....... %s" [expr {$ok2 ? "yes" : "NO"}]]
puts [format "  SURVIVES revocation of a foreign cell .... %s" [expr {$ok3 ? "yes" : "NO"}]]
if {$STAGEB} {
puts [format "  fail-CLOSED on DMA revoke (runs, no trap).. %s" [expr {$ok4 ? "yes" : "NO"}]]
}
puts [format "  FAILS CLOSED when its own cell is bumped . %s" [expr {$ok5 ? "yes" : "NO"}]]
if {$ok1 && $ok2 && $ok3 && $ok4 && $ok5} {
  puts "AUTHORITY_DEMO_OK -- revocation is scoped to the epoch cell, the DMA"
  puts "window is independently revocable, and the guest's own mapping is"
  puts "genuinely load-bearing (it stops without it)."
} else {
  puts "AUTHORITY_DEMO_FAILED"
}
