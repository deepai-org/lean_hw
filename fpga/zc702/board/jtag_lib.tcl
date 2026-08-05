# jtag_lib.tcl -- SHARED BSCAN/JTAG primitives for the lnp64mini3 harness.
# Sourced by lnp64_rump_run.tcl and ring_pump.tcl; the single home for the
# register protocol so a tweak cannot fix one copy and miss the other.
# Callers must set the global DB (DDR base) before calling g*/bulk_* procs.
# bus_acquire/bus_release stay per-script: the pump waits harder for the
# grant than the servicer (which must proceed when the core is in S_WAIT).

proc le32 {hx} { return [expr 0x[string range $hx 6 7][string range $hx 4 5][string range $hx 2 3][string range $hx 0 1]] }
proc rd {a} { jtag targets -set -filter {name =~ {*SMT1*}}
  jtag lock; set s [jtag sequence]; $s state RESET; $s irshift -state IRUPDATE -integer 10 962
  $s drshift -state IDLE -integer 42 [expr {($a<<32)}]; $s drshift -state IDLE -capture -tdi 0 42
  set r [$s run]; $s delete; jtag unlock; return [le32 $r] }
proc wr {a d} { jtag targets -set -filter {name =~ {*SMT1*}}
  jtag lock; set s [jtag sequence]; $s state RESET; $s irshift -state IRUPDATE -integer 10 962
  $s drshift -state IDLE -integer 42 [expr {(1<<40)|($a<<32)|($d & 0xFFFFFFFF)}]; $s run; $s delete; jtag unlock }
# EXT-7 stage B: guest address -> physical offset in the DDR window.
# Identity by default. The dual servicer sets RELOC_FROM (the image's text_end)
# and RELOC_DELTA (+0x800000) under LNP64_RELOC=1, mirroring the VMA it installs
# in the core: everything at or above text_end is genuinely relocated, and the
# ring + text + low addresses stay put. This proc is the ONE definition of the
# host's side of the map -- every DDR accessor routes through it, so a site
# cannot be forgotten; forgetting one site is how a "silent" address split
# would present as memory corruption 20 minutes into a boot.
set RELOC_FROM  0xFFFFFFFF
set RELOC_DELTA 0
proc gphys {a} { global RELOC_FROM RELOC_DELTA
  return [expr {$a >= $RELOC_FROM ? $a + $RELOC_DELTA : $a}] }

proc gwrite {ga hi lo} { global DB; wr 40 [expr {$DB+[gphys $ga]}]; wr 41 $lo; wr 42 $hi }
proc regv {i} { wr 14 $i; after 1; return [expr {([rd 24]<<32)|[rd 23]}] }
proc setreg {i v} { wr 50 $i; wr 51 [expr {$v & 0xFFFFFFFF}]; wr 52 [expr {($v>>32) & 0xFFFFFFFF}] }
proc le64hex {w} { set o ""; for {set k 0} {$k<8} {incr k} { append o [format %02x [expr {($w>>($k*8))&0xff}]] }; return $o }

# THROTTLED batched writer (see lnp64_shell_on_core.tcl)
proc bulk_write {triples DB {idle 32}} {
  jtag targets -set -filter {name =~ {*SMT1*}}
  jtag lock; set s [jtag sequence]; $s state RESET
  $s irshift -state IRUPDATE -integer 10 962
  foreach {ga hi lo} $triples {
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(40<<32)|(($DB+[gphys $ga]-8)&0xFFFFFFFF)}]  ;# -8: auto-inc bitstream latches addr post-increment
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(41<<32)|($lo&0xFFFFFFFF)}]
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(42<<32)|($hi&0xFFFFFFFF)}]
    $s state IDLE $idle
  }
  $s run; $s delete; jtag unlock
}

# VERIFIED batch write: write a CONTIGUOUS batch (ga increasing by 8), read it back, and
# re-write any dropped/wrong words. Eliminates the intermittent single-word HP-write drops
# that corrupt the image (~30% of raw loads crash at BI). triples = {ga hi lo ...} contiguous.
proc bulk_write_v {triples DB {idle 32}} {
  if {![llength $triples]} return
  set first_ga [lindex $triples 0]
  set nw [expr {[llength $triples]/3}]
  bulk_write $triples $DB $idle
  for {set pass 0} {$pass<4} {incr pass} {
    set got [bulk_gread $first_ga $nw 64]   ;# dwell 64 = proven clean reads (no stale false-positives)
    set bad {}
    set k 0
    foreach {ga hi lo} $triples {
      set want [expr {($hi<<32)|($lo&0xffffffff)}]
      if {[lindex $got $k] != $want} { lappend bad $ga $hi $lo }
      incr k
    }
    if {![llength $bad]} return
    puts "  load-verify: pass $pass, re-writing [expr {[llength $bad]/3}] word(s) @[format 0x%x $first_ga]"; flush stdout
    bulk_write $bad $DB $idle             ;# rewrite only the dropped words
  }
  puts "  load-verify: WARNING still bad after 4 passes @[format 0x%x $first_ga]"; flush stdout
  global LOADOK; set LOADOK 0
}

# BULK register read: all 32 regs in one jtag sequence.
# Per reg: write REG_SEL(14)=i, dwell, select 24, capture(hi), select 23, capture(lo).
proc bulk_read_regs {} {
  jtag targets -set -filter {name =~ {*SMT1*}}
  jtag lock; set s [jtag sequence]; $s state RESET
  $s irshift -state IRUPDATE -integer 10 962
  for {set i 0} {$i<32} {incr i} {
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(14<<32)|$i}]
    $s state IDLE 8
    $s drshift -state IDLE -integer 42 [expr {24<<32}]
    $s drshift -state IDLE -capture -tdi 0 42
    $s drshift -state IDLE -integer 42 [expr {23<<32}]
    $s drshift -state IDLE -capture -tdi 0 42
  }
  set res [$s run]; $s delete; jtag unlock
  set out {}
  foreach {hi lo} $res { lappend out [expr {([le32 $hi]<<32)|[le32 $lo]}] }
  return $out
}

# One-sequence trap poll: status(20) + trap-flag(40). Was two full jtag runs.
proc poll_status {} {
  jtag targets -set -filter {name =~ {*SMT1*}}
  jtag lock; set s [jtag sequence]; $s state RESET
  $s irshift -state IRUPDATE -integer 10 962
  $s drshift -state IDLE -integer 42 [expr {20<<32}]
  $s drshift -state IDLE -capture -tdi 0 42
  $s drshift -state IDLE -integer 42 [expr {40<<32}]
  $s drshift -state IDLE -capture -tdi 0 42
  set r [$s run]; $s delete; jtag unlock
  return [list [le32 [lindex $r 0]] [le32 [lindex $r 1]]]
}

# One-sequence pc(22) + all 32 regs. Was 1 + 1 runs.
proc bulk_read_pc_regs {} {
  jtag targets -set -filter {name =~ {*SMT1*}}
  jtag lock; set s [jtag sequence]; $s state RESET
  $s irshift -state IRUPDATE -integer 10 962
  $s drshift -state IDLE -integer 42 [expr {22<<32}]
  $s drshift -state IDLE -capture -tdi 0 42
  for {set i 0} {$i<32} {incr i} {
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(14<<32)|$i}]
    $s state IDLE 8
    $s drshift -state IDLE -integer 42 [expr {24<<32}]
    $s drshift -state IDLE -capture -tdi 0 42
    $s drshift -state IDLE -integer 42 [expr {23<<32}]
    $s drshift -state IDLE -capture -tdi 0 42
  }
  set res [$s run]; $s delete; jtag unlock
  set pc [le32 [lindex $res 0]]
  set out {}
  foreach {hi lo} [lrange $res 1 end] { lappend out [expr {([le32 $hi]<<32)|[le32 $lo]}] }
  return [list $pc $out]
}

# Apply an entire trap response in ONE jtag sequence: reg writes (50/51/52),
# mem writes (40/41/42, DB-relative, in log order), next-pc (53) and resume
# (54). Previously every %REG / %MEMW cost 3 separate jtag runs (~100 USB
# round-trips per trap); this is the boot-time dominator fix.
proc apply_trap_resp {regpairs memtriples npc} {
  global DB
  jtag targets -set -filter {name =~ {*SMT1*}}
  jtag lock; set s [jtag sequence]; $s state RESET
  $s irshift -state IRUPDATE -integer 10 962
  foreach {i v} $regpairs {
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(50<<32)|$i}]
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(51<<32)|($v & 0xFFFFFFFF)}]
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(52<<32)|(($v>>32) & 0xFFFFFFFF)}]
    $s state IDLE 8
  }
  foreach {ga hi lo} $memtriples {
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(40<<32)|(($DB+[gphys $ga])&0xFFFFFFFF)}]
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(41<<32)|($lo&0xFFFFFFFF)}]
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(42<<32)|($hi&0xFFFFFFFF)}]
    $s state IDLE 32
  }
  if {$npc ne ""} { $s drshift -state IDLE -integer 42 [expr {(1<<40)|(53<<32)|($npc&0xFFFFFFFF)}] }
  $s drshift -state IDLE -integer 42 [expr {(1<<40)|(54<<32)|1}]
  $s run; $s delete; jtag unlock
}

# BULK DDR read: N consecutive words starting at guest addr in one jtag sequence.
# Per word: write DDR_A(40), trigger read (43), dwell for the HP read, sel 46 cap, sel 45 cap.
# bulk_gread maps the BASE through gphys and keeps the run contiguous. A batch
# that straddled RELOC_FROM would be physically discontiguous; no caller does
# that (text pulls stay below it, data pulls above -- the boundary is the
# text/data segment boundary), and bulk_write_v's verify would catch it loudly.
proc bulk_gread {ga nwords {dwell 64}} {
  global DB
  jtag targets -set -filter {name =~ {*SMT1*}}
  jtag lock; set s [jtag sequence]; $s state RESET
  $s irshift -state IRUPDATE -integer 10 962
  for {set k 0} {$k<$nwords} {incr k} {
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(40<<32)|(($DB+[gphys $ga]+$k*8)&0xFFFFFFFF)}]
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(43<<32)|1}]
    $s state IDLE $dwell
    $s drshift -state IDLE -integer 42 [expr {46<<32}]
    $s drshift -state IDLE -capture -tdi 0 42
    $s drshift -state IDLE -integer 42 [expr {45<<32}]
    $s drshift -state IDLE -capture -tdi 0 42
  }
  set res [$s run]; $s delete; jtag unlock
  set out {}
  foreach {hi lo} $res { lappend out [expr {([le32 $hi]<<32)|[le32 $lo]}] }
  return $out
}

