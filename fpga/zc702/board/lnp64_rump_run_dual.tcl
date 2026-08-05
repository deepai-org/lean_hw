# lnp64_rump_run_dual.tcl -- the §64 DUAL-CORE servicer.
#
# Same image load + trap protocol as lnp64_rump_run_loom.tcl, plus:
#   * TWO trap surfaces.  Every poll reads core 0's STATUS/TRAP *and* core 1's
#     (BSCAN index 0x80|idx -- the wrapper's dr[39] core-select), and services
#     whichever core is trapping against the SAME trap-server process state.
#     That works unchanged because trap_server_step() pins current_tid = 1 and
#     takes the trapping core's 32 registers off the wire: the servicer never
#     had a notion of *which* hardware thread trapped, so it does not need one
#     for *which core* either.
#   * core 1 is started at LNP64_CORE1_ENTRY (nm lnp64_core1_entry) with
#     r31 = LNP64_CORE1_STACK right after core 0 starts.  Core 1 immediately
#     parks in futex_wait on the DDR gate and stays there, retiring nothing,
#     until core 0's kernel publishes the gate and pulses its doorbell.
#   * per-core retire counters are printed with every progress line, so
#     "both cores advancing" is visible in the log without a second script.
# CORE1_HOLD (idx 56) resets to 1 and must be cleared before any core-1
# command lands.
#
# Original header follows.
# lnp64_shell_fast.tcl -- run the REAL NetBSD /bin/sh on lnp64mini3 with BATCHED servicing.
# Same protocol as lnp64_shell_on_core.tcl but:
#  * bulk_read_regs: all 32 regs in ONE jtag sequence (was 32x (wr+after 1+2 rds) ~ 1s/trap)
#  * bulk_gread: %NEEDMEM pulls batched, many words per jtag sequence
#  * HWTRACE line per trap (diff against cosim's TRACE reference -- 185 traps expected)
#  * text range is never pulled (read-only; the trap-server already has it)
set LN      /home/kevin/substrate0/lnp64
set HEX     /home/kevin/substrate0/test/rump_shmif_telnet_text.hex
set DATAHX  /home/kevin/substrate0/test/rump_shmif_telnet_data.hex
set TSARGS  {--namespace-root /tmp/rumpns -- rump_shmif}
set DB      0x10000000
set RING    0x20e000                   ;# shmif ring base (guest); 1MB
# --- §64 dual-core -----------------------------------------------------------
set C1SEL   0x80                       ;# dr[39] core-select: rd/wr [C1SEL|idx]
set C1ENTRY 0                          ;# guest addr of lnp64_core1_entry
set C1STACK 0x01700000                 ;# LNP64_CORE1_STACK_TOP
if {[info exists ::env(LNP64_CORE1_ENTRY)]} { set C1ENTRY [expr $::env(LNP64_CORE1_ENTRY)] }
if {[info exists ::env(LNP64_CORE1_STACK)]} { set C1STACK [expr $::env(LNP64_CORE1_STACK)] }
proc c1 {i} { global C1SEL; return [expr {$C1SEL | $i}] }
# PRELOADED: the text image (read-only, ~624K words, ~17 min over JTAG) is
# skipped when DDR already holds THIS hex. Auto-detected: the md5 of the text
# hex is recorded in TEXTMARK after a successful load; if it matches on the
# next run, a random spot-verify of DDR confirms before skipping (~20 min
# reload -> ~4 min for unchanged-text iterations). DDR persists across PL-only
# reprogramming because the PS DRAM controller keeps refreshing.
# Force a full reload with: rm /tmp/lnp64_text_loaded.md5
# DELTA: when the md5 does NOT match but TEXTCACHE (a copy of the hex that was
# last successfully loaded) does match the marker, DDR holds the OLD image ->
# word-diff old vs new and write only the changed words (a recompile touches
# a fraction of the 624K words; full reload only when there is no valid cache).
set TEXTMARK  /tmp/lnp64_text_loaded.md5
set TEXTCACHE /tmp/lnp64_text_loaded.hex
# LNP64_FASTLOADED=1 (set by reload_core.sh after fastload.tcl): the PS DAP
# already wrote text+data+zeroed bss/ring. Honored ONLY if the text
# spot-verify passes AND a data spot-verify passes -- otherwise this run
# falls back to the normal BSCAN paths (fastload is never trusted blindly).
set FASTLOADED 0
if {[info exists ::env(LNP64_FASTLOADED)] && $::env(LNP64_FASTLOADED) eq "1"} { set FASTLOADED 1 }
set PRELOADED 0
set DELTA 0
set hexmd5 ""
if {![catch {exec md5sum $HEX} m]} {
  set hexmd5 [lindex $m 0]
  if {![catch {open $TEXTMARK} mfh]} {
    set mark [string trim [read $mfh]]; close $mfh
    if {$mark eq $hexmd5} {
      set PRELOADED 1
    } elseif {[file exists $TEXTCACHE] && ![catch {exec md5sum $TEXTCACHE} cm] \
              && [lindex $cm 0] eq $mark} {
      set DELTA 1
    }
  }
}

# Decision-input log: which load path we take and WHY (post-mortems were
# impossible without this -- the md5s are the whole story).
set cachemd5 "-"
if {[file exists $TEXTCACHE] && ![catch {exec md5sum $TEXTCACHE} cm2]} { set cachemd5 [lindex $cm2 0] }
set markv "-"
if {![catch {open $TEXTMARK} mfh2]} { set markv [string trim [read $mfh2]]; close $mfh2 }
puts "LOADPATH: hex=$hexmd5 marker=$markv cache=$cachemd5 preloaded=$PRELOADED delta=$DELTA"; flush stdout

connect -url tcp:127.0.0.1:3121
after 300
source [file join [file dirname [info script]] jtag_lib.tcl]

# --- v2 header parse + image load (same as shell_on_core) ---
proc load_image {hex dbase_var} {
  upvar $dbase_var db
  set entry 0; set tbase 0; set dbase 0; set dlen 0
  set fh [open $hex]; set text {}
  foreach line [split [read $fh] "\n"] {
    set line [string trim $line]
    if {[string index $line 0] eq "#"} {
      set p [lrange [split $line] 1 end]
      switch -- [lindex $p 0] {
        entry     { set entry [expr [lindex $p 1]] }
        text-base { set tbase [expr [lindex $p 1]] }
        data-base { set dbase [expr [lindex $p 1]] }
        data-len  { set dlen  [expr [lindex $p 1]] }
      }
    } elseif {$line ne ""} { lappend text $line }
  }
  close $fh
  return [list $entry $tbase $dbase $dlen $text]
}

set TLOAD0 [clock seconds]
proc phase {msg} { global TLOAD0; puts [format "PHASE %s t=%ds" $msg [expr {[clock seconds]-$TLOAD0}]]; flush stdout }
set LOADOK 1   ;# cleared by bulk_write_v when a batch stays bad after 4 passes
set ti [load_image $HEX db]
lassign $ti entry tbase dbase dlen twords
puts [format "v2: entry=0x%x text-base=0x%x data-base=0x%x data-len=0x%x textwords=%d" $entry $tbase $dbase $dlen [llength $twords]]
puts [format "ID=0x%08X (expect 53300017)" [rd 0]]
set text_end [expr {$tbase + [llength $twords]*8}]

# --- EXT-7 stage B: real (non-identity) translation, LNP64_RELOC=1 -----------
# Guest addresses >= text_end (data/bss/stack/heap/console rings) live at
# physical +0x800000; the ring, text and low addresses stay put. gphys in
# jtag_lib is the host half of the SAME map, so every load/pull/write below
# this point relocates in step with the VMA the cores get. Implies LNP64_MMU.
#
# Boundary choice, discovered off-hardware (mmurelocselftest): the spec table's
# "catch-all over everything" would relocate guest [0x1000,0x20e000) onto
# 0x801000+, which OVERLAPS the tail of text's physical range -- so the
# relocated region starts at text_end instead, and everything below it is
# identity. The delta field is 24-bit, so the shift must stay under 16MB.
set RELOC 0
if {[info exists ::env(LNP64_RELOC)] && $::env(LNP64_RELOC) == 1} {
  set RELOC 1
  # The boundary must fall BETWEEN segments. If the header's data-base ever sat
  # below text_end, the split would run through the middle of the data segment
  # and present as corruption 20 minutes into a boot; abort here instead.
  if {$dbase < $text_end} {
    puts [format "RELOC_ABORT: data-base 0x%x < text_end 0x%x -- boundary would split the data segment" $dbase $text_end]
    exit 1
  }
  set ::RELOC_FROM  $text_end
  set ::RELOC_DELTA 0x800000
  puts [format "RELOC: guest >= 0x%x maps to physical +0x800000 (stage B)" $text_end]
}

# Install the stage-B VMA set on core prefix p (0 or C1SEL):
#   e0  ring  [RING, RING+1MB)      delta 0         cell 2  (the DMA grant)
#   e1  data  [text_end, 4GB)       delta +0x800000 cell 1  (relocated)
#   e2  low   [0, text_end)         delta 0         cell 1  (text + low, pinned:
#       fetch is untranslated, so text must stay put)
# priTree: lower index wins, so the ring carve-out overrides e2.
# cmd 66 (limit) VALIDATES, so it is last per entry; mmu_en only after all
# three are live.
proc install_vma_reloc {p RING tend} {
  wr [expr {$p|64}] 0 ; wr [expr {$p|65}] $RING ; wr [expr {$p|68}] 0x02000000
  wr [expr {$p|66}] [expr {$RING + 0x100000}]
  wr [expr {$p|64}] 1 ; wr [expr {$p|65}] $tend ; wr [expr {$p|68}] 0x01800000
  wr [expr {$p|66}] 0xFFFFFFFF
  wr [expr {$p|64}] 2 ; wr [expr {$p|65}] 0     ; wr [expr {$p|68}] 0x01000000
  wr [expr {$p|66}] $tend
  wr [expr {$p|63}] 1
}

# BATCH: words per jtag sequence. Measured on-board 2026-07-04: writes peak
# ~2000 w/s at 1024 (software per-shift cost dominates, not TCK); verify READS
# peak at small batches and degrade with size (per-capture cost) -- 1024 is
# the sweet spot for write+verify. Verified writes catch any drops.
set BATCH 1024
if {[info exists ::env(LNP64_BATCH)]} { set BATCH $::env(LNP64_BATCH) }
# PRELOADED candidate -> spot-verify DDR really holds this text before trusting
# it: read NSPOT random 64-word windows and compare. Any mismatch (e.g. a wild
# guest write corrupted text, or a previous load was interrupted) falls back to
# a full verified load.
proc spot_verify {twords tbase nspot} {
  set nw [llength $twords]
  for {set k 0} {$k < $nspot} {incr k} {
    set base [expr {int(rand()*($nw-64))}]
    set got [bulk_gread [expr {$tbase+$base*8}] 64 64]
    for {set j 0} {$j < 64} {incr j} {
      if {[lindex $got $j] != [expr 0x[lindex $twords [expr {$base+$j}]]]} {
        puts "spot-verify MISMATCH at word [expr {$base+$j}]"
        return 0
      }
    }
  }
  return 1
}
# Write a set of {index hexword} pairs as contiguous runs via bulk_write_v.
proc write_text_words {twords tbase idxfrom idxto} {
  global DB BATCH
  set tri {}; set n 0
  for {set i $idxfrom} {$i < $idxto} {incr i} {
    set w [lindex $twords $i]
    lappend tri [expr {$tbase+$i*8}] [expr 0x[string range $w 0 7]] [expr 0x[string range $w 8 15]]; incr n
    if {$n>=$BATCH} { bulk_write_v $tri $DB; set tri {}; set n 0 }
  }
  if {[llength $tri]} { bulk_write_v $tri $DB }
}
if {$PRELOADED} {
  phase "spot-verify-start"
  puts "PRELOADED candidate (md5 match): spot-verifying 16 x64-word windows..."; flush stdout
  if {![spot_verify $twords $tbase 16]} { puts "full text reload"; set PRELOADED 0 }
}
if {!$PRELOADED && $DELTA} {
  # DDR holds the previous image (marker md5 == cache md5). Diff word lists and
  # write only changed runs (gap-coalesced: rewriting an unchanged word between
  # two changed ones is cheaper than a new run).
  catch {file delete $TEXTMARK}
  set oi [load_image $TEXTCACHE dbx]
  set ow [lindex $oi 4]
  set otb [lindex $oi 1]
  if {$otb != $tbase} {
    puts "DELTA: text-base moved (0x[format %x $otb] -> 0x[format %x $tbase]); full reload"
    set DELTA 0
  } else {
    set no [llength $ow]; set nn [llength $twords]
    set GAP 64
    set changed 0; set runs {}; set rs -1; set re -1
    for {set i 0} {$i < $nn} {incr i} {
      if {$i >= $no || [lindex $ow $i] ne [lindex $twords $i]} {
        incr changed
        if {$rs < 0} { set rs $i } elseif {$i - $re > $GAP} {
          lappend runs $rs [expr {$re+1}]; set rs $i
        }
        set re $i
      }
    }
    if {$rs >= 0} { lappend runs $rs [expr {$re+1}] }
    if {$changed > $nn*4/10} {
      puts "DELTA: $changed/$nn words differ (>40%); full reload is cheaper"
      set DELTA 0; set runs {}
    } else {
      puts "DELTA: $changed/$nn words differ, [expr {[llength $runs]/2}] runs; writing..."; flush stdout
    }
    if {$DELTA} {
      foreach {a b} $runs { write_text_words $twords $tbase $a $b }
      if {[spot_verify $twords $tbase 16]} {
        set PRELOADED 1   ;# text now verified in DDR; skip the full load below
      } else {
        puts "DELTA verify failed; falling back to full reload"
      }
    }
  }
}
# TEXT is read-only -> full load only when neither preloaded nor delta-patched.
if {!$PRELOADED} {
  catch {file delete $TEXTMARK}   ;# no valid preload while a load is in flight
  puts "loading text ([llength $twords] words)..."; flush stdout
  write_text_words $twords $tbase 0 [llength $twords]
} else { puts "text in DDR verified; refreshing mutable regions only"; flush stdout }
if {!$LOADOK} {
  # A batch never verified: DDR does NOT hold this image. Do not record the
  # marker (next run falls back to a full load) and do not boot garbage.
  puts "LOAD_FAILED: unverified words remain; aborting before boot"
  puts "LOOPEND step=0 halted=0 traps=0 exit=loadfail elapsed=0s"
  exit 1
}
if {$hexmd5 ne ""} {   ;# record: DDR now holds exactly this hex
  set mfh [open $TEXTMARK w]; puts $mfh $hexmd5; close $mfh
  catch {file copy -force $HEX $TEXTCACHE}
}
# FASTLOADED and text verified -> verify data the same way, then skip the
# BSCAN mutable refresh (the DAP already zeroed bss/ring and wrote data).
set SKIP_MUTABLE 0
if {$FASTLOADED && $PRELOADED} {
  set di0 [load_image $DATAHX dbz]; set dw0 [lindex $di0 4]
  if {[llength $dw0] > 64 && [spot_verify $dw0 $dbase 4]} {
    puts "FASTLOADED: data spot-verified; skipping BSCAN mutable refresh"; flush stdout
    set SKIP_MUTABLE 1
  } else {
    puts "FASTLOADED but data spot-verify FAILED; doing BSCAN mutable refresh"; flush stdout
  }
}
# bss + ring header + data are MUTABLE -> always refresh.
# Ring: only the shmif_mem header matters for an empty bus (first/last/gen/
# lock); stale payload bytes beyond it are never read before being rewritten.
# Zero the first 4KB instead of the whole 1MB ring (saves ~130K words/run).
phase "text-done"
if {!$SKIP_MUTABLE} {
puts "zeroing shmif ring header (512 words)..."; flush stdout
set tri {}; set n 0
for {set off 0} {$off < 0x1000} {incr off 8} {
  lappend tri [expr {$RING+$off}] 0 0; incr n
  if {$n>=$BATCH} { bulk_write $tri $DB; set tri {}; set n 0 }
}
if {[llength $tri]} { bulk_write $tri $DB }
puts "zeroing bss ([expr {$dlen/8}] words)..."; flush stdout
set tri {}; set n 0
for {set off 0} {$off < $dlen} {incr off 8} {
  lappend tri [expr {$dbase+$off}] 0 0; incr n
  if {$n>=$BATCH} { bulk_write $tri $DB; set tri {}; set n 0 }
}
if {[llength $tri]} { bulk_write $tri $DB }
set di [load_image $DATAHX db2]; set dw [lindex $di 4]
puts "loading data ([llength $dw] words)..."; flush stdout
set tri {}; set n 0; set j 0
foreach w $dw {
  lappend tri [expr {$dbase+$j*8}] [expr 0x[string range $w 0 7]] [expr 0x[string range $w 8 15]]; incr j; incr n
  if {$n>=$BATCH} { bulk_write_v $tri $DB; set tri {}; set n 0 }
}
if {[llength $tri]} { bulk_write_v $tri $DB }
}

phase "mutable-done"
puts "SERVICER: opening trap-server pipe..."; flush stdout
set ts [open "| $LN trap-server $HEX --data-hex $DATAHX --pull-mem --stdin-pipe $TSARGS 2>/tmp/ts_err.log" r+]
fconfigure $ts -buffering line -blocking 1
while {[gets $ts line] >= 0} {
  if {[string match "%INITMEM*" $line]} { lassign [split $line] _ a v; gwrite [expr 0x$a] [expr {([expr $v]>>32)&0xffffffff}] [expr {[expr $v]&0xffffffff}]
  } elseif {$line eq "%READY"} break
}
phase "servicer-ready"
puts "SERVICER: %READY, starting core"; flush stdout
# --- shmif bridge socket (tap_bridge/shmif_bridge.py listening on 9099) ---
set ringsock ""
proc ring_connect {} {
  global ringsock
  if {$ringsock ne ""} { catch {close $ringsock}; set ringsock "" }
  if {![catch {socket 127.0.0.1 9099} sk]} {
    set ringsock $sk
    fconfigure $ringsock -buffering line -blocking 0 -translation lf
    puts "RING: connected to shmif bridge"; flush stdout; return 1
  }
  return 0
}
puts "RING: serviced by ring_pump.tcl (separate xsdb; Tcl sockets wedge this interpreter)"
proc bus_acquire {} {
  # Request the HP bus and pause the core. SHORT wait for grant then PROCEED regardless:
  # post-boot the core sleeps in accept() (S_WAIT) and never reaches S_PAUSE, so it never
  # grants -- but a core in S_WAIT does NOT own the HP master, so the JTAG can drive HP
  # directly. Waiting 200000 reads here was a ~200s stall per op (killed ring throughput).
  wr 55 1
  for {set i 0} {$i<40} {incr i} { set s [rd 20]; if {(($s>>3)&1) || (($s&1)==0)} break }
}
proc bus_release {} { wr 55 0 }
# service one bridge batch: R/W lines until E (called when the socket is readable)
proc ring_service {} {
  global ringsock RING
  fconfigure $ringsock -blocking 1
  bus_acquire
  while {[gets $ringsock line] >= 0} {
    set f [split $line]
    switch -- [lindex $f 0] {
      R { set off [lindex $f 1]; set nw [lindex $f 2]
          set out {}
          foreach w [bulk_gread [expr {$RING+$off}] $nw] { lappend out [format %016x $w] }
          puts $ringsock "D [join $out { }]" }
      W { set off [lindex $f 1]
          set tri {}
          set ga [expr {$RING+$off}]
          foreach hx [lrange $f 2 end] {
            set v [expr 0x$hx]
            lappend tri $ga [expr {($v>>32)&0xffffffff}] [expr {$v&0xffffffff}]
            incr ga 8
          }
          bulk_write $tri 0x10000000 }
      E { break }
      default {}
    }
  }
  bus_release
  fconfigure $ringsock -blocking 0
}

# ---- dual-core BSCAN primitives --------------------------------------------
# One jtag sequence, four captures: core 0 STATUS(20)/TRAP(40) and core 1's.
proc poll_status_dual {} {
  jtag targets -set -filter {name =~ {*SMT1*}}
  jtag lock; set s [jtag sequence]; $s state RESET
  $s irshift -state IRUPDATE -integer 10 962
  foreach a {20 40 0x94 0xa8} {
    $s drshift -state IDLE -integer 42 [expr {[expr $a]<<32}]
    $s drshift -state IDLE -capture -tdi 0 42
  }
  set r [$s run]; $s delete; jtag unlock
  return [list [le32 [lindex $r 0]] [le32 [lindex $r 1]] \
               [le32 [lindex $r 2]] [le32 [lindex $r 3]]]
}
# pc(22) + 32 regs of the SELECTED core, one sequence (core 0: sel 0).
proc bulk_read_pc_regs_sel {sel} {
  jtag targets -set -filter {name =~ {*SMT1*}}
  jtag lock; set s [jtag sequence]; $s state RESET
  $s irshift -state IRUPDATE -integer 10 962
  $s drshift -state IDLE -integer 42 [expr {($sel|22)<<32}]
  $s drshift -state IDLE -capture -tdi 0 42
  for {set i 0} {$i<32} {incr i} {
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(($sel|14)<<32)|$i}]
    $s state IDLE 8
    $s drshift -state IDLE -integer 42 [expr {($sel|24)<<32}]
    $s drshift -state IDLE -capture -tdi 0 42
    $s drshift -state IDLE -integer 42 [expr {($sel|23)<<32}]
    $s drshift -state IDLE -capture -tdi 0 42
  }
  set res [$s run]; $s delete; jtag unlock
  set pc [le32 [lindex $res 0]]
  set out {}
  foreach {hi lo} [lrange $res 1 end] { lappend out [expr {([le32 $hi]<<32)|[le32 $lo]}] }
  return [list $pc $out]
}
# Whole trap response to the SELECTED core in one sequence.  Memory writes are
# NOT core-selected: DDR is shared and the JTAG DDR window is core 0's path
# (arbiter requester port 0), so 40/41/42 always go to core 0's surface.
proc apply_trap_resp_sel {sel regpairs memtriples npc} {
  global DB
  jtag targets -set -filter {name =~ {*SMT1*}}
  jtag lock; set s [jtag sequence]; $s state RESET
  $s irshift -state IRUPDATE -integer 10 962
  foreach {i v} $regpairs {
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(($sel|50)<<32)|$i}]
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(($sel|51)<<32)|($v & 0xFFFFFFFF)}]
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(($sel|52)<<32)|(($v>>32) & 0xFFFFFFFF)}]
    $s state IDLE 8
  }
  foreach {ga hi lo} $memtriples {
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(40<<32)|(($DB+[gphys $ga])&0xFFFFFFFF)}]
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(41<<32)|($lo&0xFFFFFFFF)}]
    $s drshift -state IDLE -integer 42 [expr {(1<<40)|(42<<32)|($hi&0xFFFFFFFF)}]
    $s state IDLE 32
  }
  if {$npc ne ""} { $s drshift -state IDLE -integer 42 [expr {(1<<40)|(($sel|53)<<32)|($npc&0xFFFFFFFF)}] }
  $s drshift -state IDLE -integer 42 [expr {(1<<40)|(($sel|54)<<32)|1}]
  $s run; $s delete; jtag unlock
}

wr 13 1
setreg 31 0x17f8000
wr 53 $entry
wr 13 2
# EXT-1 (Law 5): arm a BOUNDED preemption quantum. Law 5 wants the
# non-preemptible interval bounded, not small -- at 2.5M cycles (100 ms @
# 25 MHz) the measured cost is unmeasurable (retire 1.317M vs 1.313M per 2 s)
# while 1 ms costs 3.3x RTT. So the shipping demo runs PREEMPTIVELY at a long
# quantum; LNP64_QUANTUM=0 restores the cooperative machine for bisecting.
set QUANTUM 2500000
if {[info exists ::env(LNP64_QUANTUM)]} { set QUANTUM $::env(LNP64_QUANTUM) }
if {$QUANTUM > 0} { wr 57 $QUANTUM; puts "PREEMPT: core0 quantum=$QUANTUM cycles" }

# EXT-7 stage B, software half: run the guest under REAL translation.
#
# One VMA per core, installed before the core starts: base 0, limit 0xFFFFFFFF,
# delta 0, domain 0, epoch cell 1. That is the identity map, so the guest sees
# the same addresses it always did -- but every DDR access now goes THROUGH the
# TLB, is domain-checked, and is revocable by bumping cell 1 (cmd 67).
# "Identity" is the honest description: the mapping does not relocate anything
# yet; what changes is that translation is in the path at all.
#
# Order matters: cmd 66 (limit) is what VALIDATES the entry, so it goes last,
# and mmu_en only after the entry is live.
#   64 = TLB_SEL   65 = base | dom<<24   68 = delta | cell<<24   66 = limit
#   63 = MMU_EN    67 = MAP_PROTECT (revoke by cell)
#
# Checked off-hardware first by mmuidentityselftest: an identity VMA computes
# exactly what bypass computes, at several alignments. ddrEaRaw word-aligns and
# ddrEaXlat does not, so that equality was not obvious and was worth proving in
# the ladder rather than discovering here.
if {$RELOC} {
  install_vma_reloc 0 $RING $text_end
  puts [format "MMU: stage-B VMAs on core 0 (ring cell 2; data +0x800000 cell 1; low pinned); mmu_en=1"]
} elseif {[info exists ::env(LNP64_MMU)] && $::env(LNP64_MMU) == 1} {
  # `c1` ORs in the core-1 select bit; it is not a +64 offset.
  foreach idxs {{64 65 68 66 63}} {}
  wr 64 0 ; wr 65 0x00000000 ; wr 68 0x01000000 ; wr 66 0xFFFFFFFF ; wr 63 1
  # Core 1's VMA is NOT installed here: `wr [c1 13] 1` below resets core 1, and
  # cmd 13's reset zeroes tlb_vld. Installing early left core 1 with mmu_en=1
  # and no valid entry, so every access failed closed -- it retired 20
  # instructions and parked. It is installed after its reset instead.
  puts "MMU: identity VMA installed on core 0 (base 0, limit 0xFFFFFFFF, cell 1); mmu_en=1"
}

# ---- start core 1 -----------------------------------------------------------
# The image is already in DDR, so core 1 boots the SAME image at a different
# entry and stack; it parks in futex_wait on the gate word until core 0's
# kernel releases it, so starting it now cannot race rump_init.
set C1LIVE 0
if {$C1ENTRY != 0} {
  puts [format "CORE1: hold=%d before" [expr {([rd 56]>>5)&1}]]
  wr 56 0                                    ;# clear CORE1_HOLD (resets to 1)
  after 50
  wr [c1 13] 1                               ;# reset core 1 (zeroes dmem + rf)
  after 300
  wr [c1 50] 31; wr [c1 51] [expr {$C1STACK & 0xFFFFFFFF}]
  wr [c1 52] [expr {($C1STACK>>32) & 0xFFFFFFFF}]
  wr [c1 53] $C1ENTRY
  if {$RELOC} {
    # After the reset (which zeroes tlb_vld), before the core runs.
    install_vma_reloc $C1SEL $RING $text_end
    puts "MMU: stage-B VMAs installed on core 1 after reset; mmu_en=1"
  } elseif {[info exists ::env(LNP64_MMU)] && $::env(LNP64_MMU) == 1} {
    # After the reset (which zeroes tlb_vld), before the core runs.
    wr [c1 64] 0 ; wr [c1 65] 0x00000000 ; wr [c1 68] 0x01000000
    wr [c1 66] 0xFFFFFFFF ; wr [c1 63] 1
    puts "MMU: identity VMA installed on core 1 after reset; mmu_en=1"
  }
  wr [c1 13] 2                               ;# run
  if {$QUANTUM > 0} { wr [c1 57] $QUANTUM; puts "PREEMPT: core1 quantum=$QUANTUM cycles" }
  after 100
  set C1LIVE 1
  puts [format "CORE1: started entry=0x%x sp=0x%x status=0x%x retire=%d pc=0x%x" \
        $C1ENTRY $C1STACK [rd [c1 20]] [rd [c1 21]] [rd [c1 22]]]
  flush stdout
}

set console ""; set traps 0; set exitcode ""; set needmem_total 0
set traps1 0
set t0 [clock seconds]; set hb 0; set idlespin 0; set booted 0
for {set step 0} {$step < 200000000} {incr step} {
  if {[file exists /tmp/stop_servicer]} { puts "STOPPED by /tmp/stop_servicer (clean, between traps)"; break }
  if {[file exists /tmp/opdump]} {
    # snapshot the trap-op tally (touch /tmp/opdump; result in /tmp/ops_<t>.json)
    file delete /tmp/opdump
    puts $ts "OPDUMP /tmp/ops_[clock seconds].json"
    flush $ts
  }
  lassign [poll_status_dual] st20 st40 s120 s140
  if {($st20>>1)&1} break
  # ---- core 1's trap surface.  Serviced FIRST so a one-shot core-1 boot trap
  # can never sit behind core 0's steady state (which, once booted, is silent).
  if {$C1LIVE && ($s140 & 1)} {
    incr traps1
    lassign [bulk_read_pc_regs_sel $C1SEL] pc1 rl1
    puts [format "HWTRAP1 n=%d pc=%x op=%x" $traps1 $pc1 [expr {($s140>>8)&0xff}]]; flush stdout
    puts $ts [format "TRAP %x %s" $pc1 [join $rl1 ","]]
    set npc1 ""; set rp1 {}; set mt1 {}
    while {[gets $ts line] >= 0} {
      if {$line eq ""} continue
      set f [split $line]
      switch -glob -- [lindex $f 0] {
        "%NEEDMEM" { set a [expr 0x[lindex $f 1]]; set l [expr 0x[lindex $f 2]]
                     incr needmem_total $l
                     set hx ""
                     set nw [expr {($l+7)/8}]
                     foreach w [bulk_gread $a $nw] { append hx [le64hex $w] }
                     puts $ts [format "MEM %x %s" $a [string range $hx 0 [expr {$l*2-1}]]] }
        "%EXIT"    { set exitcode [lindex $f 1] }
        "%REG"     { lappend rp1 [lindex $f 1] [lindex $f 2] }
        "%MEMW"    { set a [expr 0x[lindex $f 1]]; set v [expr [lindex $f 2]]
                     lappend mt1 $a [expr {($v>>32)&0xffffffff}] [expr {$v&0xffffffff}] }
        "%NEXTPC"  { set npc1 [expr 0x[lindex $f 1]] }
        "%DONE"    { break }
        default    { append console $line "\n"; puts "GUEST1: $line"; flush stdout }
      }
    }
    apply_trap_resp_sel $C1SEL $rp1 $mt1 $npc1
    continue
  }
  if {($st20&1)==0} {
    incr idlespin
    if {$ringsock ne "" && ($idlespin % 2000 == 0)} {
      bus_acquire
      set hdr [bulk_gread $RING 4]
      bus_release
      set w2 [lindex $hdr 2]; set w3 [lindex $hdr 3]
      puts [format "HEARTBEAT status=0x%x gen=%d first=%d last=%d spin=%d retire0=%d retire1=%d c1status=0x%x" $st20 [lindex $hdr 1] [expr {$w2 & 0xffffffff}] [expr {($w2>>32)&0xffffffff}] $idlespin [rd 21] [rd [c1 21]] [rd [c1 20]]]; flush stdout
    }
    continue
  }
  set idlespin 0
  if {($st40&1)==0} continue
  incr traps
  if {$traps>=790} { set booted 1 }
  if {$traps % 25 == 0} { puts [format "progress: traps=%d traps1=%d dt=%ds needmem=%dB console=%d retire0=%d retire1=%d" $traps $traps1 [expr {[clock seconds]-$t0}] $needmem_total [string length $console] [rd 21] [rd [c1 21]]]; flush stdout }
  lassign [bulk_read_pc_regs] pc rl
  puts [format "HWTRAP n=%d pc=%x op=%x" $traps $pc [expr {($st40>>8)&0xff}]]; flush stdout
  puts $ts [format "TRAP %x %s" $pc [join $rl ","]]
  set npc ""; set regpairs {}; set memtriples {}
  while {[gets $ts line] >= 0} {
    if {$line eq ""} continue
    set f [split $line]
    switch -glob -- [lindex $f 0] {
      "%NEEDMEM" { set a [expr 0x[lindex $f 1]]; set l [expr 0x[lindex $f 2]]
                   incr needmem_total $l
                   set hx ""
                   set nw [expr {($l+7)/8}]
                   foreach w [bulk_gread $a $nw] { append hx [le64hex $w] }
                   puts $ts [format "MEM %x %s" $a [string range $hx 0 [expr {$l*2-1}]]] }
      "%EXIT"    { set exitcode [lindex $f 1] }
      "%REG"     { lappend regpairs [lindex $f 1] [lindex $f 2] }
      "%MEMW"    { set a [expr 0x[lindex $f 1]]; set v [expr [lindex $f 2]]
                   lappend memtriples $a [expr {($v>>32)&0xffffffff}] [expr {$v&0xffffffff}] }
      "%NEXTPC"  { set npc [expr 0x[lindex $f 1]] }
      "%DONE"    { break }
      default    { append console $line "\n"; puts "GUEST: $line"; flush stdout }
    }
  }
  # regs + mem writes + next-pc + resume: ONE jtag sequence per trap
  apply_trap_resp_sel 0 $regpairs $memtriples $npc
  if {$exitcode ne ""} break
}
puts $ts "QUIT"; catch {close $ts}
puts [format "LOOPEND step=%d halted=%d traps=%d traps1=%d exit=%s elapsed=%ds" $step [expr {([rd 20]>>1)&1}] $traps $traps1 $exitcode [expr {[clock seconds]-$t0}]]
puts [format "RETIRE core0=%d core1=%d  status0=0x%x status1=0x%x pc1=0x%x" [rd 21] [rd [c1 21]] [rd 20] [rd [c1 20]] [rd [c1 22]]]
puts [format "traps=%d exit=%s" $traps $exitcode]
puts "CONSOLE:\n$console"

# In-guest console rings (section 66). Under the native GEM pump the guest
# prints with rumpuser_putchar -- a DDR store, not a host-serviced SEND -- so
# the CONSOLE capture above is empty and the boot looks silent. Dump the rings
# HERE, inside the session that already has DDR up: a fresh xsdb connect leaves
# the DDR controller in reset, and a power cycle takes the evidence with it.
# Layout [u32 magic][u32 wptr][bytes], core n at 0x3000000 + n*0x100000.
# The servicer drives the PL over the BSCAN chain, so `mrd` (which needs an
# ARM DAP target) fails here until we point at the A9 -- the same selection
# fastload.tcl uses. The run is over, so nothing needs the PL target back.
if {[catch {targets -set -filter {name =~ {*Cortex-A9*#0*}}} cerr]} {
  puts "%CONRING target-select failed: $cerr"
}
foreach cr {0 1} {
  # Guest physical != PS physical: the guest DDR window is based at 0x10000000
  # (fastload.tcl `set DB 0x10000000`), so guest 0x3000000 is PS 0x13000000.
  # Reading the guest address directly returns unrelated DDR and looks exactly
  # like "the guest never printed".
  # Stage B: the console rings live above text_end, so they are RELOCATED
  # guest state -- read them through the same map or see unrelated DDR.
  set cb [expr {0x10000000 + [gphys [expr {0x3000000 + $cr * 0x100000}]]}]
  if {[catch {set cm [lindex [mrd -force -value $cb 1] 0]} cerr]} {
    puts "%CONRING core=$cr read failed: $cerr"; continue
  }
  if {$cm != 0xc0ffee01} { puts "%CONRING core=$cr no-ring magic=[format 0x%x $cm]"; continue }
  set cw [lindex [mrd -force -value [expr {$cb+4}] 1] 0]
  set cn [expr {$cw > 4096 ? 4096 : $cw}]
  puts "%CONRING core=$cr base=[format 0x%x $cb] bytes=$cn"
  if {$cn <= 0} { continue }
  # Collect the raw bytes once, then render two ways. The board ring came out
  # with every character repeated 8x, which is what a one-char-per-64-bit-word
  # layout looks like when read packed -- so render the stride-8 view too and
  # let the output say which one is real rather than guessing.
  set cbytes {}
  foreach cwd [mrd -force -value [expr {$cb+8}] [expr {($cn+3)/4}]] {
    for {set ci 0} {$ci < 4} {incr ci} {
      lappend cbytes [expr {($cwd >> ($ci*8)) & 0xff}]
    }
  }
  # Dump raw hex from three places and let the BYTES say what the layout is:
  # the ring start, and two windows around the write head. Guessing the stride
  # from a rendering cost three board cycles -- a rendering silently drops
  # non-printable bytes, so it cannot tell "one char per word" from "packed".
  set chead [expr {$cw % 0x10000}]
  # Render the window ending at the write head; the ring wraps at 0x10000
  # chars and this one wraps several times per run, so the start is ancient
  # history. Runs of repeated characters here are REAL -- the guest writes
  # them. That was checked the hard way: the PS DAP and the mini's own HP
  # master (regs 40/43/45/46) return identical words, and a word like
  # 0x202020202020204E is a correct lane merge, not a smear. See
  # lean_hw Machines/Lnp64mini/EXTEND_SPEC.md, "byte stores are fine".
  set chead [expr {$cw % 0x10000}]
  set cwin 1200
  set cfrom [expr {$chead > $cwin ? $chead - $cwin : 0}]
  set cn [expr {$chead - $cfrom}]
  if {$cn > 0} {
    puts "--- core $cr TEXT (wptr=$cw, last $cn chars before the head) ---"
    set ct ""
    foreach cwd [mrd -force -value [expr {$cb + 8 + $cfrom}] [expr {($cn+3)/4}]] {
      for {set ci 0} {$ci < 4} {incr ci} {
        set cby [expr {($cwd >> ($ci*8)) & 0xff}]
        if {$cby >= 32 && $cby < 127} { append ct [format %c $cby] } elseif {$cby == 10} { append ct "\n" }
      }
    }
    puts $ct
  }
}
puts "RUMP_RUN_DONE"
