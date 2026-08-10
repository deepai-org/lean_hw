# epoch_demo.tcl -- read the §3 epoch demo state off the running board.
#
# The demo runs entirely in the guest: core 1 holds a reference and re-presents
# it every kernel lap; core 0 bumps from the telnet shell (`epoch bump`).  This
# script is the OBSERVER -- it reads core 1's recorded outcomes out of the SMP
# gate struct in DDR over BSCAN, so it never participates in the protocol.
#
# Usage: LNP64_SMP_GATE=0x... xsdb epoch_demo.tcl        (gate address from
#        `nm image.elf | awk '/B lnp64_smp$/{print "0x"$1}'`)
#
# struct lnp64_smp_gate (8-byte words, toolchain/lnp64_smp.h):
#   0 ready  1 online  2 laps  3 stop  4 err
#   5 epoch_held  6 epoch_checks  7 epoch_fail([7:0] outcome, [63:8] first-fail lap)
# xsdb buffers stdout when it is not a tty and, having no `exit` of its own,
# drops into the interactive prompt when the script ends -- so an observer run
# from a service, a pipe or `ssh host xsdb ...` used to hang at the prompt and
# lose every buffered line to the eventual kill.  That is why the last two runs
# printed NOTHING.  Line-buffer, and exit explicitly (see `done` below).
fconfigure stdout -buffering line
fconfigure stderr -buffering line

source [file join [file dirname [info script]] board_env.tcl]
source $LOOM_JTAG_LIB
connect -url tcp:127.0.0.1:3121
after 200

# Leave the prompt on every path, including an error inside a jtag proc.
proc done {code} { puts "EPOCH_DEMO_DONE"; flush stdout; exit $code }

set GATE 0
if {[info exists ::env(LNP64_SMP_GATE)]} { set GATE $::env(LNP64_SMP_GATE) }
if {$GATE == 0} { puts "set LNP64_SMP_GATE (nm 'B lnp64_smp')"; flush stdout; exit 1 }
set DB 0x10000000


# The HP-bus handshake (per-script by convention -- jtag_lib.tcl only uses it).
# Same shape as the dual servicer's: request, wait briefly for the grant, then
# proceed -- a core parked in S_WAIT never reaches S_PAUSE but also does not own
# the HP master, so JTAG may drive it directly.
proc bus_acquire {} {
  wr 55 1
  for {set i 0} {$i<40} {incr i} { set s [rd 20]; if {(($s>>3)&1) || (($s&1)==0)} break }
}
proc bus_release {} { wr 55 0 }

proc outcome_name {c} {
  switch -- $c {
    0 { return "OK" }        1 { return "-BADREF" }
    2 { return "-POISONED" } 3 { return "-STALE" }
    default { return "-DENIED" }
  }
}

proc gate_words {base n} {
  # The core owns the HP master while it runs; reads without the bus grant
  # return garbage (observed: ASCII-looking values).  Acquire, read, release --
  # exactly what the servicer does around its own bulk_gread.
  bus_acquire
  set w [bulk_gread $base $n 64]
  bus_release
  return $w
}

proc sample {tag} {
  global GATE
  set w [gate_words $GATE 8]
  set held   [lindex $w 5]
  set checks [lindex $w 6]
  set failw  [lindex $w 7]
  set oc     [expr {$failw & 0xff}]
  set flap   [expr {$failw >> 8}]
  puts [format "%s laps=%d held_epoch=%d checks=%d last=%s first_fail_lap=%s" \
        $tag [lindex $w 2] $held $checks [outcome_name $oc] \
        [expr {$flap == 0 ? "none" : $flap}]]
  return [list $checks $oc $flap]
}

puts "== epoch demo observer =="
set a [sample "BEFORE"]
after 5000
set b [sample "+5s   "]

# progress check: core 1 must actually be re-presenting the reference
set d [expr {[lindex $b 0] - [lindex $a 0]}]
puts "checks in 5s: $d"
if {$d == 0} {
  puts "WARN core 1 is not checking -- engine unreachable from core 1?"
  puts "     (DUAL_SPEC D5 ties core 1's GP responses to reads-0; the holder"
  puts "      is presence-guarded, so this is inert-not-broken.)"
}

# the acceptance the goal names: once core 0 has bumped (from the shell), the
# held reference must be -STALE and must STAY -STALE (T-E1 / T-E3).
set oc [lindex $b 1]
if {$oc == 0} {
  puts "STATE: reference still current (no bump has returned yet)"
} else {
  puts "STATE: reference is [outcome_name $oc] since lap [lindex $b 2]"
  after 5000
  set c [sample "+10s  "]
  if {[lindex $c 1] == 0} {
    puts "FAIL: outcome returned to OK -- T-E1/T-E3 violated ON SILICON"
  } else {
    puts "HOLDS: still [outcome_name [lindex $c 1]] -- stale/poison fails forever"
  }
}
done 0
