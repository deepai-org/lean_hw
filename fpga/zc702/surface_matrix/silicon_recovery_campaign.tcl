# ZC702 silicon campaign for Loom's depth-eight full-rate independent-flush
# realization. Required: LOOM_ROOT, SURFACE_BITSTREAM, SURFACE_RTL_SHA256.

foreach required {LOOM_ROOT SURFACE_BITSTREAM SURFACE_RTL_SHA256} {
  if {![info exists ::env($required)] || $::env($required) eq ""} {
    error "missing required environment variable $required"
  }
}
set server tcp:127.0.0.1:3121
if {[info exists ::env(SURFACE_HW_SERVER)]} { set server $::env(SURFACE_HW_SERVER) }

proc fail {message} {
  puts stderr "SURFACE_RECOVERY_SILICON_FAIL $message"
  error $message
}
proc hex32 {value} { return [format %08x [expr {$value & 0xffffffff}]] }
proc expect_eq {what actual expected} {
  if {[expr {$actual & 0xffffffff}] != [expr {$expected & 0xffffffff}]} {
    fail "$what expected=0x[hex32 $expected] actual=0x[hex32 $actual]"
  }
}
proc command {index value} {
  wr $index $value
  after 25
  expect_eq "command readback index=$index" [rd $index] $value
}
proc wait_at_least {index target timeout_ms} {
  set elapsed 0
  while {$elapsed < $timeout_ms} {
    set value [rd $index]
    if {[expr {$value & 0xffffffff}] >= $target} { return $value }
    after 20
    incr elapsed 20
  }
  fail "timeout index=$index target=$target last=[rd $index]"
}
proc wait_exact {index expected timeout_ms} {
  set elapsed 0
  while {$elapsed < $timeout_ms} {
    set value [rd $index]
    if {[expr {$value & 0xffffffff}] == $expected} { return }
    after 20
    incr elapsed 20
  }
  fail "timeout index=$index expected=$expected last=[rd $index]"
}

connect -url $server
if {![info exists ::env(SURFACE_SKIP_PROGRAM)] || $::env(SURFACE_SKIP_PROGRAM) ne "1"} {
  targets -set -filter {name =~ "xc7z*"}
  fpga -file $::env(SURFACE_BITSTREAM)
  after 1000
}
source [file join $::env(LOOM_ROOT) fpga zc702 board jtag_lib.tcl]

expect_eq "transport magic" [rd 0] 0x534d4154
scan [string range $::env(SURFACE_RTL_SHA256) 0 7] %x rtl_prefix
expect_eq "emitted RTL hash prefix" [rd 3] $rtl_prefix
set status [rd 4]
if {($status & 4) == 0} { fail "independent clocks not ready status=0x[hex32 $status]" }
set source_hb [rd 5]
set sink_hb [rd 6]
after 50
if {[rd 5] == $source_hb} { fail "source clock heartbeat did not advance" }
if {[rd 6] == $sink_hb} { fail "sink clock heartbeat did not advance" }

# Establish a known empty epoch using only the supported common reset.
command 1 4
after 50
expect_eq "initial accepted" [rd 16] 0
expect_eq "initial delivered" [rd 24] 0
expect_eq "initial recovery status" [rd 42] 0

# Fill, release the checker, and request independent flush with transfers
# active. Bits 3 and 4 are held source/sink recovery requests; common reset
# bit 2 remains low throughout the recovery itself.
command 2 4096
command 1 1
after 25
command 1 3
wait_at_least 24 128 30000
set before_accepted [rd 16]
set before_delivered [rd 24]
if {$before_accepted == 0 || $before_delivered == 0} {
  fail "recovery was not requested under active traffic"
}
command 1 27
wait_exact 42 3 30000
after 50
expect_eq "recovered accepted" [rd 16] 0
expect_eq "recovered delivered" [rd 24] 0
expect_eq "recovered expected sequence" [rd 80] 0
expect_eq "recovered data error" [rd 40] 0

# Release both held requests, allow the four-phase endpoints to re-arm, then
# run a fresh checked epoch without asserting common reset.
command 1 1
wait_exact 42 0 30000
after 50
command 1 3
wait_at_least 24 4096 30000
command 1 0
after 50
expect_eq "restart accepted" [rd 16] 4096
expect_eq "restart delivered" [rd 24] 4096
expect_eq "restart expected sequence" [rd 80] 4096
expect_eq "restart digest" [rd 32] 0
expect_eq "restart data errors" [rd 40] 0
expect_eq "restart full-rate gap errors" [rd 41] 0
expect_eq "released recovery status" [rd 42] 0
if {[rd 56] == 0} { fail "source backpressure was not exercised" }
if {[rd 64] == 0} { fail "checker pause was not exercised" }

puts "SURFACE_RECOVERY_SILICON_PASS depth=8 endpoint=full_rate request=under_load restart_transfers=4096 common_reset_during_recovery=0"
disconnect
exit
