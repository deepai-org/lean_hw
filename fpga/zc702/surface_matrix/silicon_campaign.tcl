# Self-checking ZC702 silicon campaign for the Loom multiclock surface matrix.
# Required environment: LOOM_ROOT, SURFACE_BITSTREAM, SURFACE_RTL_SHA256.

foreach required {LOOM_ROOT SURFACE_BITSTREAM SURFACE_RTL_SHA256} {
  if {![info exists ::env($required)] || $::env($required) eq ""} {
    error "missing required environment variable $required"
  }
}
set mode short
if {[info exists ::env(SURFACE_MODE)]} { set mode $::env(SURFACE_MODE) }
if {$mode ni {short soak}} { error "SURFACE_MODE must be short or soak" }
set server tcp:127.0.0.1:3121
if {[info exists ::env(SURFACE_HW_SERVER)]} { set server $::env(SURFACE_HW_SERVER) }

proc fail {message} {
  puts stderr "SURFACE_MATRIX_SILICON_FAIL $message"
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
  # A command is an epoch toggle crossing into both unrelated domains.  Keep
  # each state stable for many clock edges so no domain can miss two toggles.
  after 25
  expect_eq "command readback index=$index" [rd $index] $value
}
proc xor_digest {count} {
  set last [expr {$count - 1}]
  switch [expr {$last & 3}] {
    0 { return $last }
    1 { return 1 }
    2 { return [expr {$last + 1}] }
    3 { return 0 }
  }
}
proc wait_lane {base lane target timeout_ms} {
  set elapsed 0
  while {$elapsed < $timeout_ms} {
    set value [rd [expr {$base + $lane}]]
    if {[expr {$value & 0xffffffff}] >= $target} { return $value }
    after 20
    incr elapsed 20
  }
  fail "timeout base=$base lane=$lane target=$target last=[rd [expr {$base + $lane}]]"
}
proc verify_zero_state {label} {
  after 50
  for {set lane 0} {$lane < 8} {incr lane} {
    expect_eq "$label accepted lane=$lane" [rd [expr {16 + $lane}]] 0
    expect_eq "$label delivered lane=$lane" [rd [expr {24 + $lane}]] 0
    expect_eq "$label expected-sequence lane=$lane" [rd [expr {80 + $lane}]] 0
  }
  expect_eq "$label data errors" [rd 40] 0
  expect_eq "$label gap errors" [rd 41] 0
}
proc reset_empty {label} {
  command 1 4
  verify_zero_state $label
}
proc begin_epoch {limit prefill} {
  command 2 $limit
  if {$prefill} {
    command 1 1
    after 25
  }
  command 1 3
}
proc verify_complete {label limit require_backpressure require_stall} {
  wait_lane 24 7 $limit 300000
  command 1 0
  after 50
  set expected_digest [xor_digest $limit]
  expect_eq "$label data errors" [rd 40] 0
  expect_eq "$label qualified full-rate gap errors" [rd 41] 0
  for {set lane 0} {$lane < 8} {incr lane} {
    expect_eq "$label accepted lane=$lane" [rd [expr {16 + $lane}]] $limit
    expect_eq "$label delivered lane=$lane" [rd [expr {24 + $lane}]] $limit
    expect_eq "$label expected-sequence lane=$lane" [rd [expr {80 + $lane}]] $limit
    expect_eq "$label digest lane=$lane" [rd [expr {32 + $lane}]] $expected_digest
    if {$require_backpressure && [rd [expr {56 + $lane}]] == 0} {
      fail "$label lane=$lane did not observe source backpressure"
    }
    if {$require_stall && [rd [expr {64 + $lane}]] == 0} {
      fail "$label lane=$lane did not observe checker pause"
    }
  }
  foreach lane {3 5 7} {
    expect_eq "$label full-rate supply gaps lane=$lane" [rd [expr {48 + $lane}]] 0
  }
  puts "SURFACE_MATRIX_CAMPAIGN_PASS campaign=$label transfers_per_lane=$limit"
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

set continuous_limit 1000000
if {$mode eq "soak"} { set continuous_limit 100000000 }
reset_empty continuous_empty_reset
begin_epoch $continuous_limit 1
verify_complete continuous $continuous_limit 1 1

# Exercise checker and producer pauses without manufacturing a false full-rate
# supply failure: stop the checker first, then the producer; restart in reverse.
reset_empty pause_reset
command 2 $continuous_limit
command 1 3
wait_lane 24 7 [expr {$continuous_limit / 8}] 300000
command 1 1
after 25
command 1 0
after 25
command 1 1
after 25
command 1 3
verify_complete pauses $continuous_limit 1 1

# Coordinated common reset while all lanes are full/backpressured.
reset_empty reset_full_setup
command 2 4096
command 1 1
after 50
for {set lane 0} {$lane < 8} {incr lane} {
  if {[rd [expr {56 + $lane}]] == 0} { fail "reset-full lane=$lane was not backpressured" }
}
command 1 4
verify_zero_state reset_full

# Coordinated common reset with traffic active at both crossings, followed by
# the required clean independent-edge release and a complete fresh epoch.
command 2 4096
command 1 3
wait_lane 24 7 128 30000
command 1 4
verify_zero_state reset_under_load
begin_epoch 4096 1
verify_complete reset_restart 4096 1 1

puts "SURFACE_MATRIX_SILICON_PASS mode=$mode lanes=8 depths=2,4,8,16 endpoints=ordinary,full_rate"
disconnect
exit
