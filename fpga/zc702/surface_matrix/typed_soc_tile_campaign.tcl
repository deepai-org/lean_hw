# ZC702 silicon campaign for the Typed SoC Composition Tile.
foreach required {LOOM_ROOT TILE_BITSTREAM TILE_RTL_SHA256} {
  if {![info exists ::env($required)] || $::env($required) eq ""} {
    error "missing required environment variable $required"
  }
}
set server tcp:127.0.0.1:3121
if {[info exists ::env(TILE_HW_SERVER)]} { set server $::env(TILE_HW_SERVER) }

proc fail {message} {
  puts stderr "TYPED_SOC_TILE_SILICON_FAIL $message"
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
proc wait_word {index target timeout_ms} {
  set elapsed 0
  while {$elapsed < $timeout_ms} {
    set value [rd $index]
    if {[expr {$value & 0xffffffff}] >= $target} { return $value }
    after 20
    incr elapsed 20
  }
  fail "timeout index=$index target=$target last=[rd $index]"
}
proc replay_digest {limit gap_word} {
  set gap_sequence [expr {$gap_word & 0xfffff}]
  set gap_client [expr {($gap_word >> 20) & 1}]
  set digest 0
  array set memory {}
  for {set client 0} {$client < 2} {incr client} {
    set salt [expr {$client ? 0x2468ace0 : 0x13579bdf}]
    for {set sequence 0} {$sequence < $limit} {incr sequence} {
      if {$client == $gap_client && $sequence == $gap_sequence} { continue }
      set address [expr {$sequence & 0xff}]
      set key "$client,$address"
      set old [expr {[info exists memory($key)] ? $memory($key) : 0}]
      set result $old
      if {(($sequence >> 8) & 1) != 0} {
        set data [expr {($sequence ^ $salt) & 0xffffffff}]
        set mask [expr {$sequence & 0xf}]
        for {set byte 0} {$byte < 4} {incr byte} {
          if {(($mask >> $byte) & 1) != 0} {
            set byte_mask [expr {0xff << (8 * $byte)}]
            set result [expr {(($result & ~$byte_mask) | ($data & $byte_mask)) & 0xffffffff}]
          }
        }
        set memory($key) $result
      }
      set digest [expr {($digest ^ $result ^ $sequence) & 0xffffffff}]
    }
  }
  return $digest
}
proc verify_reset_state {label} {
  after 50
  foreach index {17 18 19 22 23 24 25 32 40 56 57 58 80 81 82 83} {
    expect_eq "$label index=$index" [rd $index] 0
  }
}

connect -url $server
if {![info exists ::env(TILE_SKIP_PROGRAM)] || $::env(TILE_SKIP_PROGRAM) ne "1"} {
  targets -set -filter {name =~ "xc7z*"}
  fpga -file $::env(TILE_BITSTREAM)
  after 1000
}
set jtag_lib [file join $::env(LOOM_ROOT) fpga zc702 board jtag_lib.tcl]
if {![file exists $jtag_lib]} {
  set jtag_lib [file join $::env(LOOM_ROOT) test jtag_lib.tcl]
}
if {![file exists $jtag_lib]} { fail "could not locate jtag_lib.tcl" }
source $jtag_lib

if {[info exists ::env(TILE_DEBUG_SCAN)] && $::env(TILE_DEBUG_SCAN) eq "1"} {
  for {set index 0} {$index < 9} {incr index} {
    puts "TYPED_SOC_TILE_SCAN index=$index value=0x[hex32 [rd $index]]"
  }
}

expect_eq "transport magic" [rd 0] 0x54534354
scan [string range $::env(TILE_RTL_SHA256) 0 7] %x rtl_prefix
expect_eq "physical RTL hash prefix" [rd 3] $rtl_prefix
set status [rd 4]
if {($status & 4) == 0} { fail "independent clocks not ready status=0x[hex32 $status]" }
set core_hb [rd 5]
set memory_hb [rd 6]
after 50
if {[rd 5] == $core_hb} { fail "core clock heartbeat did not advance" }
if {[rd 6] == $memory_hb} { fail "memory clock heartbeat did not advance" }

# First establish genuine request/response residency using only read-tagged
# sequences. The evidence-shell holds make these states last long enough for
# JTAG to observe: bit 5 holds both memories while requests fill, then bit 4
# holds monitor consumption while responses fill.
command 2 200
command 1 0x23
wait_word 19 7 30000
command 1 0x13
wait_word 25 4 30000
set resident 0
for {set attempt 0} {$attempt < 500} {incr attempt} {
  set live [rd 48]
  if {($live & 0x7e) != 0} { set resident 1; break }
  after 2
}
if {!$resident} { fail "could not observe resident pipeline/request/response state" }
set resident_sent [rd 19]
set resident_records [rd 24]
set resident_contract_commits [rd 25]
set resident_internal_commits [rd 58]
if {$resident_sent <= $resident_contract_commits ||
    $resident_sent <= $resident_internal_commits} {
  fail "requests were not resident at both crossings sent=$resident_sent internal_commits=$resident_internal_commits contract_commits=$resident_contract_commits"
}
if {$resident_contract_commits <= $resident_records ||
    $resident_internal_commits <= $resident_records} {
  fail "responses were not resident at both crossings records=$resident_records internal_commits=$resident_internal_commits contract_commits=$resident_contract_commits"
}
if {[rd 80] >= 256 || [rd 81] >= 256} {
  fail "reset-under-load setup wrote memory before the clean replay boundary"
}
command 1 0x17
verify_reset_state reset_under_load

# Release on naturally skewed edges and run 500k transactions from each tagged
# source. One occupied pipeline flush is required and explicitly ledgered.
set per_source 500000
set expected_records 999999
command 2 $per_source
command 1 0x0b
wait_word 24 $expected_records 300000
command 1 0
after 100

expect_eq "sticky checker" [rd 40] 0
expect_eq "source A accepted" [rd 17] $per_source
expect_eq "source B accepted" [rd 18] $per_source
expect_eq "endpoint sent" [rd 19] $expected_records
expect_eq "arbiter grant A" [rd 22] $per_source
expect_eq "arbiter grant B" [rd 23] $per_source
expect_eq "checked records" [rd 24] $expected_records
expect_eq "contract lane commits" [rd 25] $expected_records
expect_eq "internal lane commits" [rd 58] $expected_records
expect_eq "flush discard ledger" [rd 57] 1
expect_eq "source A sequence" [rd 80] $per_source
expect_eq "source B sequence" [rd 81] $per_source
expect_eq "checker A sequence" [rd 82] $per_source
expect_eq "checker B sequence" [rd 83] $per_source
set gap_word [rd 64]
set expected_digest [replay_digest $per_source $gap_word]
expect_eq "response digest" [rd 32] $expected_digest
if {[rd 20] == 0 || [rd 21] == 0} { fail "producer pauses were not exercised" }
if {[rd 26] == 0 || [rd 27] == 0} { fail "memory/request backpressure was not exercised" }
if {[rd 31] == 0} { fail "response backpressure was not exercised" }
if {[rd 28] == 0 && [rd 29] == 0} {
  fail "response backpressure never propagated to either memory service"
}
if {[rd 56] == 0} { fail "arbiter contention was not exercised" }
set final_status [rd 48]
if {($final_status & 0x6) != 0x6} {
  fail "occupied flush was not executed and observed status=0x[hex32 $final_status]"
}

puts "TYPED_SOC_TILE_SILICON_PASS transfers=1000000 records=$expected_records digest=[hex32 $expected_digest] gap=[hex32 $gap_word]"
disconnect
exit
