if {![info exists ::env(LOOM_ROOT)] || ![info exists ::env(LOOM_EVIDENCE_DIR)] ||
    ![info exists ::env(LOOM_VIVADO_OUT)] || ![info exists ::env(LOOM_ROUTE_SEED)] ||
    ![info exists ::env(LOOM_RTL_SHA256)] ||
    ![info exists ::env(LOOM_ROUTE_INPUTS_SHA256)]} {
  error "Loom paths, seed, RTL hash, and route-input hash are required"
}

set root [file normalize $::env(LOOM_ROOT)]
set evidence [file normalize $::env(LOOM_EVIDENCE_DIR)]
set output [file normalize $::env(LOOM_VIVADO_OUT)]
set seed $::env(LOOM_ROUTE_SEED)
set negative none
if {[info exists ::env(LOOM_PHYSICAL_NEGATIVE)]} {
  set negative $::env(LOOM_PHYSICAL_NEGATIVE)
}
set variant matrix
if {[info exists ::env(LOOM_SURFACE_VARIANT)]} {
  set variant $::env(LOOM_SURFACE_VARIANT)
}
switch $variant {
  matrix {
    set top surface_matrix_top
    set top_file surface_matrix_top.v
    set bit_name surface_matrix.bit
  }
  registered-bram {
    set top surface_registered_bram_top
    set top_file surface_registered_bram_top.v
    set bit_name surface_registered_bram.bit
  }
  recovery {
    set top surface_recovery_top
    set top_file surface_recovery_top.v
    set bit_name surface_recovery.bit
  }
  default { error "unknown LOOM_SURFACE_VARIANT $variant" }
}
file mkdir $output

# Vivado does not expose a portable random-seed switch for place_design.
# Treat the evidence seed as a reproducible implementation strategy index;
# seeds 1..3 use AMD's recommended diverse Auto directives, and later values
# use named deterministic alternatives.
set directives {Auto_1 Auto_2 Auto_3 Explore AggressiveExplore ExtraNetDelay_high}
set place_directive [lindex $directives [expr {($seed - 1) % [llength $directives]}]]

read_verilog [file join $evidence system.v]
set rtl_sha_prefix [string range $::env(LOOM_RTL_SHA256) 0 7]
read_verilog -verilog_define "SURFACE_MATRIX_RTL_SHA_PREFIX=32'h$rtl_sha_prefix" \
  [file join $root fpga zc702 surface_matrix surface_matrix_bscan.v]
read_verilog [file join $root fpga zc702 surface_matrix surface_reset_release.v]
read_verilog [file join $root fpga zc702 surface_matrix $top_file]
synth_design -top $top -part xc7z020clg484-1 \
  -flatten_hierarchy none
read_xdc [file join $root fpga zc702 surface_matrix surface_matrix.xdc]
write_checkpoint -force [file join $output post_synth.dcp]
if {$variant eq "registered-bram"} {
  set brams [get_cells -quiet -hierarchical \
    -filter {REF_NAME == RAMB18E1 || REF_NAME == RAMB36E1}]
  if {[llength $brams] != 1} {
    error "LOOM_SURFACE_BRAM_INFERENCE_FAIL: expected exactly one RAMB18E1/RAMB36E1, found [llength $brams]"
  }
  set inference [open [file join $output storage-inference.tsv] w]
  puts $inference "logical\tcell\tprimitive"
  puts $inference "surface_ordinary_d4\t[get_property NAME $brams]\t[get_property REF_NAME $brams]"
  close $inference
}

source [file join $root fpga zc702 surface_matrix surface_matrix_cdc.tcl]
if {$variant eq "registered-bram"} {
  set loom_surface::lanes {ordinary_d4 3}
} elseif {$variant eq "recovery"} {
  set loom_surface::lanes {full_rate_d8 4}
  set loom_surface::recovery_sync_pairs {
    u_surface_full_rate_d8/u_source_recovery/peer_request_0
      u_surface_full_rate_d8/u_source_recovery/peer_request_1
    u_surface_full_rate_d8/u_source_recovery/peer_acknowledge_0
      u_surface_full_rate_d8/u_source_recovery/peer_acknowledge_1
    u_surface_full_rate_d8/u_sink_recovery/peer_request_0
      u_surface_full_rate_d8/u_sink_recovery/peer_request_1
    u_surface_full_rate_d8/u_sink_recovery/peer_acknowledge_0
      u_surface_full_rate_d8/u_sink_recovery/peer_acknowledge_1
    u_recovery_sync_source_full_rate_d8_surface_full_rate_d8_dst_done/completion_sync0
      u_recovery_sync_source_full_rate_d8_surface_full_rate_d8_dst_done/completion_sync1
    u_recovery_sync_sink_full_rate_d8_surface_full_rate_d8_src_done/completion_sync0
      u_recovery_sync_sink_full_rate_d8_surface_full_rate_d8_src_done/completion_sync1
  }
}
loom_surface_apply_cdc $output $negative

opt_design
place_design -directive $place_directive
phys_opt_design -directive Explore
route_design -directive Explore
write_checkpoint -force [file join $output routed.dcp]
loom_surface_audit_cdc $output
write_bitstream -force [file join $output $bit_name]

set worst_paths [get_timing_paths -quiet -delay_type max -max_paths 1]
if {[llength $worst_paths] != 1} {
  error "LOOM_SURFACE_TIMING_FAIL: no routed setup timing path resolved"
}
set worst_slack [get_property SLACK [lindex $worst_paths 0]]

set route_status [open [file join $output route-status.tsv] w]
puts $route_status "field\tvalue"
puts $route_status "part\txc7z020clg484-1"
puts $route_status "seed\t$seed"
puts $route_status "place_directive\t$place_directive"
puts $route_status "negative_control\t$negative"
puts $route_status "variant\t$variant"
puts $route_status "vivado_version\t[version -short]"
puts $route_status "rtl_sha256\t$::env(LOOM_RTL_SHA256)"
if {$negative eq "alter-route-input-hash"} {
  puts $route_status "route_inputs_sha256\tffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
} else {
puts $route_status "route_inputs_sha256\t$::env(LOOM_ROUTE_INPUTS_SHA256)"
}
puts $route_status "worst_setup_slack_ns\t$worst_slack"
puts $route_status "status\tPASS"
close $route_status
puts "LOOM_SURFACE_VIVADO_PASS seed=$seed"
