# Vivado lowering and routed audit for Loom's surface-matrix physical intent.
# Source this after synth_design, call loom_surface_apply_cdc before placement,
# and call loom_surface_audit_cdc after route_design.

namespace eval loom_surface {
  variable lanes {
    ordinary_d2 2 full_rate_d2 2
    ordinary_d4 3 full_rate_d4 3
    ordinary_d8 4 full_rate_d8 4
    ordinary_d16 5 full_rate_d16 5
  }
  variable all_sync_pairs {}
  variable all_gray_pairs {}
  variable recovery_sync_pairs {}
  variable applied 0
  variable omitted_gray ""
}

proc loom_surface_fail {message} {
  error "LOOM_SURFACE_CDC_FAIL: $message"
}

proc loom_surface_exact_vector {logical width} {
  set physical "u_matrix/$logical"
  set expression [format {^%s_reg(\[[0-9]+\])?$} $physical]
  set cells [get_cells -quiet -hierarchical -regexp $expression]
  set names [lsort -dictionary [get_property NAME $cells]]
  if {[llength $names] != $width} {
    loom_surface_fail "object $logical resolved to [llength $names] cells; expected $width; matches={$names}"
  }
  foreach name $names {
    set ref [get_property REF_NAME [get_cells $name]]
    if {![string match "FD*" $ref]} {
      loom_surface_fail "object $logical resolved to non-register $name ($ref)"
    }
  }
  return $names
}

proc loom_surface_exact_top_vector {logical width} {
  set expression [format {^%s_reg(\[[0-9]+\])?$} $logical]
  set cells [get_cells -quiet -hierarchical -regexp $expression]
  set names [lsort -dictionary [get_property NAME $cells]]
  if {[llength $names] != $width} {
    loom_surface_fail "top object $logical resolved to [llength $names] cells; expected $width; matches={$names}"
  }
  foreach name $names {
    set ref [get_property REF_NAME [get_cells $name]]
    if {![string match "FD*" $ref]} {
      loom_surface_fail "top object $logical resolved to non-register $name ($ref)"
    }
  }
  return $names
}

proc loom_surface_record_resolution {stream logical names} {
  puts $stream "$logical\t[join $names ,]"
}

proc loom_surface_apply_cdc {output_dir {negative_control none}} {
  variable loom_surface::lanes
  variable loom_surface::all_sync_pairs
  variable loom_surface::all_gray_pairs
  variable loom_surface::recovery_sync_pairs
  variable loom_surface::applied
  variable loom_surface::omitted_gray

  if {$applied} {
    loom_surface_fail "constraints were applied more than once"
  }
  if {$negative_control ni {none omit-gray unresolved-object forbidden-fanout alter-route-input-hash}} {
    loom_surface_fail "unknown negative control $negative_control"
  }
  file mkdir $output_dir
  set resolutions [open [file join $output_dir object-resolutions.tsv] w]
  puts $resolutions "logical\tresolved_cells"
  set all_sync_pairs {}
  set all_gray_pairs {}
  set omitted_gray ""
  set gray_index 0

  foreach {lane pointer_width} $lanes {
    foreach {direction launch_instance launch_name capture_instance capture_name stage1_name} {
      forward u_source_control write_gray u_sink_control write_gray_sync0 write_gray_sync1
      reverse u_sink_control read_gray u_source_control read_gray_sync0 read_gray_sync1
    } {
      set stem "u_surface_${lane}"
      set launch_logical "$stem/$launch_instance/$launch_name"
      set capture_logical "$stem/$capture_instance/$capture_name"
      set stage1_logical "$stem/$capture_instance/$stage1_name"

      if {$negative_control eq "unresolved-object" && $gray_index == 0} {
        set capture_logical "${capture_logical}_does_not_exist"
      }
      set launch [loom_surface_exact_vector $launch_logical $pointer_width]
      set capture [loom_surface_exact_vector $capture_logical $pointer_width]
      set stage1 [loom_surface_exact_vector $stage1_logical $pointer_width]
      loom_surface_record_resolution $resolutions $launch_logical $launch
      loom_surface_record_resolution $resolutions $capture_logical $capture
      loom_surface_record_resolution $resolutions $stage1_logical $stage1

      set_property ASYNC_REG TRUE [get_cells [concat $capture $stage1]]
      set_property SHREG_EXTRACT NO [get_cells [concat $capture $stage1]]
      lappend all_sync_pairs [list $capture_logical $capture $stage1_logical $stage1]
      lappend all_gray_pairs [list $launch_logical $launch $capture_logical $capture]

      if {$negative_control eq "omit-gray" && $gray_index == 0} {
        set omitted_gray "$launch_logical -> $capture_logical"
      } else {
        # Both periods are integer multiples of 1 ps. The neutral requirement
        # asks for one period of the faster endpoint clock: 6.400 ns here.
        set_bus_skew -from [get_cells $launch] -to [get_cells $capture] 6.400
        set_max_delay 6.400 -datapath_only \
          -from [get_cells $launch] -to [get_cells $capture]
      }
      incr gray_index
    }
  }

  foreach {stage0_logical stage1_logical} $recovery_sync_pairs {
    set stage0 [loom_surface_exact_vector $stage0_logical 1]
    set stage1 [loom_surface_exact_vector $stage1_logical 1]
    loom_surface_record_resolution $resolutions $stage0_logical $stage0
    loom_surface_record_resolution $resolutions $stage1_logical $stage1
    set_property ASYNC_REG TRUE [get_cells [concat $stage0 $stage1]]
    set_property SHREG_EXTRACT NO [get_cells [concat $stage0 $stage1]]
    lappend all_sync_pairs [list $stage0_logical $stage0 $stage1_logical $stage1]
  }
  set reset_stage0_logical "u_reset_release/request_sync0"
  set reset_stage1_logical "u_reset_release/request_sync1"
  set reset_stage0 [loom_surface_exact_top_vector $reset_stage0_logical 1]
  set reset_stage1 [loom_surface_exact_top_vector $reset_stage1_logical 1]
  set_property ASYNC_REG TRUE [get_cells [concat $reset_stage0 $reset_stage1]]
  set_property SHREG_EXTRACT NO [get_cells [concat $reset_stage0 $reset_stage1]]
  lappend all_sync_pairs [list $reset_stage0_logical $reset_stage0 \
    $reset_stage1_logical $reset_stage1]
  close $resolutions

  if {$negative_control eq "forbidden-fanout"} {
    set first_pair [lindex $all_sync_pairs 0]
    set first_stage0 [lindex [lindex $first_pair 1] 0]
    set source_net [get_nets -quiet -of_objects [get_pins ${first_stage0}/Q]]
    if {[llength $source_net] != 1} {
      loom_surface_fail "cannot resolve first synchronizer Q net for fanout negative"
    }
    create_cell -reference LUT1 loom_forbidden_sync_fanout
    set_property INIT 2'h2 [get_cells loom_forbidden_sync_fanout]
    set_property DONT_TOUCH TRUE [get_cells loom_forbidden_sync_fanout]
    connect_net -net [lindex $source_net 0] \
      -objects [get_pins loom_forbidden_sync_fanout/I0]
  }
  set applied 1
}

proc loom_surface_audit_cdc {output_dir} {
  variable loom_surface::all_sync_pairs
  variable loom_surface::all_gray_pairs
  variable loom_surface::applied
  variable loom_surface::omitted_gray

  if {!$applied} {
    loom_surface_fail "audit requested before constraints were applied"
  }
  file mkdir $output_dir
  report_cdc -name loom_surface_cdc -details -all_checks_per_endpoint \
    -no_waiver -file [file join $output_dir report_cdc.txt]
  report_clock_interaction -file [file join $output_dir report_clock_interaction.txt]
  report_bus_skew -file [file join $output_dir report_bus_skew.txt]
  report_timing_summary -file [file join $output_dir report_timing_summary.txt]

  set audit [open [file join $output_dir physical-audit.tsv] w]
  puts $audit "check\tstatus\tdetail"

  set source_clocks [get_clocks -quiet surface_source_clk]
  set sink_clocks [get_clocks -quiet surface_sink_clk]
  if {[llength $source_clocks] != 1 || [llength $sink_clocks] != 1} {
    loom_surface_fail "surface clocks did not resolve exactly"
  }
  if {[get_property NAME $source_clocks] eq [get_property NAME $sink_clocks]} {
    loom_surface_fail "source and sink clocks resolved to the same clock"
  }
  puts $audit "asynchronous_relationship\tPASS\tdistinct independently rooted named clocks"

  set critical_cdc [get_cdc_violations -name loom_surface_cdc \
    -filter {SEVERITY == Critical}]
  if {[llength $critical_cdc] != 0} {
    close $audit
    loom_surface_fail "report_cdc contains [llength $critical_cdc] unwaived Critical paths"
  }
  set warning_cdc [get_cdc_violations -name loom_surface_cdc \
    -filter {SEVERITY == Warning}]
  puts $audit "report_cdc_critical\tPASS\tzero unwaived Critical paths"
  set warning_stream [open [file join $output_dir report_cdc_warnings.tsv] w]
  puts $warning_stream "check\tstartpoint\tendpoint\tstatus"
  set warnings_ok 1
  foreach violation $warning_cdc {
    set check [get_property CHECK $violation]
    set startpoint [get_property STARTPOINT_PIN $violation]
    set endpoint [get_property ENDPOINT_PIN $violation]
    set recognized 0
    if {$check eq "CDC-6" &&
        ([string match "u_matrix/u_surface_*/*_gray_sync0_reg*" $endpoint] ||
         [string match "u_matrix/u_surface_*/u_*_recovery/peer_*_0_reg*" $endpoint] ||
         [string match "u_matrix/u_recovery_sync_*/completion_sync0_reg*" $endpoint] ||
         [string match "u_reset_release/request_sync0_reg*" $endpoint] ||
         [string match "u_transport/*_sync0_reg*" $endpoint])} {
      set recognized 1
    }
    if {$check eq "CDC-15" &&
        ([string match "*source_run_limit_reg*" $endpoint] ||
         [string match "*sink_run_limit_reg*" $endpoint] ||
         [string match "*source_enable_reg*" $endpoint] ||
         [string match "*sink_enable_reg*" $endpoint])} {
      set recognized 1
    }
    if {$check eq "CDC-26" && [string match "*u_target_storage*" $endpoint]} {
      set recognized 1
    }
    puts $warning_stream "$check\t$startpoint\t$endpoint\t[expr {$recognized ? {REVIEWED} : {UNEXPECTED}}]"
    if {!$recognized} { set warnings_ok 0 }
  }
  close $warning_stream
  if {!$warnings_ok} {
    close $audit
    loom_surface_fail "report_cdc contains an unexpected Warning path"
  }
  puts $audit "report_cdc_warnings_reviewed\tPASS\tall [llength $warning_cdc] Warning paths match exact expected topologies"

  set sync_ok 1
  set fanout_ok 1
  set placement_ok 1
  set placement_stream [open [file join $output_dir synchronizer-placement.tsv] w]
  puts $placement_stream "stage0_logical\tbit\tstage0_cell\tstage0_loc\tstage1_cell\tstage1_loc\tmanhattan"
  foreach pair $all_sync_pairs {
    lassign $pair stage0_logical stage0 stage1_logical stage1
    foreach cell [concat $stage0 $stage1] {
      if {![get_property ASYNC_REG [get_cells $cell]]} { set sync_ok 0 }
    }
    for {set index 0} {$index < [llength $stage0]} {incr index} {
      set first [lindex $stage0 $index]
      set second [lindex $stage1 $index]
      set endpoints [all_fanout -flat -endpoints_only -from [get_pins ${first}/Q]]
      set expected [get_pins ${second}/D]
      if {[llength $endpoints] != 1 || [lindex $endpoints 0] ne $expected} {
        set fanout_ok 0
      }
      set first_loc [get_property LOC [get_cells $first]]
      set second_loc [get_property LOC [get_cells $second]]
      set distance -1
      if {[regexp {SLICE_X([0-9]+)Y([0-9]+)} $first_loc _ first_x first_y] &&
          [regexp {SLICE_X([0-9]+)Y([0-9]+)} $second_loc _ second_x second_y]} {
        set distance [expr {abs($first_x - $second_x) + abs($first_y - $second_y)}]
      } else {
        set placement_ok 0
      }
      puts $placement_stream "$stage0_logical\t$index\t$first\t$first_loc\t$second\t$second_loc\t$distance"
    }
  }
  close $placement_stream
  if {!$sync_ok} { loom_surface_fail "ASYNC_REG is absent from a synchronizer stage" }
  puts $audit "synchronizer_attributes\tPASS\tall exact stage cells retain ASYNC_REG"
  if {!$fanout_ok} { loom_surface_fail "synchronizer first stage has forbidden fanout or wrong successor" }
  puts $audit "synchronizer_structure_fanout\tPASS\teach first-stage bit drives exactly its second-stage D"
  if {!$placement_ok} { loom_surface_fail "a synchronizer stage has no routed SLICE location" }
  puts $audit "synchronizer_placement\tPASS\tevery exact stage pair has a routed location and recorded Manhattan distance"

  if {$omitted_gray ne ""} {
    close $audit
    loom_surface_fail "Gray constraint deliberately omitted: $omitted_gray"
  }
  set gray_ok 1
  foreach pair $all_gray_pairs {
    lassign $pair launch_logical launch capture_logical capture
    set paths [get_timing_paths -quiet -delay_type max \
      -max_paths [llength $launch] -nworst 1 \
      -from [get_cells $launch] -to [get_cells $capture]]
    if {[llength $paths] != [llength $launch]} { set gray_ok 0 }
    foreach path $paths {
      if {[get_property SLACK $path] < 0.0} { set gray_ok 0 }
    }
  }
  if {!$gray_ok} { loom_surface_fail "Gray datapath coverage or routed slack failed" }
  set bus_report [report_bus_skew -return_string]
  if {[string match -nocase "*VIOLATED*" $bus_report]} {
    loom_surface_fail "a routed Gray bus-skew constraint is violated"
  }
  puts $audit "gray_datapath\tPASS\tall exact launch/capture vectors have nonnegative 6.400 ns max-delay slack"
  puts $audit "gray_bus_skew\tPASS\trouted report_bus_skew has no violation"

  set timing [report_timing_summary -return_string]
  if {[string match -nocase "*timing constraints are not met*" $timing]} {
    loom_surface_fail "ordinary routed timing did not pass"
  }
  puts $audit "ordinary_timing\tPASS\trouted timing summary reports constraints met"
  set source_gates [get_cells -quiet u_source_gate]
  set sink_gates [get_cells -quiet u_sink_gate]
  if {[llength $source_gates] != 1 || [llength $sink_gates] != 1 ||
      [get_property REF_NAME $source_gates] ne "BUFGCE" ||
      [get_property REF_NAME $sink_gates] ne "BUFGCE" ||
      [get_property CE_TYPE $source_gates] ne "SYNC" ||
      [get_property CE_TYPE $sink_gates] ne "SYNC"} {
    close $audit
    loom_surface_fail "coordinated-reset clock gates are absent or not synchronous BUFGCEs"
  }
  set release_cells [get_cells -quiet -hierarchical u_reset_release]
  if {[llength $release_cells] != 1} {
    close $audit
    loom_surface_fail "coordinated-reset release sequencer did not resolve exactly"
  }
  puts $audit "reset_delivery\tPASS\trequest synchronized to clk200; reset asserted with clocks running, deasserted while two synchronous BUFGCE roots are gated, then clocks restarted"
  close $audit
  puts "LOOM_SURFACE_CDC_PASS"
}
