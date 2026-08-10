# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
# Shared Tcl-side board-host paths. Shell wrappers may override the root.

set LOOM_TEST_DIR [file normalize [file dirname [info script]]]
if {[info exists ::env(LOOM_BOARD_ROOT)]} {
  set LOOM_BOARD_ROOT [file normalize $::env(LOOM_BOARD_ROOT)]
} else {
  set LOOM_BOARD_ROOT [file normalize [file join $LOOM_TEST_DIR ..]]
}
if {[info exists ::env(LOOM_OXC7_DIR)]} {
  set LOOM_OXC7_DIR [file normalize $::env(LOOM_OXC7_DIR)]
} else {
  set LOOM_OXC7_DIR [file join $LOOM_BOARD_ROOT oxc7]
}
if {[info exists ::env(LNP64_ROOT)]} {
  set LNP64_ROOT [file normalize $::env(LNP64_ROOT)]
} else {
  set LNP64_ROOT [file join $LOOM_BOARD_ROOT lnp64]
}
if {[info exists ::env(LOOM_BOARD_STATE_DIR)]} {
  set LOOM_STATE_DIR [file normalize $::env(LOOM_BOARD_STATE_DIR)]
} else {
  set LOOM_STATE_DIR [file join $LOOM_BOARD_ROOT board-state]
}
set LOOM_JTAG_LIB [file join $LOOM_TEST_DIR jtag_lib.tcl]
set LOOM_DEBUG_MAP [file join $LOOM_TEST_DIR lnp64mini_debug_map.tcl]
