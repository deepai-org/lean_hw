#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
work_dir=$(mktemp -d /tmp/loom-surface-vivado-contract.XXXXXX)
trap 'rm -rf "$work_dir"' EXIT

LOOM_ROOT="$repo_root" lake -d "$repo_root" exe surfaceMatrixEvidence \
  "$work_dir/evidence" >/dev/null
LOOM_ROOT="$repo_root" lake -d "$repo_root" exe surfaceMatrixRecoveryEvidence \
  "$work_dir/recovery-evidence" >/dev/null
intent="$work_dir/evidence/clock_constraints.md"
[[ $(grep -c 'Treat `surface_source_clk` and `surface_sink_clk` as asynchronous clocks' "$intent") == 8 ]]
[[ $(grep -c 'Preserve and identify the ordered synchronizer chain' "$intent") == 16 ]]
[[ $(grep -c 'Constrain the .* coherent CDC bus' "$intent") == 16 ]]
[[ $(grep -c 'This clock must tick while reset is asserted' "$intent") == 2 ]]
recovery_intent="$work_dir/recovery-evidence/clock_constraints.md"
[[ $(grep -c 'Treat `surface_source_clk` and `surface_sink_clk` as asynchronous clocks' "$recovery_intent") == 1 ]]
[[ $(grep -c 'Preserve and identify the ordered synchronizer chain' "$recovery_intent") == 8 ]]
[[ $(grep -c '^# Recovery interface protocol' "$recovery_intent") == 1 ]]

if grep -q 'set_clock_groups' "$repo_root/fpga/zc702/surface_matrix/surface_matrix.xdc"; then
  echo "clock groups would override the Gray max-delay requirement" >&2
  exit 1
fi
grep -q 'get_pins u_source_gate/O' \
  "$repo_root/fpga/zc702/surface_matrix/surface_matrix.xdc"
grep -q 'get_pins u_sink_gate/O' \
  "$repo_root/fpga/zc702/surface_matrix/surface_matrix.xdc"

tclsh <<EOF
proc get_ports {args} { return port }
proc get_pins {args} { return pin }
proc set_property {args} {}
proc create_clock {args} {}
proc create_generated_clock {args} {}
source {$repo_root/fpga/zc702/surface_matrix/surface_matrix.xdc}
source {$repo_root/fpga/zc702/surface_matrix/surface_matrix_cdc.tcl}
if {[llength [namespace eval loom_surface {set lanes}]] != 16} {
  error {surface lane/width table is incomplete}
}
puts SURFACE_VIVADO_TCL_PARSE_PASS
EOF

for control in omit-gray unresolved-object forbidden-fanout alter-route-input-hash; do
  grep -q "$control" "$repo_root/fpga/zc702/surface_matrix/surface_matrix_cdc.tcl"
done
yosys -q -p "read_verilog -lib /usr/share/yosys/xilinx/cells_sim.v; \
  read_verilog -lib /usr/share/yosys/xilinx/cells_xtra.v; \
  read_verilog $work_dir/evidence/system.v \
    $repo_root/fpga/zc702/surface_matrix/surface_matrix_bscan.v \
    $repo_root/fpga/zc702/surface_matrix/surface_reset_release.v \
    $repo_root/fpga/zc702/surface_matrix/surface_matrix_top.v; \
  hierarchy -check -top surface_matrix_top; proc; check"
yosys -q -p "read_verilog -lib /usr/share/yosys/xilinx/cells_sim.v; \
  read_verilog -lib /usr/share/yosys/xilinx/cells_xtra.v; \
  read_verilog $work_dir/recovery-evidence/system.v \
    $repo_root/fpga/zc702/surface_matrix/surface_matrix_bscan.v \
    $repo_root/fpga/zc702/surface_matrix/surface_reset_release.v \
    $repo_root/fpga/zc702/surface_matrix/surface_recovery_top.v; \
  hierarchy -check -top surface_recovery_top; proc; check"
grep -q 'SURFACE_MATRIX_RTL_SHA_PREFIX' \
  "$repo_root/fpga/zc702/surface_matrix/build_vivado.tcl"
"$repo_root/scripts/test_surface_reset_release.sh"
echo "SURFACE_VIVADO_CONTRACT_PASS requirements=42 lanes=8 recovery=1 negatives=4"
