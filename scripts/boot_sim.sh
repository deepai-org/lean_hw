#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# Boot the ACTUAL guest image on the emitted RTL in iverilog.
#
# The sel_cond defect survived three silicon campaigns of green gates and then
# fell in twenty seconds of this: a deterministic boot failure on the board is
# a $display away in simulation, and the board is the most expensive possible
# place to read one out. Run this BEFORE any board forensics on a boot failure,
# and after any change that alters the core's instruction semantics.
#
#   scripts/boot_sim.sh <text.hex> <data.hex> [cycles]
#
# The hexes are the assembler's flat-exec output (dev_cycle/fastload artifacts;
# leading '#' header lines are stripped here). Prints HALTED/pc/retire, the
# register file, and the guest console ring -- a panic message in the ring is a
# reproduction, full stop.
set -euo pipefail
cd "$(dirname "$0")/.."
TEXT=${1:?usage: boot_sim.sh <text.hex> <data.hex> [cycles]}
DATA=${2:?usage: boot_sim.sh <text.hex> <data.hex> [cycles]}
CYC=${3:-12000000}
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
grep -v '^#' "$TEXT" > "$T/text.hex"
grep -v '^#' "$DATA" > "$T/data.hex"
iverilog -g2012 -DTEXT_HEX="\"$T/text.hex\"" -DDATA_HEX="\"$T/data.hex\"" \
  -o "$T/boot.vvp" rtl/lnp64mini_soc.v fpga/zc702/tb_lnp64mini_boot.v
vvp "$T/boot.vvp"
