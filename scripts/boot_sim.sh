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
# register file, and the guest console ring.
#
# ALWAYS RUN THE KNOWN-GOOD IMAGE ALONGSIDE. This tb models DDR and nothing
# else, and it diverges from the board: measured 2026-08-07, both the image
# that PASSED on silicon and a new image reach 2,207,545 cycles / 181,779
# retires and then hit the same `subr_vmem.c` quantum assertion, which the
# real board does not hit. So a panic here is only evidence when the baseline
# image does NOT produce it. What the tb is good for is the first ~180k
# retires, where it is faithful and where it caught the sel_cond defect at
# 41,550 -- comparison against a baseline, not an absolute verdict.
#
# (Depth before the window guard was ~1.34M cycles: out-of-window reads -- GEM
# MMIO at 0xE000_B000 -- indexed past the DDR array, X reached o_halted, and
# the run ended looking like a clean halt. Guarded now; the remaining
# divergence is unidentified and is the next thing to chase if this tool is
# wanted deeper than a boot's first phase.)
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
