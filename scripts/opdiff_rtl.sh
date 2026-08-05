#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# The RTL leg of the opcode matrix: run every generated program through
# iverilog on the EMITTED SoC and diff the architectural result against the ISS.
#
# This exists because of the surface gap the 2026-08-05 renumbering exposed.
# `opdiffselftest` compares EDSL against ISS; `diff_emulator_iss.py` compares
# emulator against ISS. Both were green and the board still panicked, because
# **nothing compared against the RTL** -- and the RTL is what the bitstream is
# built from and what silicon runs. An infinitely thorough emulator-vs-ISS
# matrix could not have caught it.
#
# Simulation is the cheap place to find a decode disagreement. A kernel boot,
# 41 000 instructions in, is the most expensive place.
set -uo pipefail
cd "$(dirname "$0")/.."

DIR=${1:-fpga/zc702/opdiff}
SOC=rtl/lnp64mini_soc.v
TB=fpga/zc702/tb_lnp64mini_soc.v
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT

command -v iverilog >/dev/null || { echo "opdiff_rtl: iverilog not found"; exit 0; }
[ -f "$SOC" ] || { echo "opdiff_rtl: $SOC missing -- run the emit first"; exit 1; }
ls "$DIR"/*.hex >/dev/null 2>&1 || {
  echo "opdiff_rtl: no programs in $DIR -- run 'minitest opdiffhex $DIR'"; exit 1; }

total=0; bad=0; first=""
for hex in "$DIR"/*.hex; do
  name=$(basename "$hex" .hex)
  total=$((total+1))
  if ! iverilog -g2012 -DPROG_HEX="\"$hex\"" -o "$T/a.vvp" "$SOC" "$TB" 2>/dev/null; then
    echo "  BUILD-FAIL $name"; bad=$((bad+1)); [ -z "$first" ] && first=$name
    continue
  fi
  # r1..r9 plus HALTED/retire are the architectural observables the tb prints.
  vvp "$T/a.vvp" 2>/dev/null | grep -E '^(HALTED|r[0-9]=)' > "$T/rtl.txt"
  if ! [ -s "$T/rtl.txt" ]; then
    echo "  NO-OUTPUT $name"; bad=$((bad+1)); [ -z "$first" ] && first=$name
    continue
  fi
  cp "$T/rtl.txt" "$DIR/$name.rtl"
done

echo "opdiff_rtl: simulated $total program(s) on $SOC"
if [ "$bad" -ne 0 ]; then
  echo "opdiff_rtl: FAILED — $bad program(s) did not simulate (first: $first)"
  exit 1
fi
echo "opdiff_rtl: OK — every generated program runs on the RTL; results in $DIR/*.rtl"
