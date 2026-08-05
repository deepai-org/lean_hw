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

total=0; bad=0; noexp=0; first=""

# The comparison drops `cycles=`: DDR latency is a parameter of the experiment,
# not an architectural fact, and a core that reached the same state in a
# different number of cycles has not misdecoded anything. Everything else the
# testbench prints -- HALTED, pc, retire, r1..r9, the zero-page word, and any
# TRAP line -- is compared exactly.
norm() { grep -E '^(TRAP|HALTED|r[0-9]=|dmem32=)' "$1" | sed 's/ cycles=[0-9]*//'; }

for hex in "$DIR"/*.hex; do
  name=$(basename "$hex" .hex)
  exp="$DIR/$name.exp"
  total=$((total+1))
  if ! [ -f "$exp" ]; then
    echo "  NO-EXPECTATION $name — re-run 'minitest opdiffhex $DIR'"
    noexp=$((noexp+1)); [ -z "$first" ] && first=$name
    continue
  fi
  if ! iverilog -g2012 -DPROG_HEX="\"$hex\"" -o "$T/a.vvp" "$SOC" "$TB" 2>/dev/null; then
    echo "  BUILD-FAIL $name"; bad=$((bad+1)); [ -z "$first" ] && first=$name
    continue
  fi
  vvp "$T/a.vvp" 2>/dev/null > "$T/raw.txt"
  norm "$T/raw.txt" > "$DIR/$name.rtl"
  if ! [ -s "$DIR/$name.rtl" ]; then
    echo "  NO-OUTPUT $name"; bad=$((bad+1)); [ -z "$first" ] && first=$name
    continue
  fi
  norm "$exp" > "$T/exp.txt"
  if ! diff -q "$DIR/$name.rtl" "$T/exp.txt" >/dev/null; then
    bad=$((bad+1)); [ -z "$first" ] && first=$name
    if [ "$bad" -le 5 ]; then
      echo "  MISMATCH $name  (RTL < , ISS > )"
      diff "$DIR/$name.rtl" "$T/exp.txt" | head -8 | sed 's/^/    /'
    fi
  fi
done

echo "opdiff_rtl: ran $total program(s) on $SOC, each diffed against the ISS"
if [ "$noexp" -ne 0 ]; then
  echo "opdiff_rtl: FAILED — $noexp program(s) had no .exp expectation"
  exit 1
fi
if [ "$bad" -ne 0 ]; then
  echo "opdiff_rtl: FAILED — RTL disagreed with the ISS on $bad program(s) (first: $first)"
  exit 1
fi
echo "opdiff_rtl: OK — RTL ≡ ISS on all $total generated programs"
