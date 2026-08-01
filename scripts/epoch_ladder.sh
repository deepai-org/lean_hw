#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# The Layer-2 (Engine) ladder for the LNP64 §3 epoch machine:
#
#   1. FastEval acceptance selftest        (D18 — the verified evaluator IS the oracle)
#   2. D19 sync-read / BRAM shape report + composition guard
#   3. emit rtl/epochengine{,_tiny}.v and rtl/lnp64mini_epoch.v
#   4. iverilog: the engine ladder, diffed against the Lean oracle byte for byte
#   5. iverilog: the cross-core demo — core 0 bumps, core 1 sees -STALE
#   6. regression: lnp64mini{,_soc,_dual}.v re-emit byte-identically
set -euo pipefail
cd "$(dirname "$0")/.."
Z=fpga/zc702
T=${TMPDIR:-/tmp}/epoch_ladder.$$
mkdir -p "$T"
trap 'rm -rf "$T"' EXIT

echo "### 1. FastEval selftest"
lake env lean --run Machines/Epoch/Emit.lean selftest

echo "### 2. D19 report"
lake env lean --run Machines/Epoch/Emit.lean d19

echo "### 3. emit"
lake env lean --run Machines/Epoch/Emit.lean engine
lake env lean --run Machines/Epoch/Emit.lean soc

echo "### 4. iverilog: engine ladder vs the Lean oracle"
lake env lean --run Machines/Epoch/Emit.lean predict > "$T/oracle.txt"
iverilog -g2012 -o "$T/eng.vvp" rtl/epochengine.v rtl/epochengine_tiny.v \
  $Z/tb_epochengine.v
vvp "$T/eng.vvp" | grep -v 'ACKVEC_MAX\|finish called' > "$T/rtl.txt"
diff "$T/oracle.txt" "$T/rtl.txt"
echo "epoch_ladder: iverilog == FastEval oracle (byte-identical)"

echo "### 5. iverilog: the cross-core demo"
iverilog -g2012 -DPROG_HEX0="\"$Z/epoch0.hex\"" -DPROG_HEX1="\"$Z/epoch1.hex\"" \
  -o "$T/soc.vvp" rtl/lnp64mini_epoch.v $Z/tb_lnp64mini_epoch.v
vvp "$T/soc.vvp" | grep -E '^EPOCH|^CYCLES' | tee "$T/demo.txt"
grep -q 'EPOCH DEMO OK' "$T/demo.txt"

echo "### 6. regression: the existing designs re-emit byte-identically"
for f in rtl/lnp64mini.v rtl/lnp64mini_soc.v rtl/lnp64mini_dual.v; do
  cp "$f" "$T/$(basename "$f").before"
done
lake env lean --run Machines/Lnp64mini/Emit.lean          >/dev/null
lake env lean --run Machines/Lnp64mini/Emit.lean soc      >/dev/null
lake env lean --run Machines/Lnp64mini/Emit.lean dual     >/dev/null
for f in rtl/lnp64mini.v rtl/lnp64mini_soc.v rtl/lnp64mini_dual.v; do
  cmp "$f" "$T/$(basename "$f").before"
done
echo "epoch_ladder: OK"
