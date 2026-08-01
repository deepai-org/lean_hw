#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# The Layer-2 (Engine) ladder for the LNP64 §2.2 capability machine:
#
#   1. FastEval acceptance selftest        (D18 — the verified evaluator IS the oracle)
#   2. D19 sync-read / BRAM shape report + MemWriteWF port order + composition guard
#   3. emit rtl/capwalk.v, rtl/lnp64mini_cap.v, and the behavioural DDR images
#   4. iverilog: the engine ladder against a HOSTILE behavioural DDR, diffed
#      against the Lean oracle byte for byte (includes the three fill attacks)
#   5. regression: lnp64mini{,_soc,_dual}.v and lnp64mini_epoch.v re-emit
#      byte-identically
set -euo pipefail
cd "$(dirname "$0")/.."
Z=fpga/zc702
T=${TMPDIR:-/tmp}/capwalk_ladder.$$
mkdir -p "$T"
trap 'rm -rf "$T"' EXIT

echo "### 1. FastEval selftest"
lake env lean --run Machines/CapWalk/Emit.lean selftest

echo "### 2. D19 + MemWriteWF report"
lake env lean --run Machines/CapWalk/Emit.lean d19

echo "### 3. emit"
lake env lean --run Machines/CapWalk/Emit.lean engine
lake env lean --run Machines/CapWalk/Emit.lean ddr
lake env lean --run Machines/CapWalk/Emit.lean soc

echo "### 4. iverilog: the engine ladder vs the Lean oracle (hostile DDR)"
lake env lean --run Machines/CapWalk/Emit.lean predict > "$T/oracle.txt"
iverilog -g2012 -o "$T/cw.vvp" rtl/capwalk.v "$Z/tb_capwalk.v"
vvp "$T/cw.vvp" | grep -v 'finish called' > "$T/rtl.txt"
diff "$T/oracle.txt" "$T/rtl.txt"
echo "capwalk_ladder: iverilog == FastEval oracle (byte-identical)"
# The three attacks must actually have fired at the RTL, not merely agreed.
test "$(grep -c 'rc=4' "$T/rtl.txt")" -ge 5
grep -q 'fv=1 fs=6' "$T/rtl.txt"   # A1 corruption
grep -q 'fv=1 fs=7' "$T/rtl.txt"   # A2 substitution
grep -q 'fv=1 fs=5' "$T/rtl.txt"   # A3 cross-epoch replay
grep -q 'faults=3' "$T/rtl.txt"
echo "capwalk_ladder: corruption, substitution and replay all fail-stopped at the RTL"

echo "### 5. regression: the existing designs re-emit byte-identically"
REGRESS="rtl/lnp64mini.v rtl/lnp64mini_soc.v rtl/lnp64mini_dual.v \
         rtl/epochengine.v rtl/epochengine_tiny.v rtl/lnp64mini_epoch.v"
for f in $REGRESS; do
  [ -f "$f" ] || continue
  cp "$f" "$T/$(basename "$f").before"
done
lake env lean --run Machines/Lnp64mini/Emit.lean       >/dev/null
lake env lean --run Machines/Lnp64mini/Emit.lean soc   >/dev/null
lake env lean --run Machines/Lnp64mini/Emit.lean dual  >/dev/null
lake env lean --run Machines/Epoch/Emit.lean engine     >/dev/null
lake env lean --run Machines/Epoch/Emit.lean soc        >/dev/null
for f in $REGRESS; do
  [ -f "$T/$(basename "$f").before" ] || continue
  cmp "$f" "$T/$(basename "$f").before"
done

echo "capwalk_ladder: OK"
