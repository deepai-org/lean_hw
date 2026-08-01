#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# D31 regression: eqcheck must REJECT the pre-fix epoch engine netlist.
#
# `Tests/fixtures/eqcheck/epochengine_prefix.{v,json.gz}` is the epoch engine
# as it was before commit b510caf -- the 512x3 `cell_flags` bank still carrying
# the occupancy bit as a NON-ZERO reset image -- together with the netlist
# yosys 0.33 produces from exactly that text. That bank is what silicon
# disagreed with (LOOM_GAPS.md D30, Machines/Epoch/EPOCH_SPEC.md E13): yosys
# maps it to distributed LUT RAM, whose image the configuration path does not
# deliver, and nothing in the flow says so.
#
# The pass condition of this script is that eqcheck FAILS on the fixture, and
# fails for the right reason, naming the bank. No board, no simulation.
#
# Requires cadical (the fixture netlist is checked in, so yosys is not needed).
set -euo pipefail
cd "$(dirname "$0")/.."

command -v cadical >/dev/null || { echo "eqcheck_memfixture: SKIP (cadical not installed)"; exit 0; }

FIX=Tests/fixtures/eqcheck
OUT=${EQCHECK_OUT:-scratch/eqcheck}
mkdir -p "$OUT"
gunzip -c "$FIX/epochengine_prefix.json.gz" > "$OUT/epochengine_prefix.json"

lake build eqcheck >/dev/null
set +e
.lake/build/bin/eqcheck "$FIX/epochengine_prefix.v" "$OUT/epochengine_prefix.json" \
  > "$OUT/memfixture.out" 2>&1
rc=$?
set -e

fail() { echo "eqcheck_memfixture: FAILED -- $1"; sed -n '1,40p' "$OUT/memfixture.out"; exit 1; }

[ "$rc" -ne 0 ] || fail "eqcheck ACCEPTED the pre-fix netlist (exit 0)"
grep -q "RESET IMAGE NOT DELIVERED for bank 'cell_flags'" "$OUT/memfixture.out" \
  || fail "eqcheck rejected the fixture, but not for the D30 reason"
grep -q "RAM64M" "$OUT/memfixture.out" \
  || fail "the verdict does not name the distributed-RAM primitive"
# Exactly one signal may differ: the defect, and nothing else.
grep -q "EQCHECK FAILED (1 of " "$OUT/memfixture.out" \
  || fail "more than the one known signal differs (see $OUT/memfixture.out)"

echo "eqcheck_memfixture: OK -- eqcheck reproduces D30 from the netlist alone:"
grep -A2 "RESET IMAGE NOT DELIVERED" "$OUT/memfixture.out" | sed 's/^/    /'
