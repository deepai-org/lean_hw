#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# Emit EVERY design in the repo. The single place that knows the producer list.
#
# There is no single producer: `lake exe emit` writes some designs, and each
# machine's `Emit.lean` writes others, with per-design arguments. On 2026-08-07
# that cost three separate mismeasurements in one session, all the same shape:
# change a design, run the emit command you happen to remember, measure the
# result, and report a number computed from RTL that predates the change.
#
#   * an area A/B for NT=8 that synthesised the NT=32 netlist twice -- the two
#     cell censuses came back byte-identical, which was the only tell;
#   * a "verified" emit that left `rtl/lnp64mini.v` with 32 thread registers
#     in a design that had 8, because `lake exe emit` does not write that file;
#   * (on the board host, same class) a bitstream built from a five-hour-old
#     netlist, fixed separately in `fpga/zc702/board/build_oxc7_seed.sh`.
#
# `check_stale.sh` §2 always had the full list and would have caught all three.
# The failure was never the gate; it was reaching past it with a hand-picked
# subset. So the list lives here, both callers use it, and adding a design
# means adding it in exactly one place.
#
#   scripts/emit_all.sh           # emit everything
#   scripts/emit_all.sh --check   # non-zero if any .v differs from a fresh emit
set -uo pipefail
cd "$(dirname "$0")/.."
CHECK_ONLY=0; [ "${1:-}" = "--check" ] && CHECK_ONLY=1

if [ "$CHECK_ONLY" = 1 ]; then
  T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
  for f in rtl/*.v; do [ -f "$f" ] && cp "$f" "$T/$(basename "$f")"; done
fi

lake build >/dev/null 2>&1 || { echo "emit_all: lake build FAILED"; exit 1; }

# --- the producer list. Add new designs HERE and nowhere else. ---
lake exe emit >/dev/null 2>&1 || { echo "emit_all: lake exe emit FAILED"; exit 1; }
for t in "" soc dual; do
  lake env lean --run Machines/Lnp64mini/Emit.lean $t >/dev/null 2>&1 \
    || { echo "emit_all: Lnp64mini/Emit.lean '$t' FAILED"; exit 1; }
done
lake env lean --run Machines/Epoch/Emit.lean soc    >/dev/null 2>&1 || { echo "emit_all: Epoch soc FAILED"; exit 1; }
lake env lean --run Machines/Epoch/Emit.lean engine >/dev/null 2>&1 || { echo "emit_all: Epoch engine FAILED"; exit 1; }
lake env lean --run Machines/CapWalk/Emit.lean soc  >/dev/null 2>&1 || { echo "emit_all: CapWalk soc FAILED"; exit 1; }

if [ "$CHECK_ONLY" = 1 ]; then
  FAIL=0
  for f in rtl/*.v; do
    b="$T/$(basename "$f")"
    if [ -f "$b" ]; then
      cmp -s "$f" "$b" || { printf '  STALE  %s\n' "$(basename "$f")"; FAIL=1; }
    else printf '  NEW    %s (was not on disk before)\n' "$(basename "$f")"; FAIL=1; fi
  done
  [ "$FAIL" = 0 ] && echo "emit_all: OK — every .v matches a fresh emit" \
                  || echo "emit_all: STALE — the RTL on disk is not what the sources emit"
  exit "$FAIL"
fi
echo "emit_all: OK — $(ls rtl/*.v | wc -l) designs emitted"
