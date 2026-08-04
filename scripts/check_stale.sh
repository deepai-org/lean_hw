#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# Staleness gate. Every derived artifact is rebuilt from source and compared
# with what is on disk; any difference is a failure.
#
# This exists because silent staleness cost real time three separate ways:
#   * the LLVM backend's opcode table drifted out of sync with the emulator
#     and NOTHING noticed, because the board demo loads a PREBUILT image that
#     never recompiles through the backend;
#   * a stale `minitest` binary reported all-green after a `git stash pop`,
#     which nearly became a false success claim;
#   * a stale `rtl/lnp64mini.v` made a byte-identical refactor check
#     meaningless -- it was comparing against RTL emitted from a different
#     numbering entirely.
#
# In each case the *sources* were consistent and an artifact was not. A
# derived file that disagrees with its source is a lie the repo tells itself,
# so the gate turns it into a loud failure.
set -uo pipefail
cd "$(dirname "$0")/.."
FAIL=0
say() { printf '%s\n' "$*"; }
bad() { printf '  STALE  %s\n' "$*"; FAIL=1; }
ok()  { printf '  ok     %s\n' "$*"; }

say "### 1. Lean builds from source (a stale .olean is a stale binary)"
lake build minitest >/dev/null 2>&1 || { bad "lake build failed"; exit 1; }
ok "lake build minitest"

say "### 2. emitted RTL matches the designs"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
for f in rtl/*.v; do [ -f "$f" ] && cp "$f" "$T/$(basename "$f")"; done
lake exe emit >/dev/null 2>&1
for t in "" soc dual; do
  lake env lean --run Machines/Lnp64mini/Emit.lean $t >/dev/null 2>&1
done
lake env lean --run Machines/Epoch/Emit.lean soc    >/dev/null 2>&1
lake env lean --run Machines/Epoch/Emit.lean engine >/dev/null 2>&1
lake env lean --run Machines/CapWalk/Emit.lean soc  >/dev/null 2>&1
for f in rtl/*.v; do
  b="$T/$(basename "$f")"
  if [ -f "$b" ]; then cmp -s "$f" "$b" && ok "$(basename "$f")" || bad "$(basename "$f") — on disk did not match a fresh emit"
  else bad "$(basename "$f") — was not on disk before this run"; fi
done

say "### 3. .hex artifacts match their .s sources"
L=../lnp64/target/release/lnp64
if [ -x "$L" ]; then
  for s in fpga/zc702/*.s; do
    n="${s%.s}"; [ -f "$n.hex" ] || continue
    cp "$n.hex" "$T/$(basename "$n").hex.before"
    if [ -f "$n.data.hex" ]; then $L asm-flat-exec "$s" -o "$n.hex" --data-hex "$n.data.hex" >/dev/null 2>&1
    else $L asm-flat-exec "$s" -o "$n.hex" >/dev/null 2>&1; fi
    cmp -s "$n.hex" "$T/$(basename "$n").hex.before" \
      && ok "$(basename "$n").hex" || bad "$(basename "$n").hex — did not match a fresh assemble"
  done
else
  say "  (skipped: ../lnp64 assembler not built)"
fi

say "### 4. the selftests actually pass on the freshly built binary"
for t in selftest smpselftest preemptselftest domselftest \
         failstopselftest gateselftest capxferselftest mmuselftest; do
  r=$(timeout 400 ./.lake/build/bin/minitest "$t" 2>&1 | tail -1)
  case "$r" in *OK*) ok "$t";; *) bad "$t — $r";; esac
done

[ "$FAIL" -eq 0 ] && say "check_stale: OK — every derived artifact matches its source" \
                  || say "check_stale: FAILED — see STALE lines above"
exit "$FAIL"
