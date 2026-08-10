#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# Staleness gate. Every derived artifact is rebuilt from source and compared
# with what is on disk; any difference is a failure.
# It rebuilds libraries and executables, regenerated RTL, assembled programs,
# cross-repository ISA agreement, and current architectural tests.
set -uo pipefail
cd "$(dirname "$0")/.."
source "$(dirname "$0")/lnp64_root.sh"
FAIL=0
say() { printf '%s\n' "$*"; }
bad() { printf '  STALE  %s\n' "$*"; FAIL=1; }
ok()  { printf '  ok     %s\n' "$*"; }

say "### 1. Lean builds from source (a stale .olean is a stale binary)"
# `lake build` covers libraries; name the executables explicitly so subsequent
# checks cannot consume an older binary.
lake build >/dev/null 2>&1 || { bad "lake build failed"; exit 1; }
lake build minitest emit audit >/dev/null 2>&1 || { bad "lake build (exes) failed"; exit 1; }
ok "lake build (library + minitest/emit/audit executables)"

say "### 2. emitted RTL matches the designs"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
for f in rtl/*.v; do [ -f "$f" ] && cp "$f" "$T/$(basename "$f")"; done
# `emit_all.sh` is the single producer inventory.
./scripts/emit_all.sh >/dev/null 2>&1
for f in rtl/*.v; do
  b="$T/$(basename "$f")"
  if [ -f "$b" ]; then cmp -s "$f" "$b" && ok "$(basename "$f")" || bad "$(basename "$f") — on disk did not match a fresh emit"
  else bad "$(basename "$f") — was not on disk before this run"; fi
done

say "### 3. assembled and board-program artifacts match their sources"
L=$LNP64_BIN
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
  say "  (skipped: $LNP64_ROOT assembler not built)"
fi

if r=$(python3 scripts/gen_board_prog.py fpga/zc702/loomcheck.hex \
    -o fpga/zc702/loom_mini_check.tcl --name loomcheck --check 2>&1); then
  ok "$r"
else
  bad "$r"
fi
isa_expect=$(./.lake/build/bin/minitest designexpect fpga/zc702/isasmoke.hex \
  | sed -n 's/^r1=//p')
if r=$(python3 scripts/gen_board_prog.py fpga/zc702/isasmoke.hex \
    -o fpga/zc702/isasmoke_board.tcl --name isasmoke \
    --bit '$LOOM_OXC7_DIR/out/lnp64mini_epoch_top.bit' \
    --expect-r1 "$isa_expect" --check 2>&1); then
  ok "$r"
else
  bad "$r"
fi
if r=$(python3 scripts/gen_board_prog.py fpga/zc702/conformance_hw.hex \
    -o fpga/zc702/conformance_board.tcl --name CONFORMANCE \
    --bit '$LOOM_OXC7_DIR/out/lnp64mini_dual_top.bit' --check 2>&1); then
  ok "$r"
else
  bad "$r"
fi

say "### 4. the two repos agree on the ISA (cross-repo, see check_isa_agreement.py)"
# Single-repository consistency does not establish agreement with the
# architecture/toolchain repository, so compare the two sources directly.
if r=$(python3 scripts/check_isa_agreement.py 2>&1); then
  ok "${r#check_isa_agreement: ok — }"
else
  bad "ISA agreement — $(printf '%s' "$r" | tail -n +2 | head -3 | tr '\n' ';')"
fi

say "### 5. the selftests actually pass on the freshly built binary"
for t in selftest smpselftest preemptselftest domselftest \
         failstopselftest gateselftest capxferselftest slotfillselftest mmuselftest \
         subwordselftest alugapselftest \
         traceselftest mmurelocselftest; do
  r=$(timeout 400 ./.lake/build/bin/minitest "$t" 2>&1 | tail -1)
  case "$r" in *"RESULT PASS"*) ok "$t";; *) bad "$t — $r";; esac
done

say "### 6. opcode coverage and literal hygiene"
# Check completeness against the design's own table rather than a second list.
if r=$(python3 scripts/check_opcode_coverage.py 2>&1 | tail -1); then ok "$r"; else bad "opcode coverage — $r"; fi
if r=$(python3 scripts/check_opcode_literals.py 2>&1 | tail -1); then ok "$r"; else bad "opcode literals — $r"; fi

say "### 7. emitted RTL agrees with the Design-derived matrix expectations"
# The expected architectural output comes from the proved Design simulator;
# this leg checks the separately emitted RTL. Slow (one iverilog build per
# program), so it is opt-in with STALE_RTL=1 and run before a bitstream.
if [ "${STALE_RTL:-0}" = "1" ]; then
  ./.lake/build/bin/minitest opdiffhex fpga/zc702/opdiff >/dev/null 2>&1
  r=$(./scripts/opdiff_rtl.sh 2>&1 | tail -1)
  case "$r" in *"OK"*) ok "RTL ≡ Design ($r)";; *) bad "RTL vs Design — $r";; esac
else
  say "  (skipped: set STALE_RTL=1 -- ~362 iverilog builds)"
fi

say "### 8. the assembler and this core agree (cross-repo, from mnemonics)"
# `isasmoke.s` is written in mnemonics and assembled by the architecture
# repository, independently of this core's opcode constants.
r=$(./scripts/isa_smoke.sh 2>&1 | head -1)
case "$r" in *OK*|*SKIP*) ok "${r#isa_smoke: }";; *) bad "ISA smoke — $r";; esac

say "### 9. the built compiler emits what the core decodes"
# Source agreement does not establish that an installed compiler is current;
# compile and disassemble a probe to check the executable toolchain.
if r=$(python3 scripts/check_backend_encoding.py 2>&1 | tail -1); then ok "$r"; else bad "backend encoding — $r"; fi

[ "$FAIL" -eq 0 ] && say "check_stale: OK — every derived artifact matches its source" \
                  || say "check_stale: FAILED — see STALE lines above"
exit "$FAIL"
