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
# FULL build, not just minitest: the first version of this gate built only
# the test binary, so a stale .olean on the EMIT path slipped through and
# emitted RTL for a design that no longer existed.
# `lake build` alone does NOT build the executables in this project -- it
# builds the library and stops. Section 4 below then runs `.lake/build/bin/
# minitest`, which can be an OLD binary that predates the sources this gate
# just "verified". That bit on 2026-08-04: a freshly added selftest fell
# through the arg match into the emit fallback, because the running binary
# still had yesterday's dispatch. Name the exes explicitly.
lake build >/dev/null 2>&1 || { bad "lake build failed"; exit 1; }
lake build minitest emit audit >/dev/null 2>&1 || { bad "lake build (exes) failed"; exit 1; }
ok "lake build (library + minitest/emit/audit executables)"

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

say "### 4. the two repos agree on the ISA (cross-repo, see check_isa_agreement.py)"
# Sections 1-3 are all single-repo: they rebuild lean_hw's artifacts from
# lean_hw's sources. On 2026-08-04 that was not enough. The conformance merge
# was reverted in `lnp64` and reapplied in `lean_hw`, leaving each repo
# internally consistent -- this gate green, all eight selftests green -- while
# the guest image (compiled by lnp64's backend) and the mini (built from
# lean_hw) no longer spoke the same ISA. The board retrapped forever on an
# opcode the core had stopped implementing.
if r=$(python3 scripts/check_isa_agreement.py 2>&1); then
  ok "${r#check_isa_agreement: ok — }"
else
  bad "ISA agreement — $(printf '%s' "$r" | tail -n +2 | head -3 | tr '\n' ';')"
fi

say "### 5. the selftests actually pass on the freshly built binary"
for t in selftest smpselftest preemptselftest domselftest \
         failstopselftest gateselftest capxferselftest mmuselftest \
         subwordselftest coverageselftest alugapselftest opdiffselftest; do
  r=$(timeout 400 ./.lake/build/bin/minitest "$t" 2>&1 | tail -1)
  case "$r" in *OK*) ok "$t";; *) bad "$t — $r";; esac
done

say "### 6. the emulator and the ISS agree on BEHAVIOUR, not just numbering"
# Section 4 compares opcode NUMBERS. It cannot see a semantic divergence, and
# two have already shipped: MINI_GATE_CALL's destination register, and six ALU
# opcodes the ISS mis-decoded after the renumbering. This runs the differential.
if command -v python3 >/dev/null && [ -x ../lnp64/target/release/lnp64 ]; then
  r=$(timeout 900 python3 scripts/diff_emulator_iss.py 2>&1 | tail -2 | tr '\n' ' ')
  case "$r" in *"MISMATCHES: 0"*) ok "emulator ≡ ISS ($r)";; *) bad "emulator vs ISS — $r";; esac
else
  say "  (skipped: python3 or ../lnp64 emulator not available)"
fi

say "### 7. opcode coverage and literal hygiene"
# The 2026-08-05 renumbering passed every gate then panicked on silicon,
# because `liu` -- how 64-bit constants are built -- was in no generated
# program. The defect class was "the list was incomplete", so completeness is
# now checked against the design's own table rather than maintained by hand.
if r=$(python3 scripts/check_opcode_coverage.py 2>&1 | tail -1); then ok "$r"; else bad "opcode coverage — $r"; fi
if r=$(python3 scripts/check_opcode_literals.py 2>&1 | tail -1); then ok "$r"; else bad "opcode literals — $r"; fi

say "### 8. the RTL agrees with the ISS on the generated matrix"
# Sections 5 and 6 compare EDSL/emulator against the ISS. Neither can see a
# defect in the EMITTED RTL, which is what the bitstream is built from and what
# silicon runs -- and that is the surface the 2026-08-05 renumbering broke while
# every other section stayed green. Slow (one iverilog build per program), so
# it is opt-in with STALE_RTL=1 and run in full before any bitstream.
if [ "${STALE_RTL:-0}" = "1" ]; then
  ./.lake/build/bin/minitest opdiffhex fpga/zc702/opdiff >/dev/null 2>&1
  r=$(./scripts/opdiff_rtl.sh 2>&1 | tail -1)
  case "$r" in *"OK"*) ok "RTL ≡ ISS ($r)";; *) bad "RTL vs ISS — $r";; esac
else
  say "  (skipped: set STALE_RTL=1 -- ~362 iverilog builds)"
fi

say "### 9. the assembler and this core agree (cross-repo, from mnemonics)"
# Sections 5, 6 and 8 all generate their programs from lean_hw's own OP_
# constants, so a renumbering moves design and program together and they agree
# by construction. isasmoke.s is written in MNEMONICS and assembled by lnp64's
# assembler, so nothing about its encoding comes from this repo. 58 instructions,
# under a second -- the cheap place to learn that the two repos disagree.
r=$(./scripts/isa_smoke.sh 2>&1 | head -1)
case "$r" in *OK*|*SKIP*) ok "${r#isa_smoke: }";; *) bad "ISA smoke — $r";; esac

[ "$FAIL" -eq 0 ] && say "check_stale: OK — every derived artifact matches its source" \
                  || say "check_stale: FAILED — see STALE lines above"
exit "$FAIL"
