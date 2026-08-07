#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# The cross-repo ISA smoke: assemble `isasmoke.s` with lnp64's assembler, run it
# on lean_hw's emitted RTL, and diff against lean_hw's ISS.
#
# Every other leg of the ladder generates its test programs from lean_hw's own
# `OP_` constants, so a renumbering moves the design and the program together
# and they agree by construction. That is the right property for the design, and
# it cannot see the question that actually broke the board: does the ASSEMBLER,
# which lives in the other repo and which the guest image is built by, still
# emit what this core decodes?
#
# `isasmoke.s` is written in mnemonics. Nothing about its encoding comes from
# lean_hw. It is 58 instructions and runs in under a second, so there is no
# excuse for learning about a decode disagreement 41 000 instructions into a
# kernel boot instead.
#
# The same .hex is what the board should run before any guest image is loaded;
# the checksum lands in r1 and in the zero-page word at 0x100, both readable
# over BSCAN.
set -uo pipefail
cd "$(dirname "$0")/.."
source "$(dirname "$0")/lnp64_root.sh"

ASM=${ASM:-$LNP64_BIN}
SRC=fpga/zc702/isasmoke.s
HEX=fpga/zc702/isasmoke.hex
SOC=rtl/lnp64mini_soc.v
TB=fpga/zc702/tb_lnp64mini_soc.v
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT

[ -x "$ASM" ] || { echo "isa_smoke: assembler $ASM not built -- SKIP"; exit 0; }
command -v iverilog >/dev/null || { echo "isa_smoke: iverilog not found -- SKIP"; exit 0; }

# Assemble from mnemonics with the OTHER repo's assembler. This is the step that
# gives the check its value; using a prebuilt .hex would make it single-repo
# again and it would prove nothing.
"$ASM" asm-flat-exec "$SRC" -o "$HEX" || { echo "isa_smoke: assemble FAILED"; exit 1; }

./.lake/build/bin/minitest issexpect "$HEX" > "$T/iss.txt" || {
  echo "isa_smoke: ISS run FAILED"; exit 1; }

iverilog -g2012 -DPROG_HEX="\"$HEX\"" -o "$T/a.vvp" "$SOC" "$TB" 2>/dev/null || {
  echo "isa_smoke: iverilog build FAILED"; exit 1; }
vvp "$T/a.vvp" 2>/dev/null \
  | grep -E '^(TRAP|HALTED|r[0-9]=|dmem32=)' | sed 's/ cycles=[0-9]*//' > "$T/rtl.txt"

if ! diff -q "$T/rtl.txt" "$T/iss.txt" >/dev/null; then
  echo "isa_smoke: FAILED — the assembler's encoding and this core disagree"
  echo "  (RTL < , ISS > )"
  diff "$T/rtl.txt" "$T/iss.txt" | sed 's/^/    /'
  exit 1
fi

# Agreement is not enough: when the assembler emitted the OLD store byte, the
# ISS and the RTL both faithfully TRAPPED on it, agreed bit-for-bit, and this
# smoke stayed green while the store never executed (found 2026-08-06 by
# divcheck.s). A smoke program that does not run to a clean halt proves
# nothing about the bytes it never reached.
if grep -q '^TRAP' "$T/iss.txt" || ! grep -q '^HALTED=1' "$T/iss.txt"; then
  echo "isa_smoke: FAILED — the program did not run to a clean halt"
  grep -E '^(TRAP|HALTED)' "$T/iss.txt" | sed 's/^/    /'
  exit 1
fi

CK=$(grep '^r1=' "$T/iss.txt" | cut -d= -f2)
echo "isa_smoke: OK — assembler ≡ RTL ≡ ISS on $(wc -l < "$HEX") instructions"
echo "isa_smoke: checksum r1 = $CK  (the board must report this before any guest boots)"
