#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# The cross-repo ISA smoke: assemble `isasmoke.s` with lnp64's assembler, run it
# on lean_hw's emitted RTL, and diff against the Design-derived simulator.
#
# `isasmoke.s` is written in mnemonics, so its encoding comes from the external
# architecture repository rather than this core's opcode constants.
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

# Assemble from mnemonics with the architecture repository's assembler.
"$ASM" asm-flat-exec "$SRC" -o "$HEX" || { echo "isa_smoke: assemble FAILED"; exit 1; }

./.lake/build/bin/minitest designexpect "$HEX" > "$T/design.txt" || {
  echo "isa_smoke: Design simulation FAILED"; exit 1; }

iverilog -g2012 -DPROG_HEX="\"$HEX\"" -o "$T/a.vvp" "$SOC" "$TB" 2>/dev/null || {
  echo "isa_smoke: iverilog build FAILED"; exit 1; }
vvp "$T/a.vvp" 2>/dev/null \
  | grep -E '^(TRAP|HALTED|r[0-9]=|dmem32=)' | sed 's/ cycles=[0-9]*//' > "$T/rtl.txt"

if ! diff -q "$T/rtl.txt" "$T/design.txt" >/dev/null; then
  echo "isa_smoke: FAILED — the assembler's encoding and this core disagree"
  echo "  (RTL < , Design > )"
  diff "$T/rtl.txt" "$T/design.txt" | sed 's/^/    /'
  exit 1
fi

# Agreement is not enough: require a clean halt so every preceding instruction
# was actually reached.
if grep -q '^TRAP' "$T/design.txt" || ! grep -q '^HALTED=1' "$T/design.txt"; then
  echo "isa_smoke: FAILED — the program did not run to a clean halt"
  grep -E '^(TRAP|HALTED)' "$T/design.txt" | sed 's/^/    /'
  exit 1
fi

CK=$(grep '^r1=' "$T/design.txt" | cut -d= -f2)
echo "isa_smoke: OK — assembler ≡ RTL ≡ Design on $(wc -l < "$HEX") instructions"
echo "isa_smoke: checksum r1 = $CK  (the board must report this before any guest boots)"
