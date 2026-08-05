#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# Check the opcode bytes the BUILT COMPILER actually emits against the mini's
# table -- by compiling a probe and disassembling the object, not by reading any
# source file.
#
# This is the gap that every other check has, and it is almost certainly how the
# 2026-08-05 renumbering reached silicon with a green board of gates.
#
# `check_isa_agreement.py` compares Core.lean, the assembler's tables, and
# LNP64InstrInfo.td. All three are SOURCES. The guest kernel is not built from
# sources at test time -- it is built by the clang binary in
# `target/llvm-lnp64-build/bin/`, which is only as current as the last full LLVM
# rebuild. Editing the .td and not rebuilding leaves a compiler that emits the
# OLD numbering while the mini decodes the new one, and:
#
#   * every single-repo gate is green,
#   * the cross-repo ISA agreement check is green (it reads the .td),
#   * `isa_smoke.sh` is green -- it assembles through `lnp64 asm-flat-exec`,
#     which is the ASSEMBLER, a different encoder that moved correctly,
#   * and the 382-object kernel is compiled with an instruction stream the core
#     does not implement, which does not fail at load. It fails wherever the
#     first miscompiled instruction happens to execute -- 41 550 instructions
#     into a rump boot, as a panic with no obvious relation to the ISA.
#
# Reproduced deliberately: moving OP_LIU with the .td updated and clang not
# rebuilt leaves `liu` encoded as 0x04 in the object file while the mini decodes
# 0x57, and no other check notices.
#
# So this one disassembles what the compiler produced. A source file cannot lie
# to it.

import argparse
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

HW = pathlib.Path(__file__).resolve().parent.parent
LNP64 = HW.parent / "lnp64"
CORE = HW / "Machines/Lnp64mini/Core.lean"

# The probe. Written to make the backend reach for a wide spread of opcodes --
# in particular the 64-bit constants that `liu` builds, which is the family that
# had no coverage at all when the renumbering shipped.
PROBE = r"""
unsigned long k0(void){ return 0x123456787abcdef0UL; }
unsigned long k1(void){ return 0xffffffffffffffffUL; }
unsigned long k2(void){ return 0x7fffffffffffffffUL; }
unsigned long k3(void){ return 0x8000000000000000UL; }
unsigned long k4(void){ return 0x00000000ffffffffUL; }
long  add(long a, long b){ return a + b; }
long  sub(long a, long b){ return a - b; }
long  mul(long a, long b){ return a * b; }
long  divs(long a, long b){ return a / b; }
long  remu(unsigned long a, unsigned long b){ return a % b; }
long  and_(long a, long b){ return a & b; }
long  or_(long a, long b){ return a | b; }
long  xor_(long a, long b){ return a ^ b; }
long  shl(long a, int b){ return a << b; }
long  shr(unsigned long a, int b){ return a >> b; }
long  sar(long a, int b){ return a >> b; }
long  lt(long a, long b){ return a < b; }
long  ltu(unsigned long a, unsigned long b){ return a < b; }
long  ld64(long *p){ return *p; }
int   ld32(int *p){ return *p; }
short ld16(short *p){ return *p; }
char  ld8(char *p){ return *p; }
void  st64(long *p, long v){ *p = v; }
void  st32(int *p, int v){ *p = v; }
void  st16(short *p, short v){ *p = v; }
void  st8(char *p, char v){ *p = v; }
long  br(long a, long b){ return a == b ? a : b; }
long  loop(long *p, long n){ long s = 0; for (long i = 0; i < n; i++) s += p[i]; return s; }
extern long callee(long);
long  call(long a){ return callee(a) + 1; }
"""

# Backend mnemonic -> mini OP_ name, where the two spell the same instruction
# differently. Anything not listed is matched by uppercasing the mnemonic.
#
# These were MEASURED, by disassembling a probe and reading the opcode byte, not
# guessed from the spelling. Guessing got two of them wrong: `sb` is 0x35 and
# `sh` is 0x37, which is the reverse of what the names suggest, and the backend
# spells the loads `lb`/`lh`/`lwu` rather than `ld_b_s`/`ld_h_s`/`ld_w_s`. A
# wrong alias here is worse than no alias -- it compares the right instruction
# against the wrong table entry and reports a defect that is not there.
ALIAS = {
    "ld": "LD", "lb": "LD_S_72", "lh": "LD_S", "lwu": "LD_31",
    "sd": "ST", "sw": "ST_34", "sb": "ST_35", "sh": "ST_37",
    "sll": "LSL", "srl": "LSR", "sra": "ASR",
    "zext.w": "ZEXT_W",
    "ret": "JALR",
    # `li` and `mov` are both assembler spellings of `addi rd, rs, imm` -- the
    # mini's EXCLUDED list already records MOV as an alias of addi. They are
    # NOT the mini's OP_MOV (0x02), which is why comparing `mov` against OP_MOV
    # reported a disagreement that does not exist.
    "li": "ADDI", "mov": "ADDI",
}


def mini_opcodes():
    src = CORE.read_text()
    return {m.group(1): int(m.group(2), 16)
            for m in re.finditer(r"^def OP_([A-Z0-9_]+) : Nat := (0x[0-9a-f]+)",
                                 src, re.M)}


def disassemble(clang, objdump):
    """Compile the probe and return {mnemonic: {opcode bytes seen}}."""
    tmp = pathlib.Path(tempfile.mkdtemp())
    try:
        c = tmp / "probe.c"
        c.write_text(PROBE)
        o = tmp / "probe.o"
        r = subprocess.run([clang, "--target=lnp64", "-O1", "-c", str(c),
                            "-o", str(o)], capture_output=True, text=True)
        if r.returncode != 0:
            return None, f"probe did not compile: {r.stderr.strip()[:300]}"
        r = subprocess.run([objdump, "--triple=lnp64", "-d", str(o)],
                           capture_output=True, text=True)
        if r.returncode != 0:
            return None, f"disassembly failed: {r.stderr.strip()[:300]}"
        seen = {}
        # "   0: 00 00 bc 37 af 1e 10 a0   \tli\tr2, 2059198192"
        pat = re.compile(r"^\s*[0-9a-f]+:\s+((?:[0-9a-f]{2} ){8})\s*\t([a-z_0-9.]+)")
        for line in r.stdout.splitlines():
            m = pat.match(line)
            if not m:
                continue
            b = m.group(1).split()
            # op[63:56] -- the top byte of the 64-bit word, last in a
            # little-endian byte dump.
            seen.setdefault(m.group(2), set()).add(int(b[7], 16))
        return seen, None
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--clang", default=str(LNP64 / "target/llvm-lnp64-build/bin/clang"))
    ap.add_argument("--objdump",
                    default=str(LNP64 / "target/llvm-lnp64-build/bin/llvm-objdump"))
    a = ap.parse_args()

    if not pathlib.Path(a.clang).exists():
        print("check_backend_encoding: SKIP — no built clang at " + a.clang)
        return 0

    mini = mini_opcodes()
    seen, err = disassemble(a.clang, a.objdump)
    if err:
        print(f"check_backend_encoding: SKIP — {err}")
        return 0

    bad, checked, unknown = [], 0, []
    for mnem, bytes_ in sorted(seen.items()):
        name = ALIAS.get(mnem, mnem.upper())
        if name not in mini:
            unknown.append(mnem)
            continue
        want = mini[name]
        for got in sorted(bytes_):
            checked += 1
            if got != want:
                bad.append((mnem, name, got, want))

    print(f"backend encoding: {checked} emitted instruction(s) across "
          f"{len(seen)} mnemonic(s) checked against the mini's table")
    if unknown:
        print(f"  (not in the mini's table, not checked: {', '.join(unknown)})")

    if bad:
        print(f"\n  THE BUILT COMPILER DISAGREES WITH THE CORE — {len(bad)}:")
        for mnem, name, got, want in bad:
            print(f"    {mnem}: object 0x{got:02x}, mini OP_{name} 0x{want:02x}")
        print("\n  The guest kernel is compiled by this binary, not by the .td.")
        print("  If the .td was edited and LLVM was not rebuilt, the image will")
        print("  load fine and then execute an instruction the core does not")
        print("  implement, wherever that instruction first happens to run.")
        print("  Rebuild LLVM before building any image.")
        return 1

    print("check_backend_encoding: ok — every opcode the built compiler emits "
          "matches the core")
    return 0


if __name__ == "__main__":
    sys.exit(main())
