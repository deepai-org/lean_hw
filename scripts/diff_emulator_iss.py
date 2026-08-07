#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# Differential single-step: lnp64mini's ISS vs the lnp64 emulator.
#
# check_isa_agreement.py proves the implementations agree on opcode NUMBERS.
# It cannot see whether they agree on opcode BEHAVIOUR, and they have twice
# been caught not doing so:
#
#   * MINI_GATE_CALL wrote a destination register in the emulator and none on
#     the fabric, with identical encodings on both sides;
#   * `not`, `sltu`, `bgeu`, `srli`, `srai` and `sltiu` were mis-decoded by the
#     ISS after the renumbering -- OP_NOT missing from is_alu, stale raw bytes
#     0x1c/0xa5/0xa6/0x1e left behind, and is_branch holding OP_SLTU where
#     OP_BGEU belonged. THIS SCRIPT FOUND THAT SET ON ITS FIRST RUN.
#
# Opcode numbers are NOT written here. They are read out of Core.lean's OP_
# table -- the same anchor sections 4/9/10 of check_stale.sh tie to the
# assembler, the .td and the built clang. The first version of this script
# carried its own hex table, which is the duplicated-opcode-number hazard the
# 2026-08-05 rollback named; a tool that exists to catch stale literals must
# not contain any. Deriving from Core.lean also makes the emulator's step-op
# arms self-checking: if they drift, the op comes back "not supported" (a
# REQUIRED failure below) or executes the wrong instruction (a mismatch).
#
# The immediate forms and the wide-immediate builder `liu` are driven since
# 2026-08-05: `liu` is how every 64-bit constant is built, it was in no
# differential when the renumbering shipped, and a wrong constant is exactly
# what panicked silicon ("not lightweight enough for -1 CPUs"). Ops the two
# CLIs cannot drive in one register-file step (auipc needs an agreed pc;
# LR/SC, futex, clone, gate/cap ops need machine context) are covered by the
# EDSL/ISS selftests and the RTL matrix leg -- see check_opcode_coverage.py's
# EXCLUDED table for the claim per op.
#
# Values are drawn from a boundary set (sign bits, all-ones, shift-amount
# edges) plus random 64-bit noise, because the interesting disagreements are at
# the edges -- signed vs unsigned compare, shift-by->=64, sign extension.
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import random
random.seed(20260804)
HW = pathlib.Path(__file__).resolve().parent.parent
MINI = str(HW / ".lake/build/bin/minitest")
EMU = str(HW.parent / "lnp64/target/release/lnp64")
CORE = HW / "Machines/Lnp64mini/Core.lean"

OPS = {m.group(1): int(m.group(2), 16)
       for m in re.finditer(r"^def OP_([A-Z0-9_]+) : Nat := (0x[0-9a-f]+)",
                            CORE.read_text(), re.M)}

# Families by NAME; the byte comes from Core.lean. Every name listed here is
# REQUIRED: if either side cannot execute it, that is a failure, not a skip --
# a silent skip is how a hole in this net stays invisible.
RRR = ["ADD", "SUB", "MUL", "AND", "OR", "XOR", "LSL", "LSR", "ASR",
       "SLT", "SLTU", "DIV", "SREM", "UDIV", "UREM", "MULH", "MULHU",
       "ROL", "ROR"]
RR = ["NOT", "SEXT_B", "SEXT_H", "SEXT_W", "ZEXT_B", "ZEXT_H", "ZEXT_W",
      "CTZ", "BSWAP16", "BSWAP32", "BSWAP64"]
IMM = ["ADDI", "ANDI", "ORI", "XORI", "LSLI", "LSRI", "ASRI",
       "SLTI", "SLTIU", "LIU"]
# The 5-slot compare-select family. Its condition keying (op[2:0], valid only
# on the retired 0x40-0x45 block) panicked BOTH silicon renumber attempts
# through strtoll's neg?MIN:MAX, and no differential could drive it: the EDSL
# and the ISS carried the same wrong keying and agreed, the matrix could not
# build the form, and step-op had no arms. Now all three can.
SEL5 = ["SEL", "SEL_41", "SEL_42", "SEL_43", "SEL_44", "SEL_45"]

INTERESTING = [0, 1, 2, 7, 8, 63, 64, 0xff, 0x100, 0x7fffffff, 0x80000000,
               0xffffffff, 0x7fffffffffffffff, 0x8000000000000000,
               0xffffffffffffffff]
# Immediate battery: sign boundaries of the 32-bit field, shift edges at and
# past 64, and a mixed pattern. liu's hi/lo assembly breaks exactly here.
IMMS = [0, 1, -1, 63, 64, 65, 0x7fffffff, -0x80000000, 0x12345678]


def run(cmd):
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
    return r.stdout.strip(), r.returncode


def regs_str(rs):
    return ",".join(str(x) for x in rs)


def parse(out):
    d = {}
    for line in out.splitlines():
        p = line.split()
        if len(p) == 3 and p[0] == "STEP_OP_REG":
            d[int(p[1])] = int(p[2])
    return d


def seeded_regs():
    rs = [0] * 32
    for i in range(1, 32):
        rs[i] = random.choice(INTERESTING + [random.getrandbits(64)])
    return rs


missing = [n for n in RRR + RR + IMM + SEL5 if n not in OPS]
if missing:
    print(f"REQUIRED opcodes absent from Core.lean: {missing}")
    print("MISMATCHES: unmeasurable")
    sys.exit(1)

cases = []
for name in RRR:
    for _ in range(6):
        cases.append((name, (OPS[name] << 56) | (3 << 51) | (1 << 46) | (2 << 41),
                      "rs1={} rs2={}", (1, 2), seeded_regs()))
for name in RR:
    for _ in range(6):
        cases.append((name, (OPS[name] << 56) | (3 << 51) | (1 << 46),
                      "rs1={}", (1,), seeded_regs()))
for name in IMM:
    for imm in IMMS:
        w = (OPS[name] << 56) | (3 << 51) | (1 << 46) | ((imm & 0xffffffff) << 14)
        cases.append((name, w, f"rs1={{}} imm={imm}", (1,), seeded_regs()))
for name in SEL5:
    # rd=5, cc pair r1/r2, true/false values r3/r4; three shapes per variant:
    # random, equal operands (the eq/ne edge), and signed-vs-unsigned edge.
    shapes = [seeded_regs(), seeded_regs(), seeded_regs()]
    shapes[1][2] = shapes[1][1]
    shapes[2][1] = 0x8000000000000000
    shapes[2][2] = 1
    for rs in shapes:
        w = (OPS[name] << 56) | (5 << 51) | (1 << 46) | (2 << 41) | (3 << 36) | (4 << 31)
        cases.append((name, w, "rs1={} rs2={}", (1, 2), rs))

mismatch = []
tested = 0
unsupported = {}
# Emulator side per case (~1 ms each); mini side in ONE minitest process --
# each minitest process pays ~7.5 s of Lean startup before main runs, which
# at one case per process is half an hour of pure initialization.
emu_out = []
for name, w, opfmt, srcregs, rs in cases:
    hexw = "%016x" % w
    eo, erc = run([EMU, "step-op", hexw, regs_str(rs)])
    if erc != 0 or "not supported" in eo:
        unsupported.setdefault(name, eo.splitlines()[-1] if eo else f"rc={erc}")
        emu_out.append(None)
    else:
        emu_out.append(eo)

with tempfile.NamedTemporaryFile("w", suffix=".stepops", delete=False) as f:
    batch_path = f.name
    kept = [i for i, eo in enumerate(emu_out) if eo is not None]
    for i in kept:
        _, w, _, _, rs = cases[i]
        f.write("%016x %s\n" % (w, regs_str(rs)))
mo_all, mrc = run([MINI, "stepops", batch_path])
pathlib.Path(batch_path).unlink(missing_ok=True)
mini_blocks = {}
cur = None
for line in mo_all.splitlines():
    p = line.split()
    if len(p) == 2 and p[0] == "STEP_OP_CASE":
        cur = int(p[1])
        mini_blocks[cur] = []
    elif cur is not None:
        mini_blocks[cur].append(line)

for pos, i in enumerate(kept):
    name, w, opfmt, srcregs, rs = cases[i]
    hexw = "%016x" % w
    mo = "\n".join(mini_blocks.get(pos, []))
    if "STEP_OP_OK" not in mo:
        unsupported.setdefault(name, "mini stepops produced no STEP_OP_OK")
        continue
    tested += 1
    em, mm = parse(emu_out[i]), parse(mo)
    if em != mm:
        mismatch.append((name, hexw, opfmt.format(*(rs[i] for i in srcregs)), em, mm))

if unsupported:
    # Every listed op is required on BOTH sides. An op the emulator cannot
    # step is a hole in the net -- the exact shape liu hid in.
    print(f"REQUIRED ops not exercised: {sorted(unsupported)}")
    for n, why in sorted(unsupported.items()):
        print(f"  {n:8} {why}")
    print("MISMATCHES: unmeasurable (required ops skipped)")
    sys.exit(1)

print(f"tested {tested} vectors across {len(RRR + RR + IMM + SEL5)} required ops; 0 skipped")
print(f"MISMATCHES: {len(mismatch)}")
for n, w, operands, em, mm in mismatch[:12]:
    print(f"  {n:8} word={w} {operands}")
    print(f"     emulator={em}")
    print(f"     iss     ={mm}")
sys.exit(1 if mismatch else 0)
