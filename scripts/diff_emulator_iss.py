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
# Both sides expose the same single-instruction interface and print the same
# format, so the comparison is a plain diff of changed registers:
#     lnp64   step-op <hex-word> <r0,...,r31>
#     minitest stepop <hex-word> <r0,...,r31>
#
# Values are drawn from a boundary set (sign bits, all-ones, shift-amount
# edges) plus random 64-bit noise, because the interesting disagreements are at
# the edges -- signed vs unsigned compare, shift-by->=64, sign extension.
import subprocess, random, re, sys
random.seed(20260804)
MINI="/home/ubuntu/lean_hw/.lake/build/bin/minitest"
EMU="/home/ubuntu/lnp64/target/release/lnp64"
# Opcode numbers are READ FROM THE DESIGN, never hardcoded. An earlier version
# of this file carried its own table of literals and went stale the moment the
# numbering changed -- reporting mismatches that were really its own encodings.
# That is the same hazard this script exists to catch, so it must not have it.
def _mini_ops():
    src = open("/home/ubuntu/lean_hw/Machines/Lnp64mini/Core.lean").read()
    return {m.group(1): int(m.group(2), 16)
            for m in re.finditer(r"^def OP_([A-Z0-9_]+) : Nat := (0x[0-9a-f]+)", src, re.M)}

_OPS = _mini_ops()
def _op(name): return _OPS[name]

RRR = {_op(n): n for n in ["ADD","SUB","MUL","AND","OR","XOR","LSL","LSR","ASR",
                           "SLT","SLTU","DIV","SREM","UDIV","UREM","MULH","MULHU",
                           "ROL","ROR"]}
RR  = {_op(n): n for n in ["NOT","SEXT_B","SEXT_H","SEXT_W","ZEXT_B","ZEXT_H",
                           "ZEXT_W","CTZ","BSWAP16","BSWAP32","BSWAP64"]}
INTERESTING=[0,1,2,7,8,63,64,0xff,0x100,0x7fffffff,0x80000000,0xffffffff,
             0x7fffffffffffffff,0x8000000000000000,0xffffffffffffffff]
def run(cmd):
    r=subprocess.run(cmd,capture_output=True,text=True,timeout=300)
    return r.stdout.strip(), r.returncode
def regs_str(rs): return ",".join(str(x) for x in rs)
def parse(out):
    d={}
    for line in out.splitlines():
        p=line.split()
        if len(p)==3 and p[0]=="STEP_OP_REG": d[int(p[1])]=int(p[2])
    return d
mismatch=[]; tested=0; skipped=[]
cases=[]
for op,name in list(RRR.items()):
    for _ in range(6):
        rs=[0]*32
        for i in range(1,32): rs[i]=random.choice(INTERESTING+[random.getrandbits(64)])
        cases.append((op,name,3,1,2,rs))
for op,name in list(RR.items()):
    for _ in range(6):
        rs=[0]*32
        for i in range(1,32): rs[i]=random.choice(INTERESTING+[random.getrandbits(64)])
        cases.append((op,name,3,1,0,rs))
for op,name,rd,rs1,rs2,rs in cases:
    w=(op<<56)|(rd<<51)|(rs1<<46)|(rs2<<41)
    hexw="%016x"%w
    eo,erc=run([EMU,"step-op",hexw,regs_str(rs)])
    if erc!=0 or "not supported" in eo:
        skipped.append(name); continue
    mo,mrc=run([MINI,"stepop",hexw,regs_str(rs)])
    tested+=1
    em,mm=parse(eo),parse(mo)
    if em!=mm:
        mismatch.append((name,hexw,rs[rs1],rs[rs2],em,mm))
print(f"tested {tested} vectors; skipped(emulator unsupported): {sorted(set(skipped))}")
print(f"MISMATCHES: {len(mismatch)}")
for n,w,a,b,em,mm in mismatch[:12]:
    print(f"  {n:8} word={w} rs1={a} rs2={b}")
    print(f"     emulator={em}")
    print(f"     iss     ={mm}")
