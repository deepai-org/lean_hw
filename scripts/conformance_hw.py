#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# The HARDWARE leg of Appendix D's derived "Pinned corner values" family.
#
# `lnp64/scripts/run_conformance_pinned.py` runs the same vectors on the
# emulator through `lnp64 step-op`: one process per vector, one instruction
# executed out of thin air, no fetch, no decode, no writeback path. That is the
# emulator leg and it is the right first leg. It cannot see the question this
# repo exists to answer: does the CORE -- the thing the bitstream is built from
# -- obey the frozen sentence when it fetches and decodes the bytes the
# assembler emitted?
#
# So this leg does not single-step anything. It compiles the whole derived
# vector set into ONE program written in MNEMONICS, assembles it with lnp64's
# assembler, and runs it on lnp64mini: the Design-derived simulator (`minitest
# designexpect`) and, with --rtl, the emitted `rtl/lnp64mini_soc.v` under iverilog.
# The board leg reuses the identical .hex and reads the same zero-page array
# back over BSCAN.
#
# NO OPCODE NUMBER APPEARS IN THIS FILE OR IN THE ASSEMBLY IT GENERATES.
# The only op-identifying strings written here are the ASSEMBLER'S MNEMONICS,
# and even the spec-name -> mnemonic aliasing (the ISA calls the left shift
# `sll`, the assembler spells it `LSL`) is *verified* at run time by assembling
# a probe instruction and checking its top byte against `isa_opcodes.json`.
# `isa_smoke.sh`'s header says why: every other leg of the ladder generates its
# programs from lean_hw's own `OP_` constants, so a renumbering moves the design
# and the test together and they agree by construction. A tool whose job is to
# catch a stale literal must contain none.
#
# NOTHING here may weaken an expectation. If the core disagrees with a derived
# vector, that is a FINDING and is printed with the frozen sentence and its spec
# line. Vectors that cannot be expressed are SKIPPED AND COUNTED, never dropped:
# a summary that reads "268/268 green" because 40 vectors quietly vanished is
# the exact failure mode this whole family exists to prevent.
#
# And -- `isa_smoke.sh` lines 57-66 -- the program must run to a CLEAN HALT. An
# instruction the core traps on makes the Design and the RTL agree perfectly while
# the instruction under test never executes. Any TRAP here is attributed to the
# vector whose instruction the trap PC lands in, reported as a FAILURE with its
# spec sentence, and the vector is then removed so the remaining ones can run.

import argparse
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
LEAN_HW = HERE.parent

MASK64 = (1 << 64) - 1
TEXT_BASE = 0x1000          # where the flat-exec image is loaded (asm + tb agree)
WORD = 8

# ---- zero-page result array (the board reads this back over BSCAN) ----
SLOT_BASE = 0x100           # vector g's 64-bit raw result at SLOT_BASE + 8*g
BITMAP_BASE = 0x000         # 5 x 64-bit pass bitmap
MISMATCH_ADDR = 0x028
NVEC_ADDR = 0x030
BITMAP_WORDS = 5            # 5 * 64 = 320 bit positions >= 268 vectors
DMEM_WORDS = 512            # rtl/lnp64mini_soc.v: reg [63:0] dmem [0:511]

# Architectural registers the Design and the testbench both print (r1..r9).
R_BITMAP = [1, 2, 3, 4, 5]  # pass bitmap words 0..4
R_MISMATCH = 6
R_NVEC = 7
# scratch
R_A, R_B, R_RES, R_FLAG, R_T, R_U = 10, 11, 12, 13, 14, 15

# Spec mnemonic (isa_opcodes.json / the vector file) -> assembler mnemonic.
# Names only. Every entry is checked against isa_opcodes.json through the
# assembler before a single vector runs; see verify_mnemonics().
ASM_ALIAS = {
    "sll": "LSL",
    "srl": "LSR",
    "sra": "ASR",
}


def asm_mnemonic(spec_op):
    return ASM_ALIAS.get(spec_op, spec_op.upper())


# --------------------------------------------------------------------------
# environment
# --------------------------------------------------------------------------

def lnp64_paths():
    """LNP64_ROOT / LNP64_BIN come from scripts/lnp64_root.sh -- the ONE place
    this repo says where lnp64 is. Never hardcoded here."""
    root_sh = HERE / "lnp64_root.sh"
    out = subprocess.run(
        ["bash", "-c", 'source "%s"; printf "%%s\\n%%s\\n" "$LNP64_ROOT" "$LNP64_BIN"' % root_sh],
        capture_output=True, text=True, check=True).stdout.splitlines()
    root, binary = pathlib.Path(out[0]), pathlib.Path(out[1])
    if not binary.is_file() or not os.access(binary, os.X_OK):
        sys.exit("conformance_hw: assembler %s not built" % binary)
    return root, binary


# --------------------------------------------------------------------------
# assembly emission
# --------------------------------------------------------------------------

def split64(v):
    """(low32, high32) as literals the assembler's imm32 accepts
    (i32::MIN ..= u32::MAX)."""
    return v & 0xFFFFFFFF, (v >> 32) & 0xFFFFFFFF


class Prog:
    """An instruction list that remembers, for every word, which vector it
    belongs to -- so a trap PC names a vector instead of an address."""

    def __init__(self):
        self.lines = []     # (text, owner) ; owner = global vector index or None
        self.owner = None

    def emit(self, text, comment=None):
        if comment:
            text = "%-34s ; %s" % (text, comment)
        self.lines.append(("  " + text, self.owner))

    def note(self, text):
        self.lines.append((text, None))    # comment/label: not an instruction

    def n_instr(self):
        return sum(1 for t, _ in self.lines if t.startswith("  "))

    def pc_owner_map(self):
        """instruction index -> owning vector index (or None)."""
        return [o for t, o in self.lines if t.startswith("  ")]

    def text(self):
        return "\n".join(t for t, _ in self.lines) + "\n"

    # ---- helpers ----
    def li64(self, r, v, what=""):
        lo, hi = split64(v)
        self.emit("LI   r%d, %d" % (r, lo), what)
        self.emit("LIU  r%d, r%d, %d" % (r, r, hi))

    def do_op(self, rd, spec_op, form, rs1, rs2):
        m = asm_mnemonic(spec_op)
        if form == "rrr":
            self.emit("%-7s r%d, r%d, r%d" % (m, rd, rs1, rs2))
        else:
            self.emit("%-7s r%d, r%d" % (m, rd, rs1))

    def eq_flag(self, rflag, ra, rb):
        """rflag = 1 iff ra == rb.  (xor; 0 <u diff; invert)"""
        self.emit("XOR  r%d, r%d, r%d" % (rflag, ra, rb))
        self.emit("SLTU r%d, r0, r%d" % (rflag, rflag))
        self.emit("XORI r%d, r%d, 1" % (rflag, rflag))


HEADER = """\
; conformance_hw.s -- GENERATED by lean_hw/scripts/conformance_hw.py.
; DO NOT EDIT: every constant below is a DERIVED expectation out of
; {vecfile}
; (Appendix D family "Pinned corner values", derived from frozen sentences of
; {sections}). Editing a value here forges a conformance result.
;
; Written in MNEMONICS and assembled by lnp64's own assembler; no opcode number
; appears in the generator or in this file. It is one batched program: each
; vector materialises its inputs with LI/LIU, executes the op under test, stores
; the raw 64-bit result to its own zero-page slot, and folds a pass/fail bit
; into the architectural bitmap. The program must run to a CLEAN HALT --
; isa_smoke.sh:57-66 records what a trapping program proves (nothing).
;
; ---------------------------------------------------------------------------
; ZERO-PAGE RESULT ARRAY  (dmem is 512 x 64-bit; the board reads it via BSCAN)
;
;   0x000 + 8*w   pass bitmap word w, w = 0..4
;                 bit (g mod 64) of word (g div 64) is 1 iff vector g executed
;                 AND its result matched the derived expectation.
;                 g is the GLOBAL index of the vector in the runnable list, so
;                 a slot means the same thing across runs even when a vector is
;                 removed; a removed/trapped vector leaves its bit 0.
;   0x028         mismatch count (executed vectors whose result disagreed)
;   0x030         number of vectors executed by this program
;   0x100 + 8*g   raw 64-bit result of vector g   (g = 0 .. {maxg}, top {top})
;
; ARCHITECTURAL READOUT (r1..r9 are what `minitest designexpect` and
; fpga/zc702/tb_lnp64mini_soc.v both print, so the Design and the RTL legs compare
; the whole bitmap without a custom testbench):
;   r1..r5 = bitmap words 0..4     r6 = mismatch count     r7 = vectors executed
;   dmem32 (0x100) = vector 0's raw result
;
; vectors in this program : {nvec}
; ---------------------------------------------------------------------------
.text
"""


def gen_program(vectors, all_runnable_n, vecfile, sections):
    """vectors: list of (g, vector) to execute, in order. Returns Prog."""
    p = Prog()
    top = SLOT_BASE + WORD * (all_runnable_n - 1)
    p.note(HEADER.format(vecfile=vecfile, sections=sections, nvec=len(vectors),
                         maxg=all_runnable_n - 1, top="0x%x" % top).rstrip("\n"))
    p.owner = None
    p.note("; --- prologue: bitmap and counters start at zero ---")
    for r in R_BITMAP:
        p.emit("LI   r%d, 0" % r)
    p.emit("LI   r%d, 0" % R_MISMATCH)

    for g, v in vectors:
        a = v["assertion"]
        kind = a["kind"]
        p.owner = g
        p.note("")
        p.note("; === vector %s  rule=%s op=%s  slot 0x%x  bitmap word %d bit %d"
               % (v["id"], v["rule"], v["op"], SLOT_BASE + WORD * g, g // 64, g % 64))
        p.note(";     %s:%d  %s" % (sections, v["provenance"]["spec_line"],
                                    one_line(v["provenance"]["sentence"])))
        # inputs
        p.li64(R_A, int(v["inputs"]["rs1"], 16), "rs1")
        if v["form"] == "rrr":
            p.li64(R_B, int(v["inputs"]["rs2"], 16), "rs2")
        # the op under test
        p.do_op(R_RES, v["op"], v["form"], R_A, R_B)
        p.emit("SD   [r0, %d], r%d" % (SLOT_BASE + WORD * g, R_RES), "result slot")

        if kind == "no_fault":
            # Reaching this instruction IS the assertion: a fault would have
            # stopped the program. (The emulator leg can only ever return PASS
            # for `no_fault`; here it is a real observation.)
            p.emit("LI   r%d, 1" % R_FLAG, "no_fault: reached => did not fault")
        elif kind == "reg_value":
            p.li64(R_T, int(a["rd"], 16), "derived expectation")
            p.eq_flag(R_FLAG, R_RES, R_T)
        elif kind == "bits_zero_above":
            p.emit("LSRI r%d, r%d, %d" % (R_T, R_RES, a["bit"]), "bits above %d" % a["bit"])
            p.emit("SLTU r%d, r0, r%d" % (R_FLAG, R_T))
            p.emit("XORI r%d, r%d, 1" % (R_FLAG, R_FLAG))
        elif kind == "same_as":
            p.li64(R_A, int(a["inputs"]["rs1"], 16), "reference rs1")
            if v["form"] == "rrr":
                p.li64(R_B, int(a["inputs"]["rs2"], 16), "reference rs2")
            p.do_op(R_T, v["op"], v["form"], R_A, R_B)
            p.eq_flag(R_FLAG, R_RES, R_T)
        else:
            raise AssertionError("unmechanised assertion kind %r reached codegen" % kind)

        # fold into the bitmap and the mismatch counter
        p.emit("LSLI r%d, r%d, %d" % (R_U, R_FLAG, g % 64))
        p.emit("OR   r%d, r%d, r%d" % (R_BITMAP[g // 64], R_BITMAP[g // 64], R_U))
        p.emit("XORI r%d, r%d, 1" % (R_U, R_FLAG))
        p.emit("ADD  r%d, r%d, r%d" % (R_MISMATCH, R_MISMATCH, R_U))

    p.owner = None
    p.note("")
    p.note("; --- epilogue: publish the readout to the zero page, then halt ---")
    p.emit("LI   r%d, %d" % (R_NVEC, len(vectors)))
    for w, r in enumerate(R_BITMAP):
        p.emit("SD   [r0, %d], r%d" % (BITMAP_BASE + WORD * w, r))
    p.emit("SD   [r0, %d], r%d" % (MISMATCH_ADDR, R_MISMATCH))
    p.emit("SD   [r0, %d], r%d" % (NVEC_ADDR, R_NVEC))
    p.emit("EXIT r0")
    return p


def gen_diagnostic(items):
    """A tiny program that puts (got, reference) for up to 4 vectors into
    r1..r8, so a mismatch can be reported as expected-vs-got instead of just a
    zero bit. `items` is a list of (g, vector)."""
    p = Prog()
    p.note("; conformance_hw diagnostic -- GENERATED. got/reference pairs in r1..r8.")
    p.note(".text")
    for j, (g, v) in enumerate(items):
        rg, rr = 2 * j + 1, 2 * j + 2
        a = v["assertion"]
        p.note("; vector %s" % v["id"])
        p.li64(R_A, int(v["inputs"]["rs1"], 16))
        if v["form"] == "rrr":
            p.li64(R_B, int(v["inputs"]["rs2"], 16))
        p.do_op(rg, v["op"], v["form"], R_A, R_B)
        if a["kind"] == "reg_value":
            p.li64(rr, int(a["rd"], 16))
        elif a["kind"] == "bits_zero_above":
            p.emit("LSRI r%d, r%d, %d" % (rr, rg, a["bit"]))
        elif a["kind"] == "same_as":
            p.li64(R_A, int(a["inputs"]["rs1"], 16))
            if v["form"] == "rrr":
                p.li64(R_B, int(a["inputs"]["rs2"], 16))
            p.do_op(rr, v["op"], v["form"], R_A, R_B)
        else:
            p.emit("LI   r%d, 0" % rr)
    p.emit("EXIT r0")
    return p


def one_line(s):
    return re.sub(r"\s+", " ", s).strip()


# --------------------------------------------------------------------------
# execution
# --------------------------------------------------------------------------

def assemble(binary, src_path, hex_path):
    r = subprocess.run([str(binary), "asm-flat-exec", str(src_path), "-o", str(hex_path)],
                       capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit("conformance_hw: assemble FAILED\n" + (r.stdout + r.stderr).strip())


def parse_state(text):
    """The common Design / testbench readout."""
    st = {"trap": None, "halted": None, "regs": {}, "dmem32": None}
    for line in text.splitlines():
        m = re.match(r"^TRAP op=([0-9a-fA-F]+) pc=(\d+)", line)
        if m:
            st["trap"] = (m.group(1), int(m.group(2)))
        m = re.match(r"^HALTED=(\d+)", line)
        if m:
            st["halted"] = int(m.group(1))
        m = re.match(r"^r(\d+)=(\d+)$", line)
        if m:
            st["regs"][int(m.group(1))] = int(m.group(2))
        m = re.match(r"^dmem32=(\d+)", line)
        if m:
            st["dmem32"] = int(m.group(1))
    return st


def run_design(hex_path):
    exe = LEAN_HW / ".lake" / "build" / "bin" / "minitest"
    if not exe.is_file():
        sys.exit("conformance_hw: %s not built" % exe)
    r = subprocess.run([str(exe), "designexpect", str(hex_path)],
                       capture_output=True, text=True, cwd=str(LEAN_HW))
    if r.returncode != 0:
        sys.exit("conformance_hw: Design run FAILED\n" + (r.stdout + r.stderr).strip())
    return r.stdout


def run_rtl(hex_path, workdir):
    """Same invocation isa_smoke.sh uses."""
    soc = LEAN_HW / "rtl" / "lnp64mini_soc.v"
    tb = LEAN_HW / "fpga" / "zc702" / "tb_lnp64mini_soc.v"
    vvp = pathlib.Path(workdir) / "a.vvp"
    b = subprocess.run(["iverilog", "-g2012", '-DPROG_HEX="%s"' % hex_path,
                        "-o", str(vvp), str(soc), str(tb)],
                       capture_output=True, text=True)
    if b.returncode != 0:
        sys.exit("conformance_hw: iverilog build FAILED\n" + (b.stdout + b.stderr).strip())
    r = subprocess.run(["vvp", str(vvp)], capture_output=True, text=True)
    keep = [re.sub(r" cycles=\d+", "", l) for l in r.stdout.splitlines()
            if re.match(r"^(TRAP|HALTED|r\d+=|dmem32=)", l)]
    return "\n".join(keep) + "\n"


# --------------------------------------------------------------------------
# the mnemonic <-> opcode-table cross-check
# --------------------------------------------------------------------------

def verify_mnemonics(binary, opcodes, ops, workdir, log):
    """Assemble one probe instruction per op and check the byte the ASSEMBLER
    emitted equals isa_opcodes.json's byte for the spec name. This is what
    licenses ASM_ALIAS (`sll` -> `LSL`) without writing a number down, and it
    fails loudly if the assembler and the table drift apart."""
    probes, order = [], []
    for op in ops:
        form = "rrr" if op in RRR_PROBE else "rr"
        m = asm_mnemonic(op)
        probes.append("  %s r3, r1, r2" % m if form == "rrr" else "  %s r3, r1" % m)
        order.append(op)
    src = pathlib.Path(workdir) / "probe.s"
    hx = pathlib.Path(workdir) / "probe.hex"
    src.write_text(".text\n" + "\n".join(probes) + "\n  EXIT r0\n")
    assemble(binary, src, hx)
    words = [int(l.strip(), 16) for l in hx.read_text().splitlines() if l.strip()]
    bad = []
    for op, w in zip(order, words):
        want = opcodes.get(op)
        if want is None:
            bad.append("%s: absent from isa_opcodes.json" % op)
        elif (w >> 56) != want:
            bad.append("%s: assembler mnemonic %s emits byte 0x%02x, "
                       "isa_opcodes.json says 0x%02x"
                       % (op, asm_mnemonic(op), w >> 56, want))
    if bad:
        sys.exit("conformance_hw: mnemonic/opcode-table disagreement\n  " + "\n  ".join(bad))
    log("mnemonic check: %d ops resolved through the assembler and matched "
        "isa_opcodes.json" % len(order))


RRR_PROBE = {"sll", "srl", "sra", "mul", "mulh", "mulhu",
             "div", "udiv", "srem", "urem"}


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------

def can_convert(v):
    """-> (True, None) or (False, reason). Never guesses at an expectation."""
    if not v.get("runnable", True):
        r = v.get("blocked_reason") or "marked not runnable by the derivation"
        extra = []
        if v.get("w_form"):
            extra.append("the assembler has no W-form mnemonic and "
                         "Machines/Lnp64mini/Core.lean decodes no [0]=W bit either, "
                         "so this leg cannot express it any more than step-op can")
        return False, r + ((" | lnp64mini: " + "; ".join(extra)) if extra else "")
    if v["form"] == "sequence":
        return False, ("multi-op sequence: needs `max`, which is in isa_opcodes.json "
                       "but has no assembler mnemonic and no lnp64mini decode")
    if v["form"] not in ("rr", "rrr"):
        return False, "unsupported form %r" % v["form"]
    if v["assertion"]["kind"] not in ("no_fault", "reg_value", "bits_zero_above", "same_as"):
        return False, "assertion kind %r is not mechanisable as a register comparison" \
                      % v["assertion"]["kind"]
    return True, None


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rtl", action="store_true",
                    help="also run the same .hex on rtl/lnp64mini_soc.v under "
                         "iverilog and require RTL == Design == expected")
    ap.add_argument("--keep", metavar="DIR", default=str(LEAN_HW / "fpga" / "zc702"),
                    help="where to write conformance_hw.s / .hex "
                         "(the board leg reads these)")
    ap.add_argument("--max-traps", type=int, default=60,
                    help="give up after this many trap-attribution rounds")
    args = ap.parse_args()

    def log(s=""):
        print(s, flush=True)

    root, binary = lnp64_paths()
    vecfile = root / "conformance_pinned.json"
    doc = json.loads(vecfile.read_text())
    opcodes = {name: int(b, 16) for b, name in
               json.loads((root / "isa_opcodes.json").read_text()).items()}
    sections = doc.get("sections") or []
    sections = "%s %s" % (doc.get("spec", "lnp64_isa.md"),
                          ",".join("§%s" % s for s in sections) or "§4-§6")

    log("conformance_hw: %s family %r" % (vecfile, doc.get("family")))
    log("  vectors in file: %d" % len(doc["vectors"]))

    convertible, skipped = [], []
    for v in doc["vectors"]:
        ok, why = can_convert(v)
        (convertible if ok else skipped).append(v if ok else (v, why))

    n_conv = len(convertible)
    if n_conv > BITMAP_WORDS * 64:
        sys.exit("conformance_hw: %d vectors exceed the %d-bit bitmap"
                 % (n_conv, BITMAP_WORDS * 64))
    if SLOT_BASE + WORD * n_conv > DMEM_WORDS * WORD:
        sys.exit("conformance_hw: result slots overflow the %d-word zero page" % DMEM_WORDS)

    ops = sorted({v["op"] for v in convertible})
    workdir = tempfile.mkdtemp(prefix="conformance_hw.")
    try:
        verify_mnemonics(binary, opcodes, ops, workdir, log)

        keep = pathlib.Path(args.keep)
        keep.mkdir(parents=True, exist_ok=True)
        src = keep / "conformance_hw.s"
        hx = keep / "conformance_hw.hex"

        indexed = list(enumerate(convertible))     # (global index g, vector)
        live = list(indexed)
        trapped = []          # (g, vector, trap_op, pc)
        state = None
        design_text = ""
        first_prog_hex = None

        for rnd in range(args.max_traps + 1):
            p = gen_program(live, n_conv, str(vecfile), sections)
            src.write_text(p.text())
            assemble(binary, src, hx)
            if first_prog_hex is None:
                first_prog_hex = str(pathlib.Path(workdir) / "first.hex")
                shutil.copyfile(hx, first_prog_hex)
            log("  round %d: %d vectors, %d instructions" % (rnd, len(live), p.n_instr()))
            design_text = run_design(hx)
            state = parse_state(design_text)
            if state["trap"] is None:
                break
            op_hex, pc = state["trap"]
            idx = (pc - TEXT_BASE) // WORD
            owners = p.pc_owner_map()
            if not (0 <= idx < len(owners)) or owners[idx] is None:
                sys.exit("conformance_hw: TRAP op=%s at pc=%d (instruction %d) is not "
                         "inside any vector -- the harness itself faulted, which is a "
                         "bug in this script, not a conformance result" % (op_hex, pc, idx))
            g = owners[idx]
            vec = dict(indexed)[g]
            trapped.append((g, vec, op_hex, pc))
            log("    TRAP op=0x%s pc=%d -> vector %s; removing it and re-running"
                % (op_hex, pc, vec["id"]))
            live = [(gi, vv) for gi, vv in live if gi != g]
        else:
            sys.exit("conformance_hw: still trapping after %d rounds" % args.max_traps)

        if state["halted"] != 1:
            sys.exit("conformance_hw: FAILED -- the program did not run to a clean halt "
                     "(HALTED=%s). isa_smoke.sh:57-66: a program that does not halt "
                     "cleanly proves nothing about the bytes it never reached."
                     % state["halted"])

        # ---- read the architectural bitmap back ----
        bits = 0
        for w, r in enumerate(R_BITMAP):
            bits |= state["regs"].get(r, 0) << (64 * w)
        executed = {g for g, _ in live}
        passed = {g for g in executed if (bits >> g) & 1}
        failed = sorted(executed - passed)
        if state["regs"].get(R_MISMATCH) != len(failed):
            sys.exit("conformance_hw: internal inconsistency -- r%d says %s mismatches, "
                     "the bitmap says %d" % (R_MISMATCH, state["regs"].get(R_MISMATCH),
                                             len(failed)))
        if state["regs"].get(R_NVEC) != len(live):
            sys.exit("conformance_hw: internal inconsistency -- r%d says %s vectors "
                     "executed, %d were emitted" % (R_NVEC, state["regs"].get(R_NVEC),
                                                    len(live)))
        if (bits >> n_conv) != 0:
            sys.exit("conformance_hw: bitmap has bits set above the vector count")

        # ---- RTL leg ----
        rtl_report = None
        if args.rtl:
            if shutil.which("iverilog") is None:
                rtl_report = ("SKIP", "iverilog not found")
            else:
                rtl_text = run_rtl(hx, workdir)
                design_keep = "\n".join(re.sub(r" cycles=\d+", "", l)
                                     for l in design_text.splitlines()) + "\n"
                if rtl_text != design_keep:
                    rtl_report = ("MISMATCH", "RTL:\n" + rtl_text + "Design:\n" + design_keep)
                else:
                    rtl_report = ("OK", "")
                    # The RTL must also trap where the Design trapped -- otherwise
                    # the removal above hid a divergence rather than a finding.
                    if trapped:
                        first_rtl = parse_state(run_rtl(first_prog_hex, workdir))
                        first_design = parse_state(run_design(first_prog_hex))
                        if first_rtl["trap"] != first_design["trap"]:
                            rtl_report = ("MISMATCH",
                                          "first-trap disagreement: RTL %s, Design %s"
                                          % (first_rtl["trap"], first_design["trap"]))

        # ---- diagnostics for non-trap mismatches ----
        detail = {}
        for i in range(0, len(failed), 4):
            chunk = [(g, dict(indexed)[g]) for g in failed[i:i + 4]]
            d = gen_diagnostic(chunk)
            dsrc = pathlib.Path(workdir) / ("diag%d.s" % i)
            dhex = pathlib.Path(workdir) / ("diag%d.hex" % i)
            dsrc.write_text(d.text())
            assemble(binary, dsrc, dhex)
            ds = parse_state(run_design(dhex))
            if ds["halted"] != 1:
                continue
            for j, (g, _) in enumerate(chunk):
                detail[g] = (ds["regs"].get(2 * j + 1), ds["regs"].get(2 * j + 2))

        report(doc, indexed, live, passed, failed, trapped, skipped, detail,
               state, rtl_report, src, hx, sections, log)

        bad = len(failed) + len(trapped)
        if rtl_report and rtl_report[0] == "MISMATCH":
            bad += 1
        return 1 if bad else 0
    finally:
        shutil.rmtree(workdir, ignore_errors=True)


def report(doc, indexed, live, passed, failed, trapped, skipped, detail,
           state, rtl_report, src, hx, sections, log):
    byg = dict(indexed)
    rules = {}
    for g, v in indexed:
        r = rules.setdefault(v["rule"], {"pass": 0, "fail": 0, "trap": 0})
        if g in passed:
            r["pass"] += 1
        elif any(t[0] == g for t in trapped):
            r["trap"] += 1
        else:
            r["fail"] += 1
    skip_rules = {}
    for v, why in skipped:
        skip_rules.setdefault(v["rule"], {"n": 0, "why": why})["n"] += 1

    log()
    log("=" * 78)
    log("PER-RULE RESULT (lnp64mini, one batched program, Design-derived simulator)")
    log("%-24s %6s %6s %6s %8s" % ("rule", "pass", "fail", "trap", "skipped"))
    tot = [0, 0, 0, 0]
    for r in sorted(set(list(rules) + list(skip_rules))):
        c = rules.get(r, {"pass": 0, "fail": 0, "trap": 0})
        s = skip_rules.get(r, {"n": 0})["n"]
        log("%-24s %6d %6d %6d %8d" % (r, c["pass"], c["fail"], c["trap"], s))
        tot[0] += c["pass"]; tot[1] += c["fail"]; tot[2] += c["trap"]; tot[3] += s
    log("%-24s %6d %6d %6d %8d" % ("TOTAL", *tot))
    log()
    log("converted : %d   (executed %d, removed after trapping %d)"
        % (len(indexed), len(live), len(trapped)))
    log("skipped   : %d" % len(skipped))
    log("failed    : %d   (%d wrong value, %d trapped)"
        % (len(failed) + len(trapped), len(failed), len(trapped)))
    log()

    if skipped:
        log("-" * 78)
        log("SKIPPED, WITH REASONS (not silently dropped)")
        groups = {}
        for v, why in skipped:
            groups.setdefault((v["rule"], why), []).append(v["id"])
        for (r, why), ids in sorted(groups.items()):
            log("  %-22s %3d vectors" % (r, len(ids)))
            log("      %s" % one_line(why))
        log()

    if trapped or failed:
        log("-" * 78)
        log("FINDINGS -- the core disagrees with a spec-derived expectation.")
        log("No expectation was adjusted. Each is quoted with its frozen sentence.")
        for g, v, op_hex, pc in trapped:
            log()
            log("  FAIL(TRAP) %s   rule=%s op=%s form=%s"
                % (v["id"], v["rule"], v["op"], v["form"]))
            log("     inputs   : %s" % v["inputs"])
            log("     expected : %s" % describe_expect(v))
            log("     got      : TRAP op=0x%s at pc=%d -- the instruction faulted; "
                "the spec pins a value here" % (op_hex, pc))
            log("     %s:%d" % (sections, v["provenance"]["spec_line"]))
            log("     > %s" % one_line(v["provenance"]["sentence"]))
        for g in failed:
            v = byg[g]
            got, ref = detail.get(g, (None, None))
            log()
            log("  FAIL %s   rule=%s op=%s form=%s"
                % (v["id"], v["rule"], v["op"], v["form"]))
            log("     inputs   : %s" % v["inputs"])
            log("     expected : %s" % describe_expect(v))
            if got is not None:
                log("     got      : 0x%016x   (reference 0x%016x)" % (got, ref))
            else:
                log("     got      : (bitmap bit %d clear; diagnostic run unavailable)" % g)
            log("     %s:%d" % (sections, v["provenance"]["spec_line"]))
            log("     > %s" % one_line(v["provenance"]["sentence"]))
        log()

    log("-" * 78)
    log("artifacts : %s" % src)
    log("            %s   (the board runs this byte-for-byte)" % hx)
    log("readout   : pass bitmap r5..r1 = %s"
        % " ".join("%016x" % state["regs"].get(r, 0) for r in reversed(R_BITMAP)))
    log("            r6 mismatches = %d, r7 executed = %d, dmem32 (vector 0) = 0x%x"
        % (state["regs"].get(R_MISMATCH, -1), state["regs"].get(R_NVEC, -1),
           state["dmem32"] or 0))
    if rtl_report:
        log("rtl leg   : %s %s" % rtl_report)
    else:
        log("rtl leg   : not run (pass --rtl)")
    ok = not failed and not trapped and (not rtl_report or rtl_report[0] != "MISMATCH")
    log()
    log("conformance_hw: %s" % ("OK -- every converted vector matches the derived "
                                "expectation on lnp64mini"
                                if ok else "FAILURES ABOVE (see findings)"))


def describe_expect(v):
    a = v["assertion"]
    if a["kind"] == "reg_value":
        return "rd = %s" % a["rd"]
    if a["kind"] == "bits_zero_above":
        return "rd bits above bit %d are zero" % a["bit"]
    if a["kind"] == "same_as":
        return "rd equal to the same op with %s (%s)" % (a["inputs"], a.get("note", ""))
    if a["kind"] == "no_fault":
        return "the instruction does not fault"
    return str(a)


if __name__ == "__main__":
    sys.exit(main())
