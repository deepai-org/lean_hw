#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# A standing lint for opcode numbers written down twice.
#
# Every defect that survived the 2026-08-05 renumbering attempt was this one
# hazard in a different costume:
#
#   * `is_alu` held raw bytes 0x1c/0xa5/0xa6/0x1e from the old map;
#   * `is_branch` captured OP_SLTU where OP_BGEU belonged, because the list
#     replaced a numeric RANGE;
#   * `ld_wb` selected load extension with 0x05/0x08 -- the one that shipped in
#     the bitstream and broke the board;
#   * the harness's test PROGRAMS encoded 0x33/0x35/0x21 directly;
#   * `Core.lean` defined CAP_SEND_OP := 0x3e beside OP_MINI_CAP_SEND;
#   * `diff_emulator_iss.py` carried its own opcode table;
#   * four hand-written `.quad` instruction encodings bypass the LLVM backend
#     entirely, so no renumbering can reach them.
#
# A literal does not move when the numbering does. This finds them before the
# next renumbering does, and after one it can also scan for the OLD values with
# --old-map.

import argparse
import json
import pathlib
import re
import sys

HW = pathlib.Path(__file__).resolve().parent.parent
ROOTS = [HW / "Machines", HW / "Loom", HW / "fpga", HW / "scripts"]
EXTS = {".lean", ".py", ".v", ".s", ".S", ".tcl", ".c", ".h", ".rs"}

# Sites where a raw encoding is intentional and cannot be generated. Each must
# carry its own explanation at the site; this list is the index, not the excuse.
ALLOWED = {
    "lnp64_intrinsics.h", "lnp64_smp.h",          # .quad SLEEP encodings
    "liblnp64_time_min.c", "liblnp64_fd_min.c",   # .quad SLEEP encodings
    "isa_target_map.json", "isa_host_relocation.json",
    "check_opcode_literals.py",                    # this file
    "check_opcode_coverage.py",
    "ISA_CONFORMANCE.md", "EXTEND_SPEC.md",
}


def design_opcodes():
    src = (HW / "Machines/Lnp64mini/Core.lean").read_text()
    return {int(m.group(2), 16): m.group(1)
            for m in re.finditer(r"^def OP_([A-Z0-9_]+) : Nat := (0x[0-9a-f]+)",
                                 src, re.M)}


def scan(values, label):
    """Report hex literals matching any opcode value, in opcode-ish contexts."""
    hits = []
    pats = [
        re.compile(r"encImm[ISJ]?\s+(0x[0-9a-f]{2})\b"),
        re.compile(r"\benc\s+(0x[0-9a-f]{2})\b"),
        re.compile(r"L8\s+(0x[0-9a-f]{2})\b"),
        re.compile(r"\.quad\s+(0x[0-9a-f]{2})[0-9a-f]{14}\b"),
        re.compile(r"opN\s+s\s*=\s*(0x[0-9a-f]{2})\b"),
        # A second constant holding an opcode value. The OP_ definitions
        # themselves are the single source of truth and are excluded; anything
        # ELSE defined as a bare opcode byte is a duplicate, which is exactly
        # what CAP_SEND_OP := 0x3e was.
        re.compile(r"^def\s+(?!OP_)[A-Z_][A-Z_0-9]*\s*:\s*Nat\s*:=\s*(0x[0-9a-f]{2})$", re.M),
    ]
    for root in ROOTS:
        if not root.exists():
            continue
        for f in root.rglob("*"):
            if not f.is_file() or f.suffix not in EXTS:
                continue
            if f.name in ALLOWED:
                continue
            try:
                txt = f.read_text()
            except Exception:
                continue
            for pat in pats:
                for m in pat.finditer(txt):
                    v = int(m.group(1), 16)
                    if v in values:
                        line = txt[:m.start()].count("\n") + 1
                        hits.append((f.relative_to(HW), line,
                                     m.group(0).strip(), values[v]))
    return hits


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--old-map", help="JSON of the PREVIOUS numbering; after a "
                                      "renumber, scan for leftovers of it")
    args = ap.parse_args()

    cur = design_opcodes()
    hits = scan(cur, "current")
    rc = 0
    if hits:
        print(f"opcode literals: {len(hits)} raw value(s) that a renumbering "
              f"would not move")
        for f, ln, txt, name in hits:
            print(f"  {f}:{ln}  {txt}   (= OP_{name})")
        print("\n  Use the named constant, or add the file to ALLOWED with the")
        print("  reason written at the site. A literal is a second source of")
        print("  truth for a number that has one.")
        rc = 1
    else:
        print("check_opcode_literals: ok — no raw opcode values outside the "
              "allowed sites")

    if args.old_map:
        old = {int(v, 16): k for k, v in json.load(open(args.old_map)).items()}
        stale = scan(old, "old")
        stale = [h for h in stale if h not in hits]
        if stale:
            print(f"\n  LEFTOVERS OF THE PREVIOUS NUMBERING: {len(stale)}")
            for f, ln, txt, name in stale:
                print(f"    {f}:{ln}  {txt}   (was OP_{name})")
            rc = 1
    return rc


if __name__ == "__main__":
    sys.exit(main())
