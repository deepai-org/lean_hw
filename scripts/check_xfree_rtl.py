#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Reject obvious 4-state / uninitialized-state hazards in emitted µVerilog.

This is a text-level CI tripwire for the generated core RTL, not a substitute
for the Lean µVerilog semantics.  It checks the exact bytes produced by
`lake exe emit` for hazards that would invalidate the project's 2-state
BitVec model: X/Z/don't-care literals or constructs, un-reset registers, and
partially initialized memories.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


IDENT = r"[A-Za-z_][A-Za-z0-9_$]*"
REG_RE = re.compile(rf"^\s*reg\s+\[(\d+):0\]\s+({IDENT})\s*;\s*$")
MEM_RE = re.compile(rf"^\s*reg\s+\[(\d+):0\]\s+({IDENT})\s+\[0:(\d+)\]\s*;\s*$")
RESET_RE = re.compile(rf"^\s*({IDENT})\s*<=\s*(\d+)'d(\d+)\s*;\s*$")
INIT_RE = re.compile(rf"^\s*({IDENT})\[(\d+)\]\s*=\s*(\d+)'d(\d+)\s*;\s*$")
LITERAL_RE = re.compile(r"(?<![A-Za-z0-9_$])(?:\d+)?'[sS]?[bBoOdDhH]([0-9A-Fa-f_xXzZ?]+)")
FORBIDDEN_RE = re.compile(
    r"\b(inout|tri|tri0|tri1|wand|wor|supply0|supply1|pullup|pulldown|"
    r"casex|casez|force|release|deassign)\b|===|!==",
    re.IGNORECASE,
)


def strip_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    return "\n".join(line.split("//", 1)[0] for line in text.splitlines())


def literal_value_ok(width: int, value: int) -> bool:
    return value < (1 << width)


def check_file(path: Path) -> list[str]:
    errors: list[str] = []
    text = strip_comments(path.read_text())
    lines = text.splitlines()

    for lineno, line in enumerate(lines, 1):
        for lit in LITERAL_RE.finditer(line):
            digits = lit.group(1)
            if any(c in "xXzZ?" for c in digits):
                errors.append(f"{path}:{lineno}: 4-state/don't-care literal `{lit.group(0)}`")
        if FORBIDDEN_RE.search(line):
            errors.append(f"{path}:{lineno}: forbidden 4-state/special construct `{line.strip()}`")

    regs: dict[str, int] = {}
    mems: dict[str, tuple[int, int]] = {}
    for lineno, line in enumerate(lines, 1):
        if m := REG_RE.match(line):
            regs[m.group(2)] = int(m.group(1)) + 1
        elif m := MEM_RE.match(line):
            mems[m.group(2)] = (int(m.group(1)) + 1, int(m.group(3)))

    reset_seen: dict[str, int] = {}
    in_reset = False
    for lineno, line in enumerate(lines, 1):
        if re.match(r"^\s*if\s*\(\s*rst\s*\)\s*begin\s*$", line):
            in_reset = True
            continue
        if in_reset and re.match(r"^\s*end\s+else\s+begin\s*$", line):
            in_reset = False
            continue
        if not in_reset or not line.strip():
            continue
        m = RESET_RE.match(line)
        if not m:
            errors.append(f"{path}:{lineno}: non-literal or unparsable reset assignment `{line.strip()}`")
            continue
        name, width_s, value_s = m.group(1), m.group(2), m.group(3)
        width = int(width_s)
        value = int(value_s)
        if name not in regs:
            errors.append(f"{path}:{lineno}: reset assignment to undeclared reg `{name}`")
        elif regs[name] != width:
            errors.append(f"{path}:{lineno}: reset width {width} for `{name}`, declared {regs[name]}")
        elif not literal_value_ok(width, value):
            errors.append(f"{path}:{lineno}: reset literal for `{name}` exceeds {width} bits")
        reset_seen[name] = lineno

    missing_regs = sorted(set(regs) - set(reset_seen))
    for name in missing_regs:
        errors.append(f"{path}: reg `{name}` has no explicit reset assignment")

    init_seen: dict[str, set[int]] = {name: set() for name in mems}
    for lineno, line in enumerate(lines, 1):
        m = INIT_RE.match(line)
        if not m:
            continue
        name, idx_s, width_s, value_s = m.group(1), m.group(2), m.group(3), m.group(4)
        idx = int(idx_s)
        width = int(width_s)
        value = int(value_s)
        if name not in mems:
            errors.append(f"{path}:{lineno}: init assignment to undeclared memory `{name}`")
            continue
        data_width, max_idx = mems[name]
        if idx > max_idx:
            errors.append(f"{path}:{lineno}: init index {idx} exceeds `{name}` max {max_idx}")
        elif width != data_width:
            errors.append(f"{path}:{lineno}: init width {width} for `{name}`, declared {data_width}")
        elif not literal_value_ok(width, value):
            errors.append(f"{path}:{lineno}: init literal for `{name}[{idx}]` exceeds {width} bits")
        init_seen[name].add(idx)

    for name, (data_width, max_idx) in mems.items():
        expected = max_idx + 1
        seen = init_seen[name]
        if len(seen) != expected:
            missing = [i for i in range(expected) if i not in seen][:8]
            errors.append(
                f"{path}: memory `{name}` has {len(seen)}/{expected} explicit init words "
                f"(data width {data_width}); first missing {missing}"
            )

    return errors


def main(argv: list[str]) -> int:
    if not argv:
        print("usage: check_xfree_rtl.py FILE.v [...]", file=sys.stderr)
        return 2
    all_errors: list[str] = []
    for arg in argv:
        all_errors.extend(check_file(Path(arg)))
    if all_errors:
        print("xfree-rtl: FAIL", file=sys.stderr)
        for err in all_errors[:50]:
            print(err, file=sys.stderr)
        if len(all_errors) > 50:
            print(f"... {len(all_errors) - 50} more errors", file=sys.stderr)
        return 1
    print("xfree-rtl: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
