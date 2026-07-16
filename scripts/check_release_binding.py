#!/usr/bin/env python3
"""Exact byte binding between generated Lean disk leaves and shipped RTL.

This intentionally tiny checker is the release pipeline's one external byte
comparison. It reads the literal `disk*` list declarations that occur in the
kernel-checked proof modules, reconstructs their theorem-defined order, and
compares the resulting UTF-8 bytes exactly with the `.v` file.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


START = re.compile(r"^def (disk\w+) : List String := \[$")
INLINE = re.compile(r"^def (disk\w+) : List String := \[(.*)\]$")


def declarations(directory: Path) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    for source in sorted(directory.glob("*.lean")):
        lines = source.read_text().splitlines()
        i = 0
        while i < len(lines):
            inline = INLINE.fullmatch(lines[i])
            if inline:
                values = [] if not inline[2] else [json.loads(inline[2])]
                if inline[1] in result:
                    raise ValueError(f"duplicate disk declaration {inline[1]}")
                result[inline[1]] = values
                i += 1
                continue
            start = START.fullmatch(lines[i])
            if not start:
                i += 1
                continue
            values: list[str] = []
            i += 1
            while i < len(lines) and lines[i] != "]":
                text = lines[i].strip()
                if text.endswith(","):
                    text = text[:-1]
                values.append(json.loads(text))
                i += 1
            if i == len(lines):
                raise ValueError(f"unterminated disk declaration {start[1]}")
            if start[1] in result:
                raise ValueError(f"duplicate disk declaration {start[1]}")
            result[start[1]] = values
            i += 1
    return result


def ordered_names(values: dict[str, list[str]]) -> list[str]:
    names = ["diskPrefix"]
    memory = 0
    while f"diskMem{memory}Start" in values:
        names.append(f"diskMem{memory}Start")
        names += sorted(name for name in values
                        if re.fullmatch(rf"diskMem{memory}Init\d{{4}}", name))
        names.append(f"diskMem{memory}End")
        memory += 1
    names += sorted(name for name in values
                    if re.fullmatch(r"diskWireBlock\d{4}", name))
    names.append("diskSuffix")
    return names


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("rtl", type=Path)
    parser.add_argument("generated", type=Path)
    args = parser.parse_args()
    values = declarations(args.generated)
    names = ordered_names(values)
    missing = [name for name in names if name not in values]
    if missing:
        raise SystemExit(f"missing disk declarations: {', '.join(missing)}")
    used = {name for name in names}
    unexpected = sorted(name for name in values if name not in used)
    if unexpected:
        raise SystemExit(f"unbound disk declarations: {', '.join(unexpected)}")
    certified = "\n".join(line for name in names for line in values[name]).encode()
    actual = args.rtl.read_bytes()
    if certified != actual:
        mismatch = next((i for i, pair in enumerate(zip(certified, actual))
                         if pair[0] != pair[1]), min(len(certified), len(actual)))
        raise SystemExit(
            f"byte mismatch at offset {mismatch}: certified={len(certified)} "
            f"actual={len(actual)}")
    print(f"exact byte binding passed: {args.rtl} ({len(actual)} bytes)")


if __name__ == "__main__":
    main()
