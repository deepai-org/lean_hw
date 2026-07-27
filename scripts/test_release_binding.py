#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for the trusted exact-file association step."""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = """\
def diskWireTree : Rope (List String) :=
  .node (.leaf diskWireBlock0000) (.leaf diskWireBlock0001)

def diskMem0InitTree : Rope (List String) :=
  .node (.leaf diskMem0Init0000) (.leaf diskMem0Init0001)

def diskMem0Tree : Rope (List String) :=
  .node (.leaf diskMem0Start)
    (.node diskMem0InitTree (.leaf diskMem0End))

def diskMemTrees : Rope (List String) :=
  diskMem0Tree

def diskTree : Rope (List String) :=
  .node (.leaf diskPrefix)
    (.node diskMemTrees (.node diskWireTree (.leaf diskSuffix)))

"""

# `diskPrefix` and `diskSuffix` mirror the blocked generator: both are append
# trees over separately named leaves, not single literals. The checker recovers
# byte order from those appends, so the fixture must exercise that shape.
LEAVES = """\
def diskPrefix : List String :=
  diskHeader ++ (diskRegDeclBlock0000 ++ diskMemDecls)

def diskSuffix : List String :=
  diskAlwaysStart ++ (diskRegResetBlock0000 ++ (diskAlwaysMiddle ++
    (diskRegNextBlock0000 ++ (diskMemWrites ++ (diskAlwaysEnd ++
    (diskOutBlock0000 ++ diskModuleEnd))))))

def diskHeader : List String := ["header"]
def diskRegDeclBlock0000 : List String := ["reg-decl"]
def diskMemDecls : List String := ["mem-decls"]
def diskMem0Start : List String := ["mem-start"]
def diskMem0Init0000 : List String := ["mem-0"]
def diskMem0Init0001 : List String := ["mem-1"]
def diskMem0End : List String := ["mem-end"]
def diskWireBlock0000 : List String := ["wire-0"]
def diskWireBlock0001 : List String := ["wire-1"]
def diskAlwaysStart : List String := ["always-start"]
def diskRegResetBlock0000 : List String := ["reg-reset"]
def diskAlwaysMiddle : List String := ["always-middle"]
def diskRegNextBlock0000 : List String := ["reg-next"]
def diskMemWrites : List String := ["mem-writes"]
def diskAlwaysEnd : List String := ["always-end"]
def diskOutBlock0000 : List String := ["out"]
def diskModuleEnd : List String := ["module-end"]
"""

BYTES = b"\n".join([
    b"header", b"reg-decl", b"mem-decls",
    b"mem-start", b"mem-0", b"mem-1", b"mem-end",
    b"wire-0", b"wire-1",
    b"always-start", b"reg-reset", b"always-middle", b"reg-next",
    b"mem-writes", b"always-end", b"out", b"module-end",
])


def check(checker: Path, rtl: Path, generated: Path, succeeds: bool) -> None:
    result = subprocess.run(
        [sys.executable, str(checker), str(rtl), str(generated)],
        text=True, capture_output=True)
    if (result.returncode == 0) != succeeds:
        raise SystemExit(
            f"unexpected binder result {result.returncode}: "
            f"{result.stdout}{result.stderr}")


def main() -> None:
    checker = Path(__file__).with_name("check_release_binding.py").resolve()
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        generated = directory / "Generated"
        generated.mkdir()
        root = generated / "Root.lean"
        root.write_text(ROOT + LEAVES)
        rtl = directory / "artifact.v"
        rtl.write_bytes(BYTES)
        check(checker, rtl, generated, True)

        # The same declarations with a theorem-tree permutation must fail even
        # though a naming-convention-only reconstruction would still match.
        root.write_text((ROOT.replace(
            ".node (.leaf diskWireBlock0000) (.leaf diskWireBlock0001)",
            ".node (.leaf diskWireBlock0001) (.leaf diskWireBlock0000)") +
            LEAVES))
        check(checker, rtl, generated, False)

        root.write_text(ROOT + LEAVES)
        rtl.write_bytes(BYTES + b"\n")
        check(checker, rtl, generated, False)

    print("release binding tests passed: exact bytes and theorem-tree order")


if __name__ == "__main__":
    main()
