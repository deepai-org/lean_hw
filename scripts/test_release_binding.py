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

LEAVES = """\
def diskPrefix : List String := ["prefix"]
def diskMem0Start : List String := ["mem-start"]
def diskMem0Init0000 : List String := ["mem-0"]
def diskMem0Init0001 : List String := ["mem-1"]
def diskMem0End : List String := ["mem-end"]
def diskWireBlock0000 : List String := ["wire-0"]
def diskWireBlock0001 : List String := ["wire-1"]
def diskSuffix : List String := ["suffix"]
"""

BYTES = b"prefix\nmem-start\nmem-0\nmem-1\nmem-end\nwire-0\nwire-1\nsuffix"


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
