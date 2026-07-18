#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Identify a generated Lean source tree for a determinism comparison.

This hash is a build-hygiene signal, never proof evidence. Exact RTL binding
continues to use byte comparison rather than collision resistance.
"""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: generated_tree_digest.py DIRECTORY")
    root = Path(sys.argv[1])
    digest = hashlib.sha256()
    for source in sorted(root.glob("*.lean")):
        name = source.relative_to(root).as_posix().encode()
        data = source.read_bytes()
        digest.update(len(name).to_bytes(8, "big"))
        digest.update(name)
        digest.update(len(data).to_bytes(8, "big"))
        digest.update(data)
    print(digest.hexdigest())


if __name__ == "__main__":
    main()
