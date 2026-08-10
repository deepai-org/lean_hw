#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Create and verify byte identities for externally observed artifacts.

An identity is a deterministic JSON document containing each path, byte
length, and SHA-256 digest. It is operational provenance, not proof evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile


def identity(paths: list[Path]) -> dict[str, object]:
    entries: list[dict[str, object]] = []
    for path in sorted(paths, key=lambda p: p.as_posix()):
        data = path.read_bytes()
        entries.append(
            {
                "path": path.as_posix(),
                "bytes": len(data),
                "sha256": hashlib.sha256(data).hexdigest(),
            }
        )
    encoded = json.dumps(entries, sort_keys=True, separators=(",", ":")).encode()
    return {
        "schema": "loom-artifact-identity-v1",
        "set_sha256": hashlib.sha256(encoded).hexdigest(),
        "artifacts": entries,
    }


def render(value: dict[str, object]) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def write_atomic(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as output:
            output.write(text)
        os.replace(temporary, path)
    except BaseException:
        Path(temporary).unlink(missing_ok=True)
        raise


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    identify = sub.add_parser("identify")
    identify.add_argument("artifacts", nargs="+", type=Path)
    write = sub.add_parser("write")
    write.add_argument("manifest", type=Path)
    write.add_argument("artifacts", nargs="+", type=Path)
    verify = sub.add_parser("verify")
    verify.add_argument("manifest", type=Path)
    args = parser.parse_args()

    if args.command == "identify":
        value = identity(args.artifacts)
        print(
            "ARTIFACT IDENTITY"
            f" set_sha256={value['set_sha256']} count={len(value['artifacts'])}"
        )
    elif args.command == "write":
        write_atomic(args.manifest, render(identity(args.artifacts)))
        print(f"artifact identity written: {args.manifest}")
    else:
        expected = json.loads(args.manifest.read_text(encoding="utf-8"))
        paths = [Path(entry["path"]) for entry in expected.get("artifacts", [])]
        actual = identity(paths)
        if actual != expected:
            expected_by_path = {e["path"]: e for e in expected.get("artifacts", [])}
            actual_by_path = {e["path"]: e for e in actual["artifacts"]}
            changed = sorted(
                path
                for path in expected_by_path.keys() | actual_by_path.keys()
                if expected_by_path.get(path) != actual_by_path.get(path)
            )
            raise SystemExit(
                "artifact identity mismatch: " + (", ".join(changed) or "manifest")
            )
        print(
            "ARTIFACT IDENTITY PASS"
            f" set_sha256={actual['set_sha256']} count={len(paths)}"
        )


if __name__ == "__main__":
    main()
