#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Fail closed unless every KianV GF180 SRAM contract artifact is exact."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import subprocess


def git_head(path: pathlib.Path) -> str:
    return subprocess.run(
        ["git", "-C", str(path), "rev-parse", "HEAD"], check=True,
        text=True, capture_output=True).stdout.strip()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source_root", type=pathlib.Path)
    parser.add_argument("--manifest", type=pathlib.Path,
                        default=pathlib.Path("Evidence/KianV/gf180_sram_external.json"))
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    if manifest.get("schema") != 1 or not manifest.get("artifacts"):
        parser.error("invalid or empty SRAM external-component manifest")
    if git_head(args.source_root) != manifest["kianv_commit"]:
        parser.error("KianV checkout commit does not match SRAM contract")
    if git_head(args.source_root / "gf180mcu/gf180mcuD") != manifest["pdk_commit"]:
        parser.error("GF180 PDK checkout commit does not match SRAM contract")
    roles: set[str] = set()
    for artifact in manifest["artifacts"]:
        role = artifact["role"]
        if role in roles:
            parser.error(f"duplicate SRAM artifact role: {role}")
        roles.add(role)
        path = args.source_root / artifact["path"]
        data = path.read_bytes()
        if len(data) != artifact["bytes"]:
            parser.error(f"SRAM artifact size mismatch: {path}")
        if hashlib.sha256(data).hexdigest() != artifact["sha256"]:
            parser.error(f"SRAM artifact hash mismatch: {path}")
    required = {"wrapper", "gds", "lef", "blackbox"}
    if not required.issubset(roles) or len([r for r in roles if r.startswith("lib_")]) != 8:
        parser.error("SRAM manifest must bind wrapper/GDS/LEF/blackbox and eight Liberty corners")
    print(f"KIANV_GF180_SRAM_EXTERNAL_PASS artifacts={len(roles)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
