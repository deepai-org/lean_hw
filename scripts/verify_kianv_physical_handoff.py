#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Fail-closed Yosys hierarchy check for the KianV GF180 physical handoff."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import subprocess
import tempfile


SRAM = "gf180mcu_fd_ip_sram__sram512x8m8wm1"


def digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def safe_yosys_path(path: pathlib.Path) -> str:
    value = str(path.resolve())
    if any(character.isspace() or character in ";'\"" for character in value):
        raise ValueError(f"path cannot be represented safely in a Yosys command: {value}")
    return value


def macro_paths(document: dict) -> list[str]:
    modules = document["modules"]
    found: list[str] = []

    def visit(module: str, path: list[str], ancestors: set[str]) -> None:
        if module in ancestors:
            raise ValueError(f"recursive emitted hierarchy at {module}")
        for name, cell in modules[module].get("cells", {}).items():
            next_path = path + [name]
            child = cell["type"]
            if child == SRAM:
                found.append(".".join(next_path))
            elif child in modules and not modules[child].get("attributes", {}).get("blackbox"):
                visit(child, next_path, ancestors | {module})

    visit("chip_top", [], set())
    return sorted(found)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rtl", type=pathlib.Path, required=True)
    parser.add_argument("--config", type=pathlib.Path, required=True)
    parser.add_argument("--manifest", type=pathlib.Path, required=True)
    parser.add_argument("--kianv-root", type=pathlib.Path, required=True)
    args = parser.parse_args()

    manifest = json.loads(args.manifest.read_text())
    if manifest.get("kind") != "kianv_loom_gf180_physical_handoff":
        raise ValueError("unexpected physical handoff manifest kind")
    expected_rtl = manifest["outputs"]["physical_rtl"]["sha256"]
    expected_config = manifest["outputs"]["librelane_config"]["sha256"]
    pdn_entry = manifest["outputs"]["pdn_config"]
    pdn = args.kianv_root / pdn_entry["path"]
    if digest(args.rtl) != expected_rtl or digest(args.config) != expected_config:
        raise ValueError("physical handoff output hash mismatch")
    if not pdn.is_file() or digest(pdn) != pdn_entry["sha256"]:
        raise ValueError("physical PDN config hash mismatch")
    helper_entry = manifest["inputs"]["physical_helpers"]
    helper = args.kianv_root / helper_entry["path"]
    if not helper.is_file() or digest(helper) != helper_entry["sha256"]:
        raise ValueError("physical helper hash mismatch")
    if manifest.get("sram_instances") != 21:
        raise ValueError("known-good KianV floorplan requires exactly 21 SRAM macros")
    if manifest.get("synthesis_options") != {"SYNTH_SHARE_RESOURCES": False}:
        raise ValueError("unexpected Loom synthesis options")
    if manifest.get("physical_options") != {
        "RUN_HEURISTIC_DIODE_INSERTION": True,
        "HEURISTIC_ANTENNA_THRESHOLD": 130,
        "GRT_MACRO_EXTENSION": 1,
    }:
        raise ValueError("unexpected Loom physical repair options")

    rtl_text = args.rtl.read_text()
    if "gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper__loom_body" in rtl_text:
        raise ValueError("behavioral Loom SRAM body survived physical handoff")
    if f"{SRAM} u_prim" not in rtl_text:
        raise ValueError("physical SRAM primitive instance is absent")
    config_text = args.config.read_text()
    if config_text.count("SYNTH_SHARE_RESOURCES: false") != 1:
        raise ValueError("Loom physical config must disable pathological resource sharing")
    for setting in (
        "RUN_HEURISTIC_DIODE_INSERTION: true",
        "HEURISTIC_ANTENNA_THRESHOLD: 130",
        "GRT_MACRO_EXTENSION: 1",
    ):
        if config_text.count(setting) != 1:
            raise ValueError(f"Loom physical config must contain {setting}")
    if "dir::../src/chip_core.sv" in config_text:
        raise ValueError("original chip_core remains in Loom physical source list")
    if config_text.count("dir::../src/chip_core.loom.v") != 1:
        raise ValueError("Loom physical source is not selected exactly once")
    if config_text.count("PDN_CFG: dir::pdn_cfg.loom.tcl") != 1:
        raise ValueError("translated Loom PDN config is not selected")
    expected_paths = sorted(manifest["sram_path_translation"].values())
    if sorted(path for path in expected_paths if path in pdn.read_text()) != expected_paths:
        raise ValueError("translated PDN config does not name every SRAM exactly once")

    chip_top = args.kianv_root / "src" / "chip_top.sv"
    helpers = helper
    include = args.kianv_root / "src"
    with tempfile.TemporaryDirectory(prefix="kianv-loom-physical-") as directory:
        hierarchy_json = pathlib.Path(directory) / "hierarchy.json"
        command = (
            f"read_verilog -sv -I {safe_yosys_path(include)} -DSLOT_1X1 "
            "-DGF180 -DUSE_POWER_PINS "
            f"{safe_yosys_path(args.rtl)} {safe_yosys_path(helpers)} "
            f"{safe_yosys_path(chip_top)}; "
            "hierarchy -top chip_top; proc; "
            f"write_json {safe_yosys_path(hierarchy_json)}"
        )
        result = subprocess.run(
            ["yosys", "-Q", "-p", command], text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        if result.returncode:
            raise RuntimeError("Yosys physical hierarchy failed:\n" + result.stdout[-8000:])
        hierarchy = json.loads(hierarchy_json.read_text())

    top_cell = hierarchy["modules"]["chip_top"]["cells"].get("i_chip_core")
    if top_cell is None or "NUM_BIDIR_PADS" not in top_cell["type"]:
        raise ValueError("chip_top did not specialize the compatible NUM_BIDIR_PADS interface")
    found = macro_paths(hierarchy)
    expected = sorted(manifest["sram_path_translation"].values())
    if found != expected:
        raise ValueError(
            "post-Yosys SRAM hierarchy differs from the translated floorplan; "
            f"missing={sorted(set(expected) - set(found))}, "
            f"extra={sorted(set(found) - set(expected))}"
        )
    print(
        "KIANV_PHYSICAL_HANDOFF_VERIFY_PASS "
        f"sram_instances={len(found)} rtl_sha256={digest(args.rtl)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
