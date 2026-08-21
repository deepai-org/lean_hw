#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Build a fail-closed KianV RTL/config handoff for the pinned GF180 flow.

The neutral Loom artifact intentionally contains an executable model for the
contracted foundry SRAM.  A physical implementation must instead retain the
foundry wrapper/primitive and must update the fixed-macro paths after hierarchy
specialization.  This tool performs only those technology-bound changes and
records every byte and hierarchy translation in a manifest.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re


IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_$]*")
MODULE = re.compile(
    r"(?ms)^module\s+(?P<name>[^\s(#]+).*?^endmodule\s*$\n?"
)
SRAM_WRAPPER = "gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper"
SRAM_PRIMITIVE = "gf180mcu_fd_ip_sram__sram512x8m8wm1"
ANTENNA_CELL = "gf180mcu_fd_sc_mcu9t5v0__antenna"
ANTENNA_INSTANCE = "u_d6_antenna"


def digest_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest(path: pathlib.Path) -> str:
    return digest_bytes(path.read_bytes())


def encoded_identifier(name: str) -> str:
    return "_loom_u" + "_".join(str(byte) for byte in name.encode())


def emitted_instance_name(name: str) -> str:
    if IDENTIFIER.fullmatch(name) and not name.startswith("u_loom_"):
        return name
    return "u" + encoded_identifier(name)


def emitted_module_name(name: str) -> str:
    if IDENTIFIER.fullmatch(name) and not name.endswith("__loom_body"):
        return name
    return encoded_identifier(name)


def module_blocks(text: str) -> dict[str, re.Match[str]]:
    blocks: dict[str, re.Match[str]] = {}
    for match in MODULE.finditer(text):
        name = match.group("name")
        if name in blocks:
            raise ValueError(f"duplicate module declaration {name!r}")
        blocks[name] = match
    return blocks


def replace_modules(text: str, replacements: dict[str, str]) -> str:
    blocks = module_blocks(text)
    missing = sorted(set(replacements) - set(blocks))
    if missing:
        raise ValueError(f"modules required for physical replacement are absent: {missing}")
    spans = sorted(
        ((blocks[name].start(), blocks[name].end(), replacement)
         for name, replacement in replacements.items()),
        reverse=True,
    )
    for start, end, replacement in spans:
        text = text[:start] + replacement.rstrip() + "\n\n" + text[end:]
    return text


def specialize_chip_core_interface(text: str) -> str:
    old = "module chip_core("
    new = "module chip_core #(\n  parameter NUM_BIDIR_PADS = 54\n)("
    if text.count(old) != 1:
        raise ValueError("expected exactly one specialized chip_core declaration")
    text = text.replace(old, new, 1)
    # The parameter is an integration compatibility parameter: this package
    # was proved only for the pinned 54-pad elaboration.  Refuse to imply that
    # a different value changes the already-specialized implementation.
    marker = "module chip_core #(\n  parameter NUM_BIDIR_PADS = 54\n)(\n" \
        "  input wire clk,\n  input wire rst_n,\n  input wire [53:0] bidir_in,"
    if text.count(marker) != 1:
        raise ValueError("chip_core no longer has the proved 54-pad interface")
    return text


def enumerate_sram_paths(package: dict) -> dict[str, str]:
    modules = {module["name"]: module for module in package["modules"]}
    top = package["top"]
    if top not in modules:
        raise ValueError(f"package top {top!r} is absent")
    paths: dict[str, str] = {}

    def visit(module_name: str, semantic: list[str], emitted: list[str]) -> None:
        module = modules[module_name]
        for instance in module.get("instances", []):
            child = instance["module_name"]
            source_name = instance["name"]
            next_semantic = semantic + [source_name]
            next_emitted = emitted + [emitted_instance_name(source_name)]
            if child == SRAM_WRAPPER:
                old = "i_chip_core." + ".".join(next_semantic) + ".u_prim"
                new = "i_chip_core." + ".".join(next_emitted) + ".u_prim"
                if old in paths:
                    raise ValueError(f"duplicate semantic SRAM path {old}")
                paths[old] = new
            elif child in modules:
                visit(child, next_semantic, next_emitted)

    visit(top, [], [])
    if not paths:
        raise ValueError("no contracted GF180 SRAM instances are reachable")
    return paths


def powered_modules(package: dict) -> set[str]:
    modules = {module["name"]: module for module in package["modules"]}
    memo: dict[str, bool] = {}

    def reaches_sram(name: str, ancestors: set[str]) -> bool:
        if name in memo:
            return memo[name]
        if name in ancestors:
            raise ValueError(f"recursive package hierarchy at {name}")
        result = False
        for instance in modules[name].get("instances", []):
            child = instance["module_name"]
            if child == SRAM_WRAPPER or (
                child in modules and reaches_sram(child, ancestors | {name})
            ):
                result = True
        memo[name] = result
        return result

    for name in modules:
        reaches_sram(name, set())
    return {name for name, powered in memo.items() if powered}


def add_power_ports(block: str, module_name: str) -> str:
    if "`ifdef USE_POWER_PINS" in block:
        raise ValueError(f"generated module {module_name} already has conditional power ports")
    prefix = f"module {module_name}"
    if not block.startswith(prefix):
        raise ValueError(f"module block mismatch for {module_name}")
    if block.startswith(prefix + " #("):
        marker = ")(\n"
        index = block.find(marker)
        if index < 0:
            raise ValueError(f"parameterized module {module_name} has no ANSI port list")
        index += len(marker)
    else:
        marker = "(\n"
        index = block.find(marker, len(prefix))
        if index < 0:
            raise ValueError(f"module {module_name} has no ANSI port list")
        index += len(marker)
    ports = (
        "`ifdef USE_POWER_PINS\n"
        "  inout wire VDD,\n"
        "  inout wire VSS,\n"
        "`endif\n"
    )
    return block[:index] + ports + block[index:]


def add_power_hierarchy(text: str, package: dict) -> tuple[str, list[str]]:
    modules = {module["name"]: module for module in package["modules"]}
    powered = powered_modules(package)
    replacements: dict[str, str] = {}
    blocks = module_blocks(text)
    for source_name in sorted(powered):
        emitted_name = emitted_module_name(source_name)
        if emitted_name not in blocks:
            raise ValueError(f"powered emitted module is absent: {emitted_name}")
        block = blocks[emitted_name].group(0)
        block = add_power_ports(block, emitted_name)
        for instance in modules[source_name].get("instances", []):
            child = instance["module_name"]
            if child != SRAM_WRAPPER and child not in powered:
                continue
            child_name = emitted_module_name(child)
            instance_name = emitted_instance_name(instance["name"])
            marker = f"  {child_name} {instance_name} (\n"
            if block.count(marker) != 1:
                raise ValueError(
                    f"expected one powered child instance {source_name}.{instance['name']}"
                )
            connections = (
                marker
                + "`ifdef USE_POWER_PINS\n"
                + "    .VDD(VDD),\n"
                + "    .VSS(VSS),\n"
                + "`endif\n"
            )
            block = block.replace(marker, connections, 1)
        replacements[emitted_name] = block
    return replace_modules(text, replacements), sorted(powered)


def physical_rtl(emitted: pathlib.Path, wrapper: pathlib.Path,
                 package: dict) -> tuple[str, list[str]]:
    neutral = emitted.read_text()
    wrapper_text = wrapper.read_text()
    wrapper_blocks = module_blocks(wrapper_text)
    if set(wrapper_blocks) != {SRAM_WRAPPER}:
        raise ValueError("foundry wrapper source must contain exactly its named module")
    foundry_module = wrapper_blocks[SRAM_WRAPPER].group(0)
    if f"{SRAM_PRIMITIVE} u_prim" not in foundry_module:
        raise ValueError("foundry wrapper no longer instantiates the expected u_prim")
    close_marker = "  );\n\n`else\n"
    if foundry_module.count(close_marker) != 1:
        raise ValueError("foundry wrapper primitive close marker changed")
    # The first routed Loom handoff exposed two foundry-deck Metal2 antenna
    # markers at x offsets 366.035--366.635 um inside the north-oriented
    # instruction-cache tile 3 SRAM.  The macro LEF identifies that exact
    # input buffer as D[6] (pin x=365.150--366.270 um).  OpenROAD cannot see
    # the macro-internal gate geometry, so retain one physical antenna diode
    # on D[6] per contracted SRAM wrapper.  This is a bounded 21-cell repair;
    # generic length-threshold insertion would add about 99,000 diodes.
    diode = (
        "  );\n\n"
        "  (* keep *)\n"
        f"  {ANTENNA_CELL} {ANTENNA_INSTANCE} (\n"
        "`ifdef USE_POWER_PINS\n"
        "      .I  (D[6]),\n"
        "      .VDD(VDD),\n"
        "      .VSS(VSS),\n"
        "      .VNW(VDD),\n"
        "      .VPW(VSS)\n"
        "`else\n"
        "      .I  (D[6])\n"
        "`endif\n"
        "  );\n\n`else\n"
    )
    foundry_module = foundry_module.replace(close_marker, diode, 1)
    neutral = replace_modules(neutral, {
        SRAM_WRAPPER: foundry_module,
        SRAM_WRAPPER + "__loom_body":
            "// Loom behavioral SRAM body removed: physical flow uses the contracted foundry macro.",
    })
    neutral = specialize_chip_core_interface(neutral)
    return add_power_hierarchy(neutral, package)


def physical_config(source: pathlib.Path, translations: dict[str, str]) -> str:
    text = source.read_text()
    if re.search(r"(?m)^SYNTH_SHARE_RESOURCES:", text):
        raise ValueError("source config unexpectedly sets SYNTH_SHARE_RESOURCES")
    for option in (
        "RUN_HEURISTIC_DIODE_INSERTION",
        "HEURISTIC_ANTENNA_THRESHOLD",
        "GRT_MACRO_EXTENSION",
    ):
        if re.search(rf"(?m)^{option}:", text):
            raise ValueError(f"source config unexpectedly sets {option}")
    strategy = 'SYNTH_STRATEGY: "AREA 3"\n'
    if text.count(strategy) != 1:
        raise ValueError("expected the pinned AREA 3 synthesis strategy")
    # Yosys resource sharing performs pairwise SAT searches. Loom's explicit
    # TLB memory reads make that optional pass pathological (multi-million
    # variable queries), while leaving it disabled preserves the proved RTL
    # semantics and lets the ordinary memory lowering/map passes run.
    text = text.replace(
        strategy,
        strategy + "SYNTH_SHARE_RESOURCES: false\n",
        1,
    )
    antenna_marker = "DRT_ANTENNA_MARGIN: 10 # %\n"
    if text.count(antenna_marker) != 1:
        raise ValueError("expected the pinned detailed-route antenna margin")
    # A one-GCell macro extension keeps detailed routes away from the fixed
    # SRAM boundaries, where the first route exposed one M3.2b spacing site.
    # The macro-internal D[6] antenna repair is an exact physical RTL cell;
    # do not enable LibreLane's broad length-threshold diode insertion.
    text = text.replace(
        antenna_marker,
        antenna_marker
        + "GRT_MACRO_EXTENSION: 1\n",
        1,
    )
    start = text.find("VERILOG_FILES:\n")
    if start < 0:
        raise ValueError("LibreLane config has no VERILOG_FILES block")
    body_start = start + len("VERILOG_FILES:\n")
    match = re.search(r"(?m)^[A-Z][A-Z0-9_]*:", text[body_start:])
    if match is None:
        raise ValueError("could not find the end of VERILOG_FILES")
    end = body_start + match.start()
    files = (
        "VERILOG_FILES:\n"
        "  - dir::../src/chip_core.loom.v\n"
        "  - dir::../src/loom_physical_helpers.v\n"
        "  - dir::../src/chip_top.sv\n\n"
    )
    text = text[:start] + files + text[end:]

    configured = set(re.findall(r'^\s+"([^"]+\.u_prim)":\s*$', text, re.MULTILINE))
    expected = set(translations)
    if configured != expected:
        missing = sorted(expected - configured)
        extra = sorted(configured - expected)
        raise ValueError(
            f"SRAM placement hierarchy mismatch before translation; missing={missing}, extra={extra}"
        )
    for old, new in sorted(translations.items()):
        needle = f'"{old}":'
        if text.count(needle) != 1:
            raise ValueError(f"expected one placement entry for {old}")
        text = text.replace(needle, f'"{new}":', 1)
    if text.count("PDN_CFG: dir::pdn_cfg.tcl") != 1:
        raise ValueError("expected the pinned PDN config reference")
    text = text.replace("PDN_CFG: dir::pdn_cfg.tcl", "PDN_CFG: dir::pdn_cfg.loom.tcl", 1)
    return text


def physical_pdn(source: pathlib.Path, translations: dict[str, str]) -> str:
    text = source.read_text()
    for old, new in sorted(translations.items()):
        if text.count(old) != 1:
            raise ValueError(f"expected one PDN macro entry for {old}")
        text = text.replace(old, new, 1)
    leftovers = [old for old in translations if old in text]
    if leftovers:
        raise ValueError(f"untranslated PDN macro paths remain: {leftovers}")
    return text


def write(path: pathlib.Path, data: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(data)


def display_path(path: pathlib.Path, root: pathlib.Path) -> str:
    try:
        return str(path.resolve().relative_to(root.resolve()))
    except ValueError:
        return str(path.resolve())


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--emitted", type=pathlib.Path, required=True)
    parser.add_argument("--package", type=pathlib.Path, required=True)
    parser.add_argument("--kianv-root", type=pathlib.Path, required=True)
    parser.add_argument("--output-rtl", type=pathlib.Path, required=True)
    parser.add_argument("--output-config", type=pathlib.Path, required=True)
    parser.add_argument("--output-pdn", type=pathlib.Path, required=True)
    parser.add_argument("--manifest", type=pathlib.Path, required=True)
    args = parser.parse_args()

    package_document = json.loads(args.package.read_text())
    package = package_document.get("package", package_document)
    translations = enumerate_sram_paths(package)
    wrapper = args.kianv_root / "src" / f"{SRAM_WRAPPER}.v"
    helpers = args.kianv_root / "src" / "loom_physical_helpers.v"
    source_config = args.kianv_root / "librelane" / "config.yaml"
    source_pdn = args.kianv_root / "librelane" / "pdn_cfg.tcl"
    if not helpers.is_file() or "module async_reset_sync" not in helpers.read_text():
        raise ValueError("chip-top Loom physical helper is absent or invalid")
    rtl, power_modules = physical_rtl(args.emitted, wrapper, package)
    config = physical_config(source_config, translations)
    pdn = physical_pdn(source_pdn, translations)
    write(args.output_rtl, rtl)
    write(args.output_config, config)
    write(args.output_pdn, pdn)

    manifest = {
        "schema": 1,
        "kind": "kianv_loom_gf180_physical_handoff",
        "inputs": {
            "neutral_rtl": {"path": display_path(args.emitted, args.kianv_root), "sha256": digest(args.emitted)},
            "package": {"path": display_path(args.package, args.kianv_root), "sha256": digest(args.package)},
            "foundry_wrapper": {"path": display_path(wrapper, args.kianv_root), "sha256": digest(wrapper)},
            "physical_helpers": {"path": display_path(helpers, args.kianv_root), "sha256": digest(helpers)},
            "librelane_config": {"path": display_path(source_config, args.kianv_root), "sha256": digest(source_config)},
            "pdn_config": {"path": display_path(source_pdn, args.kianv_root), "sha256": digest(source_pdn)},
        },
        "outputs": {
            "physical_rtl": {"path": display_path(args.output_rtl, args.kianv_root), "sha256": digest(args.output_rtl)},
            "librelane_config": {"path": display_path(args.output_config, args.kianv_root), "sha256": digest(args.output_config)},
            "pdn_config": {"path": display_path(args.output_pdn, args.kianv_root), "sha256": digest(args.output_pdn)},
        },
        "specialized_parameters": {"NUM_BIDIR_PADS": 54},
        "synthesis_options": {"SYNTH_SHARE_RESOURCES": False},
        "physical_options": {
            "GRT_MACRO_EXTENSION": 1,
        },
        "sram_input_antenna_diodes": {
            "cell": ANTENNA_CELL,
            "instance": ANTENNA_INSTANCE,
            "pin": "D[6]",
            "instances": len(translations),
        },
        "power_modules": power_modules,
        "sram_primitive": SRAM_PRIMITIVE,
        "sram_instances": len(translations),
        "sram_path_translation": translations,
    }
    write(args.manifest, json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(
        "KIANV_PHYSICAL_HANDOFF_PASS "
        f"sram_instances={len(translations)} rtl_sha256={digest(args.output_rtl)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
