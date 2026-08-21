#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Fast structural tests for the KianV compositional proof generator."""

from __future__ import annotations

import importlib.util
import pathlib


ROOT = pathlib.Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "kianv_bottom_up_equivalence", ROOT / "scripts/kianv_bottom_up_equivalence.py")
assert SPEC is not None and SPEC.loader is not None
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)


def module(name: str, memories: list[dict]) -> dict:
    return {
        "name": name,
        "domains": [{"name": "clock", "clock_port": "clk",
                     "reset": {"port": None}}],
        "instances": [],
        "register_equivalence": [],
        "memory_equivalence": memories,
    }


memory_module = module("memory_top", [
    {"original": "ram_a", "word_memory": "loom_ram_a", "size": 2, "width": 8},
    {"original": "ram_b", "word_memory": "loom_ram_b", "size": 3, "width": 5},
])
memory_package = {"top": "memory_top", "modules": [memory_module]}
pairs = RUNNER.state_pairs(memory_package, memory_module)
assert len(pairs) == 5
assert RUNNER.memory_group_indexes(pairs) == [0, 1]

wire_commands: list[str] = []
RUNNER.add_memory_relation_wires(wire_commands, pairs, "gold")
wire_script = "\n".join(wire_commands)
assert wire_script.count("add -wire __loom_memory_gold_") == 2
assert "add -wire __loom_memory_gold_0 16" in wire_script
assert "__loom_memory_gold_0[7:0] \\ram_a[0]" in wire_script
assert "__loom_memory_gold_0[15:8] \\ram_a[1]" in wire_script
assert "add -wire __loom_memory_gold_1 15" in wire_script

memory_script = RUNNER.script_for(
    pathlib.Path("elaborated.json"), pathlib.Path("emitted.v"),
    memory_package, memory_module, {"cells": {}}, 12)
assert memory_script.count("equiv_add -try \\__loom_memory_gold_") == 2
assert "memory -nowiden" in memory_script
assert "equiv_miter -assert loom_equiv_assert" in memory_script
assert "sat -seq 1 -tempinduct -set-init-zero" in memory_script
assert "equiv_simple" not in memory_script

stateless_module = module("stateless_top", [])
stateless_package = {"top": "stateless_top", "modules": [stateless_module]}
stateless_script = RUNNER.script_for(
    pathlib.Path("elaborated.json"), pathlib.Path("emitted.v"),
    stateless_package, stateless_module, {"cells": {}}, 12)
assert "equiv_simple -seq 12" in stateless_script
assert "equiv_induct -seq 12" in stateless_script
assert "sat -seq 1 -tempinduct" not in stateless_script

print("kianv bottom-up runner: PASS")
