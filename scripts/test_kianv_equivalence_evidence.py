#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Fail-open/closed tests for deterministic KianV closure evidence."""

from __future__ import annotations

import json
import pathlib
import subprocess
import tempfile


ROOT = pathlib.Path(__file__).resolve().parent.parent
RESULTS = [{
    "module": f"logic_{index}", "status": "PASS", "proof_mode": "compositional",
    "proof_strategy": "equiv_simple_induct", "state_pairs": 0,
    "child_instances": 0, "child_ports": 0,
} for index in range(73)]
RESULTS.append({
    "module": "gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper",
    "status": "CONTRACT", "state_pairs": 0, "child_instances": 0,
    "child_ports": 0, "contract": "Evidence.KianV.Gf180Sram.specification",
    "contract_sha256": "4" * 64,
})
REPORT = {
    "schema": 1, "status": "PASS",
    "elaborated_sha256": "1" * 64, "package_sha256": "2" * 64,
    "emitted_sha256": "3" * 64, "external_contract_sha256": "4" * 64,
    "selected_modules": [result["module"] for result in RESULTS],
    "results": RESULTS,
}

with tempfile.TemporaryDirectory() as temporary:
    directory = pathlib.Path(temporary)
    report = directory / "report.json"
    json_out = directory / "evidence.json"
    markdown_out = directory / "evidence.md"
    report.write_text(json.dumps(REPORT), encoding="utf-8")
    command = ["python3", str(ROOT / "scripts/kianv_equivalence_evidence.py"),
               "--report", str(report), "--json-out", str(json_out),
               "--markdown-out", str(markdown_out)]
    subprocess.run(command, check=True, stdout=subprocess.DEVNULL)
    evidence = json.loads(json_out.read_text(encoding="utf-8"))
    assert evidence["status"] == "PASS"
    assert evidence["module_count"] == 74
    assert evidence["proved_modules"] == 73
    assert evidence["external_contracts"] == 1

    rejected = dict(REPORT)
    rejected["status"] = "FAIL"
    report.write_text(json.dumps(rejected), encoding="utf-8")
    failure = subprocess.run(command, stdout=subprocess.DEVNULL,
                             stderr=subprocess.DEVNULL)
    assert failure.returncode != 0

print("kianv equivalence evidence: PASS")
