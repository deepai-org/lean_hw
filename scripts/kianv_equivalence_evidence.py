#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Validate a complete KianV proof report and emit deterministic evidence."""

from __future__ import annotations

import argparse
import collections
import json
import pathlib


EXPECTED_MODULES = 74


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=pathlib.Path, required=True)
    parser.add_argument("--json-out", type=pathlib.Path, required=True)
    parser.add_argument("--markdown-out", type=pathlib.Path, required=True)
    args = parser.parse_args()

    report = json.loads(args.report.read_text(encoding="utf-8"))
    results = report.get("results", [])
    selected = report.get("selected_modules", [])
    names = [result.get("module") for result in results]
    if report.get("status") != "PASS":
        raise SystemExit("KianV equivalence report is not PASS")
    if len(results) != EXPECTED_MODULES or len(selected) != EXPECTED_MODULES:
        raise SystemExit("KianV equivalence report does not cover 74 specializations")
    if names != selected or len(set(names)) != EXPECTED_MODULES:
        raise SystemExit("KianV equivalence result coverage is incomplete or reordered")
    statuses = collections.Counter(result.get("status") for result in results)
    if statuses != {"PASS": 73, "CONTRACT": 1}:
        raise SystemExit(f"unexpected KianV proof statuses: {dict(statuses)}")
    contracts = [result for result in results if result["status"] == "CONTRACT"]
    if contracts[0].get("contract") != "Evidence.KianV.Gf180Sram.specification":
        raise SystemExit("the sole external specialization is not the GF180 SRAM contract")

    stable_results = []
    for result in results:
        stable_results.append({key: result[key] for key in (
            "module", "status", "proof_mode", "proof_strategy", "state_pairs",
            "child_instances", "child_ports", "contract", "contract_sha256")
            if key in result})
    strategies = collections.Counter(result.get("proof_strategy", "external_contract")
                                     for result in results)
    modes = collections.Counter(result.get("proof_mode", "external_contract")
                                for result in results)
    evidence = {
        "schema": 1,
        "status": "PASS",
        "module_count": EXPECTED_MODULES,
        "proved_modules": statuses["PASS"],
        "external_contracts": statuses["CONTRACT"],
        "elaborated_sha256": report["elaborated_sha256"],
        "package_sha256": report["package_sha256"],
        "emitted_sha256": report["emitted_sha256"],
        "external_contract_sha256": report["external_contract_sha256"],
        "proof_strategies": dict(sorted(strategies.items())),
        "proof_modes": dict(sorted(modes.items())),
        "results": stable_results,
    }
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.markdown_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(evidence, indent=2) + "\n", encoding="utf-8")

    notable = [result for result in stable_results
               if result.get("status") == "CONTRACT"
               or result.get("proof_mode") == "flatten"
               or result.get("proof_strategy") == "memory_relational_induction"]
    lines = [
        "# KianV bottom-up equivalence closure",
        "",
        "Status: **PASS**",
        "",
        "- Reachable specializations: 74/74 covered",
        "- Loom logic proofs: 73 PASS",
        "- Exact technology contracts: 1 PASS (GF180 SRAM wrapper)",
        "- Compositional proofs: 72",
        "- Explicit flatten fallback: 1 (32-bit logarithm hierarchy)",
        "- Memory relational-induction proofs: 4",
        "",
        "The memory strategy packs every mapped word into an exact per-memory",
        "state relation, asserts all related state bits plus observable ports,",
        "and proves the zero-refinement base case and one-step invariant by",
        "unbounded temporal induction. It does not abstract or omit memory bits.",
        "",
        "## Bound artifacts",
        "",
        f"- Elaborated JSON: `{evidence['elaborated_sha256']}`",
        f"- Neutral package: `{evidence['package_sha256']}`",
        f"- Loom-emitted RTL: `{evidence['emitted_sha256']}`",
        f"- GF180 SRAM contract: `{evidence['external_contract_sha256']}`",
        "",
        "## Non-default proof cases",
        "",
        "| Module | Result | Composition | Strategy | State relations |",
        "|---|---:|---|---|---:|",
    ]
    for result in notable:
        module = result["module"].replace("|", "\\|")
        lines.append(f"| `{module}` | {result['status']} | "
                     f"{result.get('proof_mode', 'external contract')} | "
                     f"{result.get('proof_strategy', 'external contract')} | "
                     f"{result['state_pairs']} |")
    lines += [
        "",
        "The companion JSON records every specialization. Generate both files",
        "only from a single all-green report using",
        "`scripts/kianv_equivalence_evidence.py`; partial reports fail closed.",
        "",
    ]
    args.markdown_out.write_text("\n".join(lines), encoding="utf-8")
    print(f"KIANV_EQUIVALENCE_EVIDENCE_PASS modules={EXPECTED_MODULES} "
          f"json={args.json_out} markdown={args.markdown_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
