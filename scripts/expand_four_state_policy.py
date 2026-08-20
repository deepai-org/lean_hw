#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Expand reviewed source-level decisions into exact site-bound policy rules."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
from typing import Any


CLASSIFICATIONS = {
    "synthesis_dont_care", "unreachable_decode", "undriven_behavior",
    "uninitialized_state_or_memory",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def matches(decision: dict[str, Any], site: dict[str, Any]) -> bool:
    source = site["source"]
    return (decision["module"] in ("*", site["module"])
            and decision["file"] in ("*", source["file"])
            and decision["line_start"] <= source["start_line"] <= decision["line_end"]
            and decision.get("pattern", site["pattern"]) == site["pattern"])


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--coverage", type=pathlib.Path, required=True)
    parser.add_argument("--decisions", type=pathlib.Path, required=True)
    parser.add_argument("--output", type=pathlib.Path, required=True)
    args = parser.parse_args()

    coverage_bytes = args.coverage.read_bytes()
    decision_bytes = args.decisions.read_bytes()
    coverage = json.loads(coverage_bytes)
    document = json.loads(decision_bytes)
    if document.get("schema") != 1 or not isinstance(document.get("decisions"), list):
        raise SystemExit("invalid four-state decision document")
    decisions = document["decisions"]
    names: set[str] = set()
    for decision in decisions:
        required = {"name", "module", "file", "line_start", "line_end",
                    "classification", "fill", "rationale"}
        if not isinstance(decision, dict) or not required.issubset(decision):
            raise SystemExit("incomplete four-state decision")
        if decision["name"] in names:
            raise SystemExit(f"duplicate decision name {decision['name']!r}")
        names.add(decision["name"])
        if decision["classification"] not in CLASSIFICATIONS:
            raise SystemExit(f"invalid classification in {decision['name']!r}")
        if decision["fill"] not in ("zero", "one") or not decision["rationale"]:
            raise SystemExit(f"invalid fill/rationale in {decision['name']!r}")

    used: set[str] = set()
    rules = []
    for site in coverage.get("four_state_sites", []):
        selected = [decision for decision in decisions if matches(decision, site)]
        if len(selected) != 1:
            raise SystemExit(
                f"site {site['site']} matched {len(selected)} decisions; expected exactly one")
        decision = selected[0]
        used.add(decision["name"])
        source = site["source"]
        rules.append({
            "name": f"{decision['name']}__{site['site']}",
            "site": site["site"],
            "module": site["module"],
            "file": source["file"],
            "line_start": source["start_line"],
            "line_end": source["start_line"],
            "classification": decision["classification"],
            "fill": decision["fill"],
            "rationale": decision["rationale"],
        })
    unused = sorted(names - used)
    if unused:
        raise SystemExit(f"unused four-state decisions: {', '.join(unused)}")
    if not rules:
        raise SystemExit("coverage contains no four-state sites")

    output = {
        "schema": 1,
        "coverage_sha256": sha256(coverage_bytes),
        "decisions_sha256": sha256(decision_bytes),
        "rules": rules,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    print(f"FOUR_STATE_POLICY_PASS sites={len(rules)} "
          f"coverage_sha256={output['coverage_sha256']} "
          f"decisions_sha256={output['decisions_sha256']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
