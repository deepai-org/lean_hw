#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Measure fail-closed import acceptance over one identified elaborated design.

This is a coverage report, not a proof or a substitute for per-module emitted
RTL equivalence. It deliberately runs the same ModuleTranslator used by the
single-module adapter, while loading the large elaborated JSON only once.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
from collections import Counter

from yosys_to_loom_ir import ModuleTranslator


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def render_markdown(report: dict) -> str:
    summary = report["summary"]
    blockers = report["blocker_module_counts"]
    lines = [
        "# Neutral import coverage",
        "",
        "This report executes the fail-closed Yosys-to-neutral-IR translator over",
        "every module in one exact elaborated artifact. Acceptance means neutral IR",
        "translation only; it does not imply emitted RTL equivalence or signoff.",
        "",
        f"- Modules: {summary['module_count']}",
        f"- Accepted neutral imports: {summary['accepted_modules']}",
        f"- Blocked neutral imports: {summary['blocked_modules']}",
        f"- Elaborated JSON SHA-256: `{report['elaborated_sha256']}`",
        "",
        "## Blocker classes",
        "",
    ]
    lines += [f"- `{kind}`: {count} module(s)" for kind, count in blockers.items()]
    sites = report.get("four_state_sites", [])
    if sites:
        lines += ["", "## Unclassified four-state sites", "",
                  "These stable identifiers are the exact units selected by an explicit refinement policy.",
                  "", "| Module | Site | Pattern | Source |", "|---|---|---|---|"]
        for site in sites:
            source = site["source"]
            lines.append(
                f"| `{site['module']}` | `{site['site']}` | `{site['pattern']}` | "
                f"`{source['file']}:{source['start_line']}` |")
    lines += ["", "## Per-module status", "", "| Module | Status | Blocker classes |",
              "|---|---|---|"]
    for module in report["modules"]:
        kinds = ", ".join(f"`{kind}`" for kind in module["blocker_kinds"]) or "—"
        lines.append(f"| `{module['name']}` | {module['status']} | {kinds} |")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--yosys-json", type=pathlib.Path, required=True)
    parser.add_argument("--inventory", type=pathlib.Path, required=True)
    parser.add_argument("--json-out", type=pathlib.Path, required=True)
    parser.add_argument("--markdown-out", type=pathlib.Path, required=True)
    args = parser.parse_args()

    yosys_bytes = args.yosys_json.read_bytes()
    inventory = json.loads(args.inventory.read_bytes())
    actual = sha256(yosys_bytes)
    expected = inventory.get("frontend", {}).get("elaborated_sha256")
    if actual != expected:
        raise SystemExit(
            f"elaborated JSON identity mismatch: inventory={expected} actual={actual}")
    modules = json.loads(yosys_bytes).get("modules", {})
    records = []
    blocker_modules: Counter[str] = Counter()
    for name, module in sorted(modules.items()):
        translated = ModuleTranslator(name, module, modules).translate()
        kinds = sorted({item["kind"] for item in translated["unsupported"]})
        blocker_modules.update(kinds)
        records.append({
            "name": name,
            "status": "ACCEPTED" if not kinds else "BLOCKED",
            "blocker_kinds": kinds,
            "blockers": translated["unsupported"],
        })
    accepted = sum(record["status"] == "ACCEPTED" for record in records)
    four_state_sites = []
    for record in records:
        for blocker in record["blockers"]:
            metadata = blocker.get("metadata", {})
            if blocker["kind"].startswith("four_state_") and "site" in metadata:
                four_state_sites.append({
                    "module": record["name"], "source": blocker["source"], **metadata,
                })
    report = {
        "schema": 1,
        "elaborated_sha256": actual,
        "inventory_sha256": sha256(args.inventory.read_bytes()),
        "summary": {
            "module_count": len(records),
            "accepted_modules": accepted,
            "blocked_modules": len(records) - accepted,
        },
        "blocker_module_counts": dict(sorted(blocker_modules.items())),
        "four_state_sites": four_state_sites,
        "modules": records,
    }
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.markdown_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    args.markdown_out.write_text(render_markdown(report))
    print(f"IMPORT_COVERAGE_PASS accepted={accepted} blocked={len(records)-accepted} "
          f"elaborated_sha256={actual}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
