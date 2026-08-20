#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Fail-closed external sequential-RTL equivalence adapter.

The adapter does not turn Yosys into a Loom theorem.  It produces PASS, FAIL,
or SKIP evidence bound to every input/output byte, the exact invocation,
tool version, and named assumptions.  Its process exit is successful only for
PASS, so required checks cannot silently accept SKIP.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import shutil
import subprocess
import tempfile
from typing import Any


def digest(path: pathlib.Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def artifact(role: str, path: pathlib.Path) -> dict[str, Any]:
    return {"role": role, "path": path.resolve().as_posix(),
            "sha256": digest(path)}


def safe_paths(paths: list[pathlib.Path], parser: argparse.ArgumentParser) -> None:
    missing = [str(path) for path in paths if not path.is_file()]
    if missing:
        parser.error("missing RTL file(s): " + ", ".join(missing))
    if any(any(character.isspace() for character in str(path.resolve()))
           for path in paths):
        parser.error("RTL paths containing whitespace are unsupported")


def write_report(args: argparse.Namespace, status: str, detail: str,
                 version: str, invocation: list[str], run_id: str,
                 log_artifact: dict[str, Any], inputs: list[dict[str, Any]]) -> None:
    report = {
        "schema": 1,
        "module": args.module_label,
        "stage": "original_to_loom_rtl",
        "status": status,
        "detail": detail,
        "run": {
            "adapter": "scripts/rtl_equivalence.py",
            "tool": "yosys",
            "version": version,
            "run_id": run_id,
            "invocation": invocation,
        },
        "artifacts": inputs + [log_artifact],
        "assumptions": [
            {"name": f"assumption_{index + 1}", "statement": statement}
            for index, statement in enumerate(args.assumption)
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--module-label", required=True)
    parser.add_argument("--gold-top", required=True)
    parser.add_argument("--revised-top", required=True)
    parser.add_argument("--gold-file", action="append", type=pathlib.Path, required=True)
    parser.add_argument("--revised-file", action="append", type=pathlib.Path, required=True)
    parser.add_argument("--include", action="append", type=pathlib.Path, default=[])
    parser.add_argument("--define", action="append", default=[])
    parser.add_argument("--assumption", action="append", default=[])
    parser.add_argument("--seq", type=int, default=12)
    parser.add_argument("--yosys", default="yosys")
    parser.add_argument("--log", type=pathlib.Path, required=True)
    parser.add_argument("--output", type=pathlib.Path, required=True)
    args = parser.parse_args()

    if args.seq <= 0:
        parser.error("--seq must be positive")
    files = [path.resolve() for path in args.gold_file + args.revised_file]
    safe_paths(files, parser)
    for include in args.include:
        if any(character.isspace() for character in str(include.resolve())):
            parser.error("include paths containing whitespace are unsupported")

    inputs = ([artifact(f"original_rtl_{index}", path)
               for index, path in enumerate(args.gold_file)] +
              [artifact(f"loom_emitted_rtl_{index}", path)
               for index, path in enumerate(args.revised_file)])
    invocation = [
        args.yosys, "-Q", "<generated-script>",
        "--gold-top", args.gold_top, "--revised-top", args.revised_top,
        "--seq", str(args.seq),
    ]
    identity = hashlib.sha256(json.dumps({
        "module": args.module_label,
        "inputs": inputs,
        "defines": args.define,
        "includes": [path.resolve().as_posix() for path in args.include],
        "seq": args.seq,
    }, sort_keys=True).encode()).hexdigest()

    args.log.parent.mkdir(parents=True, exist_ok=True)
    executable = shutil.which(args.yosys)
    if executable is None:
        args.log.write_text(f"SKIP: equivalence tool not found: {args.yosys}\n")
        write_report(args, "SKIP", "equivalence tool unavailable", "unavailable",
                     invocation, identity, artifact("equivalence_log", args.log), inputs)
        print(f"RTL_EQUIVALENCE_SKIP module={args.module_label}")
        return 2

    version_run = subprocess.run([executable, "-V"], text=True,
                                 capture_output=True, check=False)
    version = version_run.stdout.strip() if version_run.returncode == 0 else "version-query-failed"
    options = ["-sv"]
    options += [f"-I{path.resolve()}" for path in args.include]
    options += [f"-D{define}" for define in args.define]
    gold_files = " ".join(path.resolve().as_posix() for path in args.gold_file)
    revised_files = " ".join(path.resolve().as_posix() for path in args.revised_file)

    with tempfile.TemporaryDirectory(prefix="loom-rtl-equivalence-") as temp:
        script_path = pathlib.Path(temp) / "equivalence.ys"
        script = "\n".join([
            f"read_verilog {' '.join(options)} {gold_files}",
            f"hierarchy -check -top {args.gold_top}",
            "proc", "memory", "opt_clean",
            f"rename {args.gold_top} loom_equiv_gold",
            "design -stash loom_gold_design",
            f"read_verilog {' '.join(options)} {revised_files}",
            f"hierarchy -check -top {args.revised_top}",
            "proc", "memory", "opt_clean",
            f"rename {args.revised_top} loom_equiv_revised",
            "design -stash loom_revised_design",
            "design -copy-from loom_gold_design -as loom_equiv_gold loom_equiv_gold",
            "design -copy-from loom_revised_design -as loom_equiv_revised loom_equiv_revised",
            "equiv_make loom_equiv_gold loom_equiv_revised loom_equiv_miter",
            "hierarchy -top loom_equiv_miter",
            f"equiv_simple -seq {args.seq}",
            f"equiv_induct -seq {args.seq}",
            "equiv_status -assert",
            "",
        ])
        script_path.write_text(script)
        invocation[2] = script
        run = subprocess.run([executable, "-Q", "-s", str(script_path)],
                             text=True, capture_output=True, check=False)
        args.log.write_text(run.stdout + run.stderr)

    status = "PASS" if run.returncode == 0 else "FAIL"
    detail = ("Yosys proved every generated equivalence cell" if status == "PASS"
              else "Yosys failed or left at least one equivalence cell unproved")
    write_report(args, status, detail, version, invocation, identity,
                 artifact("equivalence_log", args.log), inputs)
    print(f"RTL_EQUIVALENCE_{status} module={args.module_label} run_id={identity}")
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
