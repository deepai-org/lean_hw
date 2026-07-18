#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Record the resource cost of kernel-checking release register leaves.

The monitor is observational only: it neither starts nor signals Lean.  It
uses Linux /proc start times and RSS samples, so a run produces reviewable
per-leaf timings without placing a profiler inside the trusted proof path.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import platform
import re
import subprocess
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


@dataclass
class ProcessSample:
    batch: int
    started: float
    peak_rss_kib: int = 0


def proc_start(pid: int, now: float) -> float:
    fields = Path(f"/proc/{pid}/stat").read_text().split()
    start_ticks = int(fields[21])
    uptime = float(Path("/proc/uptime").read_text().split()[0])
    return now - (uptime - start_ticks / os.sysconf("SC_CLK_TCK"))


def proc_rss(pid: int) -> int:
    for line in Path(f"/proc/{pid}/status").read_text().splitlines():
        if line.startswith("VmRSS:"):
            return int(line.split()[1])
    return 0


def lean_processes(artifact: str, now: float) -> dict[int, ProcessSample]:
    pattern = re.compile(
        rf"GeneratedRelease/{re.escape(artifact)}/SemanticRegBatch(\d+)\.lean"
    )
    result: dict[int, ProcessSample] = {}
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        pid = int(entry.name)
        try:
            command = (entry / "cmdline").read_bytes().replace(b"\0", b" ").decode()
            match = pattern.search(command)
            if match and ("/lean " in command or command.startswith("lean ")):
                result[pid] = ProcessSample(
                    int(match[1]), proc_start(pid, now), proc_rss(pid)
                )
        except (FileNotFoundError, ProcessLookupError, PermissionError, UnicodeError):
            continue
    return result


def accepted_count(root: Path) -> int:
    return sum(1 for _ in root.glob("SemanticRegBatch*.olean"))


def source_count(root: Path) -> int:
    return sum(1 for _ in root.glob("SemanticRegBatch*.lean"))


def system_used_memory() -> int:
    values: dict[str, int] = {}
    for line in Path("/proc/meminfo").read_text().splitlines():
        name, value, *_ = line.replace(":", "").split()
        if name in ("MemTotal", "MemAvailable"):
            values[name] = int(value)
    return values["MemTotal"] - values["MemAvailable"]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("artifact", choices=("Acc8", "Lnp64u"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--interval", type=float, default=2.0)
    parser.add_argument("--done-file", type=Path,
                        help="when set, monitor until this full-run marker exists")
    args = parser.parse_args()

    source_root = Path("GeneratedRelease") / args.artifact
    object_root = Path(".lake/build/lib/lean/GeneratedRelease") / args.artifact
    args.output.mkdir(parents=True, exist_ok=True)
    observations = args.output / "register-leaves.csv"
    started_at = time.time()
    metadata = {
        "artifact": args.artifact,
        "monitor_started_utc": datetime.fromtimestamp(
            started_at, timezone.utc).isoformat(),
        "machine": platform.platform(),
        "architecture": platform.machine(),
        "logical_cores": os.cpu_count(),
        "lean": subprocess.run(
            ["lean", "--version"], check=True, text=True,
            capture_output=True).stdout.strip(),
        "toolchain": Path("lean-toolchain").read_text().strip(),
        "accepted_at_monitor_start": accepted_count(object_root),
        "rss_sampling_interval_seconds": args.interval,
    }
    (args.output / "environment.json").write_text(
        json.dumps(metadata, indent=2, sort_keys=True) + "\n")

    with observations.open("w", newline="") as stream:
        writer = csv.DictWriter(
            stream, fieldnames=("batch", "duration_seconds", "peak_rss_kib"))
        writer.writeheader()

    active: dict[int, ProcessSample] = {}
    completed: list[dict[str, int | float]] = []
    peak_parallel = 0
    peak_aggregate_rss = 0
    peak_system_used_memory = 0
    saw_sources = False
    idle_after_complete = 0

    while True:
        now = time.time()
        current = lean_processes(args.artifact, now)
        for pid, sample in current.items():
            if pid not in active:
                active[pid] = sample
            active[pid].peak_rss_kib = max(
                active[pid].peak_rss_kib, sample.peak_rss_kib)

        for pid in list(active):
            if pid not in current:
                sample = active.pop(pid)
                row = {
                    "batch": sample.batch,
                    "duration_seconds": round(now - sample.started, 3),
                    "peak_rss_kib": sample.peak_rss_kib,
                }
                completed.append(row)
                # Persist each observation immediately: a failed or interrupted
                # proof run should retain the measurements collected so far.
                with observations.open("a", newline="") as stream:
                    csv.DictWriter(stream, fieldnames=(
                        "batch", "duration_seconds", "peak_rss_kib"
                    )).writerow(row)

        peak_parallel = max(peak_parallel, len(current))
        peak_aggregate_rss = max(
            peak_aggregate_rss,
            sum(sample.peak_rss_kib for sample in current.values()))
        peak_system_used_memory = max(
            peak_system_used_memory, system_used_memory())
        expected = source_count(source_root)
        accepted = accepted_count(object_root)
        saw_sources = saw_sources or expected > 0
        leaves_done = saw_sources and expected > 0 and accepted >= expected
        run_done = args.done_file is None or args.done_file.exists()
        if leaves_done and run_done and not current:
            idle_after_complete += 1
            if idle_after_complete >= 2:
                break
        else:
            idle_after_complete = 0
        time.sleep(args.interval)

    durations = sorted(float(row["duration_seconds"]) for row in completed)
    rss = [int(row["peak_rss_kib"]) for row in completed]

    def percentile(values: list[float], fraction: float) -> float | None:
        if not values:
            return None
        return values[round((len(values) - 1) * fraction)]

    summary = {
        "accepted_register_leaves": accepted_count(object_root),
        "expected_register_leaves": source_count(source_root),
        "monitor_wall_seconds": round(time.time() - started_at, 3),
        "observed_completed_processes": len(completed),
        "duration_seconds": {
            "min": percentile(durations, 0),
            "p10": percentile(durations, 0.1),
            "p25": percentile(durations, 0.25),
            "median": percentile(durations, 0.5),
            "p75": percentile(durations, 0.75),
            "p90": percentile(durations, 0.9),
            "max": percentile(durations, 1),
        },
        "observed_register_cpu_hours": round(sum(durations) / 3600, 3),
        "peak_leaf_rss_kib": max(rss, default=0),
        "peak_parallel_register_checks": peak_parallel,
        "peak_aggregate_register_rss_kib": peak_aggregate_rss,
        "peak_system_used_memory_kib": peak_system_used_memory,
        "completed_utc": datetime.now(timezone.utc).isoformat(),
    }
    (args.output / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
