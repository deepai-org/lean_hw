#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Separate irreducible kernel-checking cost from per-process overhead.

The release build compiles thousands of generated modules, each in its own
`lean` process. Every one of those processes pays a fixed toll -- start Lean,
deserialize its imports -- before checking anything. That toll is an artifact
of using the module system as the parallelism substrate, and it disappears if
obligations are batched into fewer, larger modules.

This script estimates `W`: total CPU-seconds of actual kernel checking, with
the toll removed. `W` is the quantity that no restructuring can reduce, so it
decides whether a wall-clock target is reachable at all:

    W <= budget          -> the target is an engineering problem
    W >  budget          -> the target exceeds the trust posture itself

Method. For each family of generated modules, compile a probe module that has
the family's exact import block and no declarations. Its CPU time is the toll
for that family. Then

    W_family = observed_family_cpu - module_count * toll_family

Observed family CPU comes from the phase CSV written by phase_timing.sh, so
this reads real build data rather than re-running the build.

Usage:
    scripts/measure_check_cost.py .lake/release-metrics/<run>/phases.csv
"""

from __future__ import annotations

import argparse
import csv
import os
import re
import resource
import subprocess
import sys
import time
from pathlib import Path


# Phase label -> (generated-module glob). Only phases that compile a single
# family of generated modules appear here; phases that run generators or
# compile one-off roots are handled separately as `singleton` entries.
FAMILY_PHASES: dict[str, str] = {
    "wire batches": "Batch*.lean",
    "tree chunk batches": "TreeChunkBatch*.lean",
    "memory data": "MemData*.lean",
    "memory renders": "MemRender*.lean",
    "memory roots": "MemRoot*.lean",
    "framing registers": "FramingReg*.lean",
    "framing outputs": "FramingOut*.lean",
    "fast indexed wire blocks": "FastIndexedBatch*.lean",
    "fast lookup evidence": "FastLookupEvidenceBatch*.lean",
    "shared join data": "ActionJoinBatch*.lean",
    "action leaves and join checks": "DagCut???Leaf*.lean",
    "action cut metadata": "DagCut???Nodes*.lean",
    "action cut roots": "DagCut???.lean",
    "fast indexed bridge batches": "FastIndexedBridgeBatch*.lean",
    "hybrid registers": "HybridReg*.lean",
    "semantic wire batches": "SemanticWireBatch*.lean",
    "semantic register batches": "SemanticRegBatch*.lean",
    "read register batches": "ReadRegBatch*.lean",
    "declared memory batches": "DeclMemBatch*.lean",
}

# Phases that compile exactly one module. Their toll is one process, so their
# checking cost is (cpu - toll) with a module count of 1.
SINGLETON_PHASES: dict[str, str] = {
    "shared action certificate": "ActionCert.lean",
    "render root": "Root.lean",
    "indexed root": "IndexedRoot.lean",
    "fast indexed wire root": "FastIndexedRoot.lean",
    "fast lookup root": "FastLookupEvidenceRoot.lean",
    "fast indexed bridge": "FastIndexedBridge.lean",
    "hybrid root": "HybridRoot.lean",
    "hybrid prelude": "HybridPrelude.lean",
    "semantic wires": "SemanticWires.lean",
    "semantic registers": "SemanticRegs.lean",
    "read registers": "ReadRegs.lean",
    "declared memories": "DeclMems.lean",
    "semantic actions": "SemanticActions.lean",
    "semantic reads": "SemanticReads.lean",
    "semantic memories": "SemanticMems.lean",
    "semantic module": "SemanticModule.lean",
    "semantic release (imports R-MC)": "SemanticRelease.lean",
}

IMPORT = re.compile(r"^import\s+\S+")


def child_cpu() -> float:
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    return usage.ru_utime + usage.ru_stime


def probe_toll(repo: Path, source: Path, probe_dir: Path,
               cache: dict[str, float]) -> float:
    """CPU seconds for an empty module with `source`'s import block."""
    imports = [line for line in source.read_text().splitlines()
               if IMPORT.match(line)]
    key = "\n".join(imports)
    if key in cache:
        return cache[key]
    probe_dir.mkdir(parents=True, exist_ok=True)
    probe = probe_dir / f"Probe{len(cache):04d}.lean"
    probe.write_text(key + "\n")
    before = child_cpu()
    started = time.monotonic()
    result = subprocess.run(
        ["lake", "env", "lean", "-j", "1", str(probe.resolve()),
         "-o", str(probe.with_suffix(".olean"))],
        cwd=repo, capture_output=True, text=True)
    wall = time.monotonic() - started
    toll = child_cpu() - before
    if result.returncode != 0:
        print(f"  probe failed for {source.name}: {result.stderr.strip()[:200]}",
              file=sys.stderr)
        return 0.0
    print(f"  toll {source.name:<34} {toll:6.2f}s cpu  ({wall:5.2f}s wall, "
          f"{len(imports)} imports)")
    cache[key] = toll
    return toll


def read_phase_cpu(csv_path: Path) -> dict[str, float]:
    """Sum CPU seconds per phase label (a label may repeat across scopes)."""
    totals: dict[str, float] = {}
    with csv_path.open() as handle:
        for row in csv.DictReader(handle):
            if not row.get("label"):
                continue
            try:
                cpu = float(row["cpu_seconds"])
            except (TypeError, ValueError):
                continue
            totals[row["label"]] = totals.get(row["label"], 0.0) + cpu
    return totals


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("phases", type=Path, help="phases.csv from a run")
    parser.add_argument("--generated", type=Path,
                        default=Path("GeneratedRelease/Lnp64u"))
    parser.add_argument("--budget", type=float, default=19200.0,
                        help="CPU-second budget (default 10 min x 32 cores)")
    args = parser.parse_args()

    repo = Path.cwd()
    generated: Path = args.generated
    if not generated.is_dir():
        raise SystemExit(f"missing generated tree {generated}")
    phase_cpu = read_phase_cpu(args.phases)
    probe_dir = repo / "scratch" / "cost-probes"
    cache: dict[str, float] = {}

    print("Probing per-family import toll (empty modules, real import sets):")
    rows: list[tuple[str, int, float, float, float]] = []
    for label, pattern in sorted(FAMILY_PHASES.items()):
        observed = phase_cpu.get(label)
        if observed is None:
            continue
        members = sorted(generated.glob(pattern))
        if not members:
            continue
        toll = probe_toll(repo, members[0], probe_dir, cache)
        rows.append((label, len(members), toll, observed,
                     observed - len(members) * toll))
    for label, name in sorted(SINGLETON_PHASES.items()):
        observed = phase_cpu.get(label)
        source = generated / name
        if observed is None or not source.exists():
            continue
        toll = probe_toll(repo, source, probe_dir, cache)
        rows.append((label, 1, toll, observed, observed - toll))

    print()
    header = (f"{'phase':<44}{'mods':>6}{'toll/mod':>10}"
              f"{'observed':>11}{'checking':>11}")
    print(header)
    print("-" * len(header))
    total_observed = total_toll = total_check = 0.0
    for label, count, toll, observed, check in sorted(
            rows, key=lambda r: -r[4]):
        print(f"{label:<44}{count:>6}{toll:>9.2f}s{observed:>10.0f}s"
              f"{check:>10.0f}s")
        total_observed += observed
        total_toll += count * toll
        total_check += check

    print("-" * len(header))
    print(f"{'TOTAL':<44}{'':>6}{'':>10}{total_observed:>10.0f}s"
          f"{total_check:>10.0f}s")
    print()
    print(f"observed CPU across measured phases : {total_observed:9.0f} s")
    print(f"per-process toll (removable)        : {total_toll:9.0f} s"
          f"  ({100 * total_toll / total_observed:.0f}%)")
    print(f"W, irreducible kernel checking      : {total_check:9.0f} s")
    print(f"budget                              : {args.budget:9.0f} s")
    print()
    if total_check <= 0.75 * args.budget:
        print("VERDICT: W is comfortably under budget. The wall-clock target is")
        print("an engineering problem -- batching and join restructuring.")
    elif total_check <= args.budget:
        print("VERDICT: W fits the budget but with little headroom. Restructuring")
        print("must be near-optimal; consider renegotiating the target too.")
    else:
        print("VERDICT: W EXCEEDS the budget. No batching or scheduling change")
        print("can reach the target -- the trust posture itself costs more than")
        print("the budget allows. Renegotiate the budget or the posture.")
    print()
    print("Caveats: phases that both generate and compile attribute generation")
    print("time to checking; families sharing one phase are attributed together;")
    print("the probe measures a cold-ish process against a warm page cache, so")
    print("the toll is a lower bound and W is correspondingly an upper bound.")


if __name__ == "__main__":
    main()
