#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# One-command cold reproduction (NEXTSTEPS §P2): pinned-toolchain build,
# audit gate, emission, RTL hygiene, lockstep corroboration, SAT
# crosscheck. From a clean clone on a fresh machine:
#
#   ./scripts/reproduce.sh
#
# Expected wall time: dominated by the cold `lake build` (Mathlib deps are
# fetched from Reservoir's cache by `lake`); the lockstep runs need
# iverilog, and the LRAT crosscheck needs cadical + python3 (both
# self-SKIP when absent).
#
# Pinned tool versions (what this repo is developed and CI'd against):
#   Lean      leanprover/lean4:v4.28.0   (lean-toolchain; fetched by elan)
#   iverilog  12.0 (stable)
#   yosys     0.33
#   cadical   1.7.3   (invoked with --no-binary --lrat)
set -euo pipefail
cd "$(dirname "$0")/.."

echo "reproduce: toolchain $(cat lean-toolchain)"
command -v lake >/dev/null || {
  echo "reproduce: lake not found — install elan (https://leanprover.github.io)"
  exit 1
}

# Full build + audit + certificate checks + emission + RTL hygiene.
scripts/ci.sh

# Lockstep corroboration against the emitted RTL (needs iverilog; each
# script validates its own prerequisites).
if command -v iverilog >/dev/null; then
  scripts/lockstep_acc8.sh
  scripts/lockstep_lnp64u.sh
else
  echo "reproduce: SKIP lockstep (iverilog not installed)"
fi

echo "reproduce: OK"
