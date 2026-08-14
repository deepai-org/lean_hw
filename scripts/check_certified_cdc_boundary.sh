#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Mechanical trust-boundary gate for the generic/certified multiclock path.
set -euo pipefail
cd "$(dirname "$0")/.."

bad=0

if rg -n '^import (Evidence|Machines|Tools)(\.|$)' Loom --glob '*.lean'; then
  echo "cdc-boundary: FAIL generic Loom imports a higher/evidence layer" >&2
  bad=1
fi

release_roots=(
  Tools/VerifiedRelease.lean
  Machines/Substrate/TwoClock.lean
  Machines/Lnp64mini/Multiclock.lean
)
if rg -n '^import Evidence(\.|$)' "${release_roots[@]}"; then
  echo "cdc-boundary: FAIL a certified System/release root imports Evidence" >&2
  bad=1
fi

# These are signatures of the former handwritten FIFO/mailbox renderers.
# Structural wrapper rendering and the proved MicroVerilog printer are
# allowed; behavioral CDC blocks embedded as strings in generic Loom are not.
if rg -n 'module loom_(async_fifo|toggle|sync_fifo)|rgray_sync[12]|wgray_sync[12]|always @\(posedge (src_clk|dst_clk)' \
    Loom --glob '*.lean'; then
  echo "cdc-boundary: FAIL handwritten behavioral CDC RTL is in generic Loom" >&2
  bad=1
fi

# The certified wrapper is allowed to instantiate and connect proved modules,
# but it may not acquire behavioral RTL over time. Keep this deliberately
# lexical and fail closed: new structural spellings must be reviewed here.
certified_renderer=Loom/Hw/CertifiedSystemArtifact.lean
if rg -n '"[^"\n]*(always(_ff|_comb)?|posedge|negedge|\breg\b|case[[:space:]]*\(|<=[[:space:]])' \
    "$certified_renderer"; then
  echo "cdc-boundary: FAIL certified System renderer contains behavioral RTL" >&2
  bad=1
fi

if unexpected_assigns=$(rg -n '"assign ' "$certified_renderer" | \
    rg -v 'assign dst_valid = sink_valid;|assign dst_payload = read_sample;' || true); \
    [[ -n "$unexpected_assigns" ]]; then
  echo "$unexpected_assigns"
  echo "cdc-boundary: FAIL unreviewed assignment in certified structural renderer" >&2
  bad=1
fi

if ((bad != 0)); then
  exit 1
fi

echo "cdc-boundary: PASS (generic Loom has no higher-layer import or handwritten CDC RTL)"
