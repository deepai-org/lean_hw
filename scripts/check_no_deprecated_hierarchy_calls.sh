#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Typed hierarchy construction is the ordinary API. Keep the deprecated
# erased compatibility wrappers isolated to their declarations until they can
# be removed entirely.
set -euo pipefail
cd "$(dirname "$0")/.."

pattern='(^|[^[:alnum:]_])(ComponentGraph\.(empty|addInstance|connect|expose)|SystemBuilder\.(island|addIsland))([^[:alnum:]_]|$)'

if hits=$(git grep -nE "$pattern" -- '*.lean' \
    ':!Loom/Hw/Component.lean' \
    ':!Loom/Hw/System.lean' \
    ':!Loom/Hw/Multiclock.lean'); then
  echo "deprecated-hierarchy-api: ordinary callers must use typed hierarchy APIs:" >&2
  echo "$hits" >&2
  exit 1
fi

echo "deprecated-hierarchy-api: OK"
