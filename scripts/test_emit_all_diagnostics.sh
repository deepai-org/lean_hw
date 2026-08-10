#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Regression for the failure boundary in emit_all.sh. A silent fake `lake`
# must still produce an actionable command, label, and explicit empty-log note.
set -euo pipefail
cd "$(dirname "$0")/.."

fake_bin=$(mktemp -d)
trap 'rm -f "$fake_bin/lake"; rmdir "$fake_bin"' EXIT
ln -s /bin/false "$fake_bin/lake"

set +e
output=$(PATH="$fake_bin:$PATH" scripts/emit_all.sh 2>&1)
status=$?
set -e

if [[ $status -eq 0 ]]; then
  echo "emit_all diagnostics: FAIL — silent producer unexpectedly passed" >&2
  exit 1
fi

for expected in \
  "emit_all: RESULT FAIL — lake build" \
  "emit_all: command: lake build" \
  "producer wrote no diagnostic output"; do
  if [[ "$output" != *"$expected"* ]]; then
    echo "emit_all diagnostics: FAIL — missing: $expected" >&2
    printf '%s\n' "$output" >&2
    exit 1
  fi
done

echo "emit_all diagnostics: PASS"
