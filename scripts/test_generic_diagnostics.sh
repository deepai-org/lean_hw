#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/lib/diagnostics.sh

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

set +e
output=$(loom_run_step sample "silent command" /bin/false 2>&1)
status=$?
set -e
[[ $status -ne 0 ]]
[[ "$output" == *"sample: RESULT FAIL — silent command"* ]]
[[ "$output" == *"sample: command: /bin/false"* ]]
[[ "$output" == *"producer wrote no diagnostic output"* ]]

printf 'old\n' >"$work/input"
printf 'built\n' >"$work/output"
loom_require_fresh "$work/output" "$work/input"
sleep 1
touch "$work/input"
if loom_require_fresh "$work/output" "$work/input" 2>/dev/null; then
  echo "generic diagnostics: stale output unexpectedly passed" >&2
  exit 1
fi

printf 'artifact bytes\n' >"$work/artifact.bin"
python3 scripts/artifact_identity.py write "$work/identity.json" "$work/artifact.bin" >/dev/null
python3 scripts/artifact_identity.py verify "$work/identity.json" >/dev/null
printf 'changed\n' >>"$work/artifact.bin"
set +e
identity_error=$(python3 scripts/artifact_identity.py verify "$work/identity.json" 2>&1)
identity_status=$?
set -e
[[ $identity_status -ne 0 ]]
[[ "$identity_error" == *"artifact identity mismatch: $work/artifact.bin"* ]]

loom_result generic_diagnostics PASS "command, freshness, and artifact-identity failures are named"
