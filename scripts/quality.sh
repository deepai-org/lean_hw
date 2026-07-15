#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Fast, dependency-free repository hygiene checks. Semantic trust checks live
# in `lake exe audit`; this script catches packaging drift before a Lean build.
set -euo pipefail
cd "$(dirname "$0")/.."

fail=0

if [[ ! -f lean-toolchain ]] || rg -q '(nightly|:latest$)' lean-toolchain; then
  echo "quality: lean-toolchain must pin a stable release" >&2
  fail=1
fi

for required in lakefile.lean lake-manifest.json README.md LICENSE NOTICE; do
  if [[ ! -f "$required" ]]; then
    echo "quality: missing required package file: $required" >&2
    fail=1
  fi
done

while IFS= read -r file; do
  if ! rg -q 'SPDX-License-Identifier:' "$file"; then
    echo "quality: missing SPDX header: $file" >&2
    fail=1
  fi
done < <(git ls-files '*.lean')

if git grep -nI -E '[[:blank:]]+$' -- '*.lean' '*.md' '*.sh'; then
  echo "quality: trailing whitespace found" >&2
  fail=1
fi

junk_re='(^|/)(__pycache__/|[^/]*\.py[co]$|scratch[^/]*\.lean$|[^/]*(draft|wip)[^/]*\.txt$)'
if junk=$(git ls-files | rg "$junk_re"); then
  echo "quality: generated or scratch files are tracked:" >&2
  echo "$junk" >&2
  fail=1
fi

if (( fail != 0 )); then
  exit 1
fi

echo "quality: OK"
