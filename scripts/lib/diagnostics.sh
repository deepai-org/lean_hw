#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Generic command, freshness, and structured-result diagnostics.

loom_result() {
  local owner=$1 verdict=$2
  shift 2
  printf '%s: RESULT %s' "$owner" "$verdict"
  if (($#)); then printf ' — %s' "$*"; fi
  printf '\n'
}

# loom_run_step OWNER LABEL COMMAND...
# Preserve the producer's status while making even an empty failure actionable.
loom_run_step() {
  local owner=$1 label=$2
  shift 2
  local log status
  log=$(mktemp)
  if "$@" >"$log" 2>&1; then
    rm -f "$log"
    return 0
  else
    status=$?
  fi
  loom_result "$owner" FAIL "$label" >&2
  printf '%s: command:' "$owner" >&2
  printf ' %q' "$@" >&2
  printf '\n' >&2
  if [[ -s "$log" ]]; then
    sed 's/^/  | /' "$log" >&2
  else
    printf '  | (producer wrote no diagnostic output)\n' >&2
  fi
  rm -f "$log"
  return "$status"
}

# loom_require_fresh OUTPUT INPUT...
loom_require_fresh() {
  local out=$1
  shift
  if [[ ! -s "$out" ]]; then
    printf 'artifact freshness: missing or empty output: %s\n' "$out" >&2
    return 1
  fi
  local input
  for input in "$@"; do
    if [[ "$input" -nt "$out" ]]; then
      printf 'artifact freshness: stale output %s (newer input: %s)\n' \
        "$out" "$input" >&2
      return 1
    fi
  done
}
