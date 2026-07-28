# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Shared per-phase wall/CPU timing for the release build scripts.
#
# Source this file, then wrap each build stage in `run_phase LABEL cmd...`.
# When LOOM_PHASE_LOG names a file, every phase appends one CSV row:
#
#   started_utc,scope,label,wall_seconds,cpu_seconds,parallelism
#
# `cpu_seconds` is reaped-children CPU (user+sys) for the shell running the
# phase, so `parallelism = cpu/wall` states how much of the machine a phase
# actually used. A phase with parallelism near 1 on a 32-core host is serial
# and will not improve with more workers; that distinction is the point of
# recording CPU alongside wall clock.

_loom_clk_tck=$(getconf CLK_TCK 2>/dev/null || echo 100)
_loom_cpu_ticks=0

# Read cumulative reaped-children CPU ticks for THIS shell. Deliberately uses
# only builtins: a command substitution would fork, and the fork's children
# times are not the caller's.
_loom_read_cpu() {
  local stat
  if [[ -r /proc/self/stat ]]; then
    read -r -a stat < /proc/self/stat
    _loom_cpu_ticks=$(( stat[15] + stat[16] ))
  else
    _loom_cpu_ticks=0
  fi
}

run_phase() {
  local label=$1
  shift
  local started=$SECONDS
  local started_utc
  started_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  _loom_read_cpu
  local cpu_before=$_loom_cpu_ticks
  echo "==> $label"
  # `set -e` in the calling script aborts on failure *before* anything is
  # printed, so a phase killed by the OOM killer looks like a clean stop with
  # no message. Capture the status and say so.
  local status=0
  "$@" || status=$?
  if ((status != 0)); then
    echo "!!! phase FAILED: $label (exit $status after $((SECONDS - started))s)" >&2
    if ((status >= 128)); then
      echo "!!! exit >= 128 means a signal; $((status - 128)) is likely SIGKILL (9) from the OOM killer" >&2
    fi
    return $status
  fi
  local wall=$(( SECONDS - started ))
  _loom_read_cpu
  local cpu_ticks=$(( _loom_cpu_ticks - cpu_before ))
  local cpu par
  cpu=$(awk -v t="$cpu_ticks" -v h="$_loom_clk_tck" 'BEGIN { printf "%.2f", t / h }')
  par=$(awk -v c="$cpu" -v w="$wall" \
    'BEGIN { if (w > 0) printf "%.2f", c / w; else printf "" }')
  echo "<== $label: ${wall}s (cpu ${cpu}s, parallelism ${par:-n/a})"
  if [[ -n "${LOOM_PHASE_LOG:-}" ]]; then
    printf '%s,%s,%s,%s,%s,%s\n' "$started_utc" "${LOOM_PHASE_SCOPE:-release}" \
      "$label" "$wall" "$cpu" "$par" >> "$LOOM_PHASE_LOG"
  fi
  return $status
}

# Write the CSV header exactly once, when the log is first created.
loom_phase_log_init() {
  [[ -n "${LOOM_PHASE_LOG:-}" ]] || return 0
  mkdir -p "$(dirname "$LOOM_PHASE_LOG")"
  [[ -s "$LOOM_PHASE_LOG" ]] && return 0
  printf 'started_utc,scope,label,wall_seconds,cpu_seconds,parallelism\n' \
    > "$LOOM_PHASE_LOG"
}
