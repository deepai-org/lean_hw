#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
#
# The four standing gates, run on a schedule (see crontab: nightly):
#
#   1. audit tier   — a clean-checkout kernel-only release build completes
#                     and stays inside the overnight bound (<= 4 h wall);
#                     its phase timings are recorded per run.
#   2. compiler-output — the shipped witnesses equal Design.toProgram
#                     (enforced inside the release build as the
#                     'toProgram parity gate' phases).
#   3. tutorial path — the documented user path (design + invariant +
#                     transport) still builds, and its axiom closure is
#                     exactly propext/Classical.choice/Quot.sound.
#   4. CI tier      — representative single-edit warm-cache recheck classes
#                     each complete under 600 s. The recheck cost of an
#                     edit class is measured as recompiling the module the
#                     edit touches, from the warm cache the audit run just
#                     produced.
#
# Every failure is a real regression: the script exits nonzero and the
# summary CSV row records which gate broke.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
ulimit -s unlimited

stamp=$(date -u +%Y%m%dT%H%M%SZ)
outdir=".lake/release-metrics/nightly-$stamp"
mkdir -p "$outdir"
summary="$outdir/gates.csv"
echo "gate,wall_seconds,limit_seconds,status" > "$summary"
overall=0

record() { # name wall limit status
  echo "$1,$2,$3,$4" >> "$summary"
  echo "gate $1: $4 (${2}s, limit ${3}s)"
  [[ "$4" == PASS ]] || overall=1
}

measure() { # name limit command...
  local name=$1 limit=$2; shift 2
  local start end wall status
  start=$(date +%s)
  if "$@" >> "$outdir/$name.log" 2>&1; then status=ok; else status=fail; fi
  end=$(date +%s)
  wall=$((end - start))
  if [[ "$status" == ok && "$wall" -le "$limit" ]]; then
    record "$name" "$wall" "$limit" PASS
  elif [[ "$status" == ok ]]; then
    record "$name" "$wall" "$limit" "FAIL(over-budget)"
  else
    record "$name" "$wall" "$limit" "FAIL(error)"
  fi
}

# ---- Gate 1+2: clean-checkout audit run (parity gates are internal phases).
# Wipes generated sources and all build objects; pinned .lake/packages kept.
if [[ "${NIGHTLY_SKIP_CLEAN:-0}" != 1 ]]; then
  rm -rf GeneratedRelease rtl .lake/build
  measure "audit-clean-release" 14400 scripts/build_verified_release.sh 32
else
  echo "gate audit-clean-release: SKIPPED (NIGHTLY_SKIP_CLEAN=1)"
fi

# ---- Gate 3: the tutorial path, plus its exact axiom closure.
tutorial_gate() {
  lake build Machines.Tutorial.SatCounter || return 1
  lake env lean --run Machines/Tutorial/SatCounter.lean || return 1
  local axioms
  axioms=$(mktemp)
  cat > "$axioms" <<'EOF'
import Machines.Tutorial.SatCounter
open Machines.Tutorial.SatCounter in
run_cmd do
  let closure ← Lean.collectAxioms `Machines.Tutorial.SatCounter.satOk_rtl
  let expected := #[`propext, `Classical.choice, `Quot.sound]
  unless closure.toList.toArray.qsort (·.toString < ·.toString) ==
      expected.qsort (·.toString < ·.toString) do
    throwError "unexpected axiom closure: {closure}"
EOF
  lake env lean "$axioms"
}
measure "tutorial-path" 600 tutorial_gate

# ---- Gate 4: warm-cache single-edit recheck classes.
# Each class re-elaborates and kernel-checks the module a representative
# edit touches, against the warm cache. Downstream joins are not yet
# included (v1 approximation, noted in RELEASE_COST.md).
measure "edit-user-design" 600 \
  lake env lean Machines/Tutorial/SatCounter.lean
measure "edit-hybrid-leaf" 600 \
  lake env lean -j 1 "$(realpath GeneratedRelease/Lnp64u/HybridReg0000.lean)" \
    -o "$outdir/HybridReg0000.olean"
measure "edit-semantic-mems" 600 \
  lake env lean "$(realpath GeneratedRelease/Lnp64u/SemanticMems.lean)" \
    -o "$outdir/SemanticMems.olean"

echo "summary: $summary"
cat "$summary"
exit "$overall"
