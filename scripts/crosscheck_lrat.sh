#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Cross-validation of the two LRAT checkers (charter Phase 3; PLAN P6 / §8 4.2).
#
# Legs:
#   1. `checker/` — the independent, from-scratch, strict hint-driven RUP
#      checker (`lake exe chk`), zero shared code with Loom/Std.Sat.
#   2. Loom's proved checker (`Loom.Dp.Cert.checkLrat`, i.e. Lean core's
#      verified `Std.Tactic.BVDecide.LRAT.check`), driven by
#      `scripts/loom_check_lrat.lean` via the interpreter.
#
# Matrix: cadical-produced php4..php6 certificates must be ACCEPTED by both;
# mutated certificates must be REJECTED. One documented divergence: the
# `drophint` mutation removes a hint from the final empty-clause step —
# the resulting certificate is still semantically derivable, so Loom/Std's
# checker (which runs full unit propagation, not strict hint-following)
# soundly ACCEPTS it, while `chk` strictly REJECTS it. Only `chk` is tested
# on that case. (Std's checker also panics on deletions of out-of-range
# ids, so the loom leg is only fed structurally in-range certificates.)
#
# Requires cadical + python3; SKIPs (exit 0) if either is missing, so it is
# safe to call from CI without making CI depend on cadical.
set -euo pipefail
cd "$(dirname "$0")/.."

for dep in cadical python3; do
  if ! command -v "$dep" >/dev/null; then
    echo "crosscheck_lrat: SKIP ($dep not installed)"
    exit 0
  fi
done

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

echo "crosscheck_lrat: building checker/ ..."
(cd checker && lake build chk >/dev/null)
CHK=checker/.lake/build/bin/chk

# Pigeonhole CNFs: n+1 pigeons, n holes (UNSAT), var(i,j) = i*n + j + 1.
python3 - "$tmp" <<'EOF'
import sys
tmp = sys.argv[1]
for n in (4, 5, 6):
    cls = [[i*n + j + 1 for j in range(n)] for i in range(n+1)]
    for j in range(n):
        for i1 in range(n+1):
            for i2 in range(i1+1, n+1):
                cls.append([-(i1*n+j+1), -(i2*n+j+1)])
    with open(f"{tmp}/php{n}.cnf", "w") as f:
        f.write(f"p cnf {(n+1)*n} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
EOF

fail=0
report() { echo "crosscheck_lrat: $1"; }
bad()    { report "FAIL: $1"; fail=1; }

# ── Positive matrix: both checkers accept cadical's certificates ──
for n in 4 5 6; do
  cadical -q --lrat --no-binary "$tmp/php$n.cnf" "$tmp/php$n.lrat" >/dev/null && rc=$? || rc=$?
  [ "$rc" -eq 20 ] || { bad "cadical did not report UNSAT for php$n (exit $rc)"; continue; }
  if "$CHK" "$tmp/php$n.cnf" "$tmp/php$n.lrat" >/dev/null; then
    report "chk  accepts php$n: ok"
  else
    bad "chk rejected cadical's php$n certificate"
  fi
  if lake env lean --run scripts/loom_check_lrat.lean "$tmp/php$n.cnf" "$tmp/php$n.lrat" >/dev/null 2>&1; then
    report "loom accepts php$n: ok"
  else
    bad "Loom-side checker rejected cadical's php$n certificate"
  fi
done

# ── Negative matrix: mutated php5 certificates ──
python3 - "$tmp" <<'EOF'
import sys
tmp = sys.argv[1]
lines = open(f"{tmp}/php5.lrat").read().splitlines()

def write(name, ls):
    open(f"{tmp}/php5_{name}.lrat", "w").write("\n".join(ls) + "\n")

# flip: negate the first literal of the first addition step
out, done = [], False
for L in lines:
    t = L.split()
    if not done and "d" not in t and len(t) > 2 and t[1] != "0":
        t[1] = str(-int(t[1])); L = " ".join(t); done = True
    out.append(L)
write("flip", out)

# drophint: remove the first hint of the empty-clause step
out = []
for L in lines:
    t = L.split()
    if "d" not in t and t[1] == "0":
        del t[2]; L = " ".join(t)
    out.append(L)
write("drophint", out)

# trunc: drop the final (empty-clause) step
write("trunc", lines[:-1])

# delbad: delete a clause id that was never added
write("delbad", ["1 d 99999 0"] + lines)
EOF

for m in flip drophint trunc delbad; do
  if "$CHK" "$tmp/php5.cnf" "$tmp/php5_$m.lrat" >/dev/null 2>&1; then
    bad "chk ACCEPTED mutated certificate php5_$m"
  else
    report "chk  rejects php5_$m: ok"
  fi
done
# Loom leg on the semantically-broken mutations (see header for why
# drophint and delbad are excluded).
for m in flip trunc; do
  if lake env lean --run scripts/loom_check_lrat.lean "$tmp/php5.cnf" "$tmp/php5_$m.lrat" >/dev/null 2>&1; then
    bad "Loom-side checker ACCEPTED mutated certificate php5_$m"
  else
    report "loom rejects php5_$m: ok"
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "crosscheck_lrat: OK (both checkers agree on php4..php6 + mutations)"
else
  echo "crosscheck_lrat: FAILURES above"
  exit 1
fi
