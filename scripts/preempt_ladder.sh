#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# EXT-1/EXT-2 — the lnp64mini extension ladder (preemption tick, domains)
# EXT-1 — the preemption tick (`Machines/Lnp64mini/EXTEND_SPEC.md` increment 1):
#
#   1. FastEval acceptance selftest (EDSL ≡ ISS on the quantum, + the four
#      architectural claims: switch / no-stall / cooperative / resume / Law-5)
#   2. D19 sync-read shape (the core grew registers, not memory reads)
#   3. emit rtl/lnp64mini{,_soc,_dual}.v and fpga/zc702/preempt.hex
#   4. iverilog: the spinner program on the emitted soc, preemptive AND
#      cooperative, diffed against the Lean ISS oracle byte for byte
#   5. iverilog: the six pre-existing system testbenches, which must still
#      print exactly DUAL_SPEC's numbers — with the quantum off AND on
#      (every one of those programs is single-threaded, so a quantum that
#      only ever preempts to a *different* READY thread cannot move them)
set -euo pipefail
cd "$(dirname "$0")/.."
# Compiled selftests: the interpreted path costs ~25 min per lockstep run and
# overflows the interpreter stack in `Design.reset`. `lake exe minitest` runs
# the same `main` natively -- the MMU selftest goes 25 min -> 45 s.
lake build minitest >/dev/null
MINI=./.lake/build/bin/minitest
Z=fpga/zc702
T=${TMPDIR:-/tmp}/preempt_ladder.$$
mkdir -p "$T"
trap 'rm -rf "$T"' EXIT

echo "### 0. EXT-2 domain selftest (EDSL == ISS on cur_dom + all 32 tdom slots,"
echo "        and the architectural claim: CLONE cannot leave its domain)"
$MINI domselftest

echo "### 0b. EXT-3 fail-stop selftest (poison stops the RUNNER and"
echo "         deschedules the READY -- two distinct enforcement points)"
$MINI failstopselftest

echo "### 1. FastEval selftest (EXT-1)"
$MINI preemptselftest | tee "$T/self.txt"
grep -q 'PREEMPT SELFTEST OK' "$T/self.txt"

echo "### 2. D19 report"
$MINI d19 >/dev/null

echo "### 3. emit"
$MINI       >/dev/null
$MINI soc   >/dev/null
$MINI dual  >/dev/null
$MINI preempthex >/dev/null

echo "### 4. iverilog: the Law-5 spinner vs the Lean oracle"
iverilog -g2012 -DPROG_HEX="\"$Z/preempt.hex\"" -DQUANTUM="32'd64" \
  -o "$T/pq.vvp" rtl/lnp64mini_soc.v $Z/tb_lnp64mini_preempt.v
vvp "$T/pq.vvp" | grep '^PREEMPT' > "$T/rtl_q64.txt"
$MINI preemptpredict 64 > "$T/or_q64.txt"
diff "$T/or_q64.txt" "$T/rtl_q64.txt"
iverilog -g2012 -DPROG_HEX="\"$Z/preempt.hex\"" \
  -o "$T/pc.vvp" rtl/lnp64mini_soc.v $Z/tb_lnp64mini_preempt.v
vvp "$T/pc.vvp" | grep '^PREEMPT' > "$T/rtl_q0.txt"
$MINI preemptpredict 0 > "$T/or_q0.txt"
diff "$T/or_q0.txt" "$T/rtl_q0.txt"
grep -q 'halted=1 trap=0 pc=4136 r5=1 r9=42 dmem0=1 t1state=0 preempted=1' "$T/rtl_q64.txt"
grep -q 'halted=0 trap=0 pc=0 r5=0 r9=0 dmem0=0 t1state=1 preempted=0' "$T/rtl_q0.txt"
echo "preempt_ladder: iverilog == ISS oracle; the spinner terminates ONLY with a quantum"

echo "### 5. the six system testbenches, quantum off and on"
run_tbs () {                       # $1 = outdir; EXTRA[] = extra iverilog defines
  local O=$1
  mkdir -p "$O"
  iverilog -g2012 -DPROG_HEX="\"$Z/loomcheck.hex\"" ${EXTRA[@]+"${EXTRA[@]}"} \
    -o "$O/a.vvp" rtl/lnp64mini_soc.v $Z/tb_lnp64mini_soc.v
  vvp "$O/a.vvp" | grep -v 'finish called' > "$O/soc.txt"
  local pair p0 p1
  for pair in "loomcheck:loomcheck" "smpcount:smpcount" "smpcount:smpcount_skew" \
              "pingpong0:pingpong1"; do
    p0=${pair%:*}; p1=${pair#*:}
    iverilog -g2012 -DPROG_HEX0="\"$Z/$p0.hex\"" -DPROG_HEX1="\"$Z/$p1.hex\"" \
      ${EXTRA[@]+"${EXTRA[@]}"} \
      -o "$O/$p0-$p1.vvp" rtl/lnp64mini_dual.v $Z/tb_lnp64mini_dual.v
    vvp "$O/$p0-$p1.vvp" | grep -v 'finish called' > "$O/$p0-$p1.txt"
  done
  iverilog -g2012 -DONLY_C0 -DPROG_HEX0="\"$Z/loomcheck.hex\"" ${EXTRA[@]+"${EXTRA[@]}"} \
    -o "$O/only_c0.vvp" rtl/lnp64mini_dual.v $Z/tb_lnp64mini_dual.v
  vvp "$O/only_c0.vvp" | grep -v 'finish called' > "$O/only_c0.txt"
}
EXTRA=()
run_tbs "$T/q0"
EXTRA=(-DQUANTUM="32'd64")
run_tbs "$T/q64"
for f in soc.txt loomcheck-loomcheck.txt smpcount-smpcount.txt \
         smpcount-smpcount_skew.txt pingpong0-pingpong1.txt only_c0.txt; do
  cmp "$T/q0/$f" "$T/q64/$f"
done
# the recorded DUAL_SPEC numbers, not merely self-consistency
grep -q 'HALTED=1 cycles=273 pc=4192 retire=25' "$T/q0/soc.txt"
grep -q 'CYCLES=372'   "$T/q0/loomcheck-loomcheck.txt"
grep -q 'CYCLES=12540' "$T/q0/smpcount-smpcount.txt"
grep -q 'CYCLES=14933' "$T/q0/smpcount-smpcount_skew.txt"
grep -q 'CYCLES=2014'  "$T/q0/pingpong0-pingpong1.txt"
grep -q 'CYCLES=346'   "$T/q0/only_c0.txt"
echo "preempt_ladder: the six testbenches reproduce DUAL_SPEC's numbers, quantum 0 AND 64"

echo "preempt_ladder: OK"
