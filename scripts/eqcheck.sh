#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Post-synthesis equivalence check (D22, Loom/Netlist/EQCHECK_SPEC.md).
#
# For each emitted design: synthesize `rtl/X.v` to a
# LUT/FF-mapped netlist with yosys and check, signal by signal, that the
# netlist's one-cycle transition function equals the µVerilog module's —
# every UNSAT LRAT-certified and re-checked by `Loom.Dp.Cert.checkLrat`.
#
# The generated netlists go to a scratch (gitignored) directory; nothing
# here writes into the repository.
#
# Designs with memories are checked bank by bank (D31): reset images, write
# ports against the primitives' own pins, and both read shapes. Every excluded
# signal is still named with its reason (EQCHECK_SPEC.md §Memories).
#
#   scripts/eqcheck.sh                  # the acceptance list
#   scripts/eqcheck.sh s0blinky         # one design
#   scripts/eqcheck.sh --negative-control
#
# Requires yosys + cadical; SKIPs (exit 0) if either is missing.
set -euo pipefail
cd "$(dirname "$0")/.."

for dep in yosys cadical; do
  if ! command -v "$dep" >/dev/null; then
    echo "eqcheck: SKIP ($dep not installed)"
    exit 0
  fi
done

OUT=${EQCHECK_OUT:-scratch/eqcheck}
mkdir -p "$OUT"
lake build eqcheck >/dev/null
EQ=.lake/build/bin/eqcheck

# Synthesize $1 to $OUT/$1.json.
#   * `proc; splitnets` before synthesis so every register bit keeps an
#     unambiguous netname (`wreduce` otherwise shrinks *and reorders* the
#     multi-bit register wires, making per-bit matching unsound);
#   * `select <top> %n; delete` drops the ~430 blackbox cell-library
#     modules from the JSON (9 MB -> 30 kB) without touching the top module.
synth() {
  local d=$1
  yosys -p "read_verilog rtl/$d.v; hierarchy -check -top $d; proc; splitnets; \
            synth_xilinx -flatten -nowidelut -top $d; \
            select $d %n; delete; select -clear; \
            write_json $OUT/$d.json" > "$OUT/$d.synth.log" 2>&1
}

if [ "${1:-}" = "--negative-control" ]; then
  # Mutate one LUT INIT bit of a synthesized netlist: the checker must FAIL
  # with a countermodel (proof that the tool can see a real difference).
  d=${2:-satcounter}
  [ -f "$OUT/$d.json" ] || synth "$d"
  python3 - "$OUT/$d.json" "$OUT/$d.mutant.json" <<'EOF'
import json, sys
src, dst = sys.argv[1], sys.argv[2]
d = json.load(open(src))
m = d['modules'][list(d['modules'])[0]]
for name, c in m['cells'].items():
    init = c.get('parameters', {}).get('INIT')
    if c['type'].startswith('LUT') and init and set(init) <= set('01'):
        flipped = ('0' if init[-1] == '1' else '1')
        c['parameters']['INIT'] = init[:-1] + flipped
        print(f"negative control: {c['type']} '{name}' INIT bit 0: "
              f"{init[-1]} -> {flipped}")
        break
else:
    sys.exit("negative control: no LUT with a 0/1 INIT found")
json.dump(d, open(dst, 'w'))
EOF
  echo "── eqcheck on the mutated netlist (a FAILURE here is the pass condition) ──"
  if "$EQ" "rtl/$d.v" "$OUT/$d.mutant.json"; then
    echo "negative control FAILED: eqcheck accepted a mutated netlist"
    exit 1
  else
    echo "negative control OK: eqcheck rejected the mutated netlist"
    exit 0
  fi
fi

designs=${*:-"s0blinky satcounter pingpong s13soak s0bscan epochengine lnp64mini_soc"}

# Emitted, not checked in (rtl/ is gitignored); regenerate what is missing.
[ -f rtl/lnp64mini_soc.v ] || lake env lean --run Machines/Lnp64mini/Emit.lean soc
[ -f rtl/epochengine.v ]   || lake env lean --run Machines/Epoch/Emit.lean engine

# Acknowledged failures, per design: a defect that IS real, is recorded
# elsewhere, and is deliberately not fixed by this run. It still prints in
# full, as an [ACK] line -- the flag stops it failing the gate, it does not
# stop it being seen. Mirrors `check_mem_init.py --allow`.
#
#   (tpc was here until 2026-08-01: lnp64mini's 32x64 thread-PC tables held
#   reset image 64'"'"'d4096 on a RAM32M-mapped bank -- the same D30 loss as the
#   epoch bank. D37 FIXED it rather than acknowledging it: the image is now
#   all-zero and the cmd-13 sweep establishes TEXT_BASE, so there is nothing
#   left to ack. See LOOM_GAPS.md D37 / EPOCH_SPEC.md E13.)
#   dmem  yosys 0.33 wires RAMB36E1 SDP-72 `DIPBDIP` to `DIPADIP`'"'"'s nets, so
#         data bits 44/53/62 are never written while `DOPBDOP` reads them --
#         a self-inconsistent netlist, and a synthesizer defect rather than an
#         emission one. See EQCHECK_SPEC.md §Deviations 13.
ack_for() {
  case "$1" in
    lnp64mini_soc) echo "--ack dmem" ;;
    *) echo "" ;;
  esac
}

status=0
for d in $designs; do
  synth "$d"
  # shellcheck disable=SC2046
  "$EQ" $(ack_for "$d") "rtl/$d.v" "$OUT/$d.json" || status=1
done
exit $status
