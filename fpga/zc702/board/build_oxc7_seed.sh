#!/bin/bash
# build_oxc7_seed.sh -- openXC7 build for the ZC702 xc7z020, with a staleness
# gate at every stage.
#
# Flow: yosys (synth) -> nextpnr-xilinx (P&R -> FASM) -> fasm2frames -> xc7frames2bit
# Usage (run from the configured board root):
#   [NPNR_SEED=n] oxc7/build_oxc7_seed.sh <TOP> <xdc> <src.v> [src2.v ...]
#
# `pipefail` preserves producer failures through `tee`/`tail`; every stage also
# requires a nonempty output at least as new as all of its inputs. This prevents
# a later stage from accepting an artifact left by an earlier build.
#
# This file is the source of truth (REPO_BOUNDARY.md); push it with
# scripts/board_sync.sh rather than editing the copy on the board host, which
# is how §69's boot-script divergence happened.
set -euo pipefail
NP=/snap/openxc7/current/opt/nextpnr-xilinx
DB=$NP/external/prjxray-db/zynq7
PART=xc7z020clg484-1
LOOM_OXC7_DIR=${LOOM_OXC7_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}
CHIPDB=${CHIPDB:-$LOOM_OXC7_DIR/xc7z020.bin}

TOP=$1; XDC=$2; shift 2
SRCS="$@"
O=$LOOM_OXC7_DIR/out/$TOP
mkdir -p "$(dirname "$O")"

# fresher <out> <in>... -- fail unless <out> exists, is non-empty, and is at
# least as new as every input. `-nt` is false for equal mtimes, so the test is
# "not older than", spelled as "no input is newer".
fresher() {
  local out=$1; shift
  [ -s "$out" ] || { echo "OXC7_BUILD_FAILED: $out missing or empty"; exit 1; }
  local in
  for in in "$@"; do
    if [ "$in" -nt "$out" ]; then
      echo "OXC7_BUILD_FAILED: $out is STALE -- $in is newer"
      echo "  (a stage produced no output and a later stage would have used the"
      echo "   previous build's artifact; see this script's header)"
      exit 1
    fi
  done
}

echo "### [1/4] yosys synth ($TOP) ###"
rm -f "$O.json"
# The portable default is the current accepted artifact: stock openXC7 0.8.2
# with `-nodsp` (59035/106400 LUTs, 32.86 MHz). Set YOSYS_SYNTH_FLAGS="" to
# exercise DSP inference on openXC7 0.9.2 or newer. No DSP-enabled artifact is
# currently accepted by the board ladder; see ../README.md.
yosys -q -p "read_verilog $SRCS; synth_xilinx -flatten -nowidelut ${YOSYS_SYNTH_FLAGS--nodsp} -top $TOP; write_json $O.json" 2>&1 | tee "$O.synth.log"
fresher "$O.json" $SRCS "$XDC"

echo "### [2/4] nextpnr-xilinx P&R ###"
rm -f "$O.fasm" "$O.bit"
nextpnr-xilinx --seed "${NPNR_SEED:-1}" --chipdb "$CHIPDB" --xdc "$XDC" --json "$O.json" --fasm "$O.fasm" --write "$O.routed.json" 2>&1 | tee "$O.pnr.log"
fresher "$O.fasm" "$O.json"

echo "### [3/4] fasm2frames ###"
rm -f "$O.frm"
fasm2frames --db-root "$DB" --part "$PART" "$O.fasm" "$O.frm" 2>&1 | tail -3
fresher "$O.frm" "$O.fasm"

echo "### [4/4] xc7frames2bit ###"
xc7frames2bit --part_name "$PART" --frm_file "$O.frm" --output_file "$O.bit" --part_file "$DB/$PART/part.yaml" 2>&1 | tail -3
fresher "$O.bit" "$O.frm"

# The routed Fmax, echoed next to the bit so a build's timing is in the same
# place as its artifact rather than buried in the P&R log.
grep -E "Max frequency for clock .*'sysclk'" "$O.pnr.log" | tail -1 || true
# Record WHAT PRODUCED THIS BITSTREAM. `/snap/openxc7/current` is a moving
# symlink and nothing else in the repo pins it, so without this a tool refresh
# can change the silicon with no evidence but a puzzling Fmax. Same doctrine as
# the guest image's build stamp: an artifact names its producer.
{ echo "bit:      $(basename "$O.bit")  $(stat -c%s "$O.bit") bytes"
  echo "built:    $(date -Is)"
  echo "nextpnr:  $(nextpnr-xilinx --version 2>&1 | head -1)"
  echo "yosys:    $(yosys -V 2>&1 | head -1)"
  echo "chipdb:   $CHIPDB  $(md5sum "$CHIPDB" 2>/dev/null | cut -c1-12)"
  echo "synth:    synth_xilinx -flatten -nowidelut ${YOSYS_SYNTH_FLAGS--nodsp}"
  echo "seed:     ${NPNR_SEED:-default}"
  echo "sources:  $SRCS"
} > "$O.toolchain.txt"
cat "$O.toolchain.txt"
ls -l "$O.bit" && echo "OXC7_BUILD_DONE bit=$O.bit"
