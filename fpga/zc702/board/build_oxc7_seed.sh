#!/bin/bash
# build_oxc7_seed.sh -- openXC7 build for the ZC702 xc7z020, with a staleness
# gate at every stage.
#
# Flow: yosys (synth) -> nextpnr-xilinx (P&R -> FASM) -> fasm2frames -> xc7frames2bit
# Usage (run from ~/substrate0):
#   [NPNR_SEED=n] oxc7/build_oxc7_seed.sh <TOP> <xdc> <src.v> [src2.v ...]
#
# WHY THE GATE EXISTS (fpga_dev.md §71c, 2026-08-07). The previous version had
# `set -e`, which looks like it covers this and does not: every stage is piped
# into `tee`/`tail`, so the pipeline's exit status is the *filter's*, not the
# tool's. A killed yosys therefore returned 0, the script walked straight on to
# nextpnr against the json from the PREVIOUS build -- five hours old -- and
# produced a .bit timestamped now, containing a core from then. It even
# reported a plausible Fmax, because it was the old design's Fmax. The tell was
# the timestamp pair (.bit at 18:20, .json at 03:02) and nothing else.
#
# A bitstream is the most expensive possible file to be lying about. So:
# `pipefail` makes a dead tool fail the stage, and each stage additionally
# asserts that its OUTPUT is newer than its INPUT. Belt and braces on purpose --
# the pipefail fix alone would not catch a tool that exits 0 without writing.
#
# This file is the source of truth (REPO_BOUNDARY.md); push it with
# scripts/board_sync.sh rather than editing the copy on the board host, which
# is how §69's boot-script divergence happened.
set -euo pipefail
NP=/snap/openxc7/current/opt/nextpnr-xilinx
DB=$NP/external/prjxray-db/zynq7
PART=xc7z020clg484-1
CHIPDB=$HOME/substrate0/oxc7/xc7z020.bin

TOP=$1; XDC=$2; shift 2
SRCS="$@"
O=$HOME/substrate0/oxc7/out/$TOP
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
# YOSYS_SYNTH_FLAGS: extra `synth_xilinx` flags for this target. The board
# flow needs `-nodsp` while openXC7 cannot complete an inferred DSP48: a
# native 64x64 multiply makes yosys emit a DSP macro and the flow dies with
# "Port PCOUT46 has no connections" (2026-08-10). Measured cost of the
# fallback on this device: 3833 LUTs per multiplier, so two cores move the
# dual from ~46% to ~53% -- inside the reseed-lottery band, not free.
yosys -q -p "read_verilog $SRCS; synth_xilinx -flatten -nowidelut ${YOSYS_SYNTH_FLAGS:-} -top $TOP; write_json $O.json" 2>&1 | tee "$O.synth.log"
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
ls -l "$O.bit" && echo "OXC7_BUILD_DONE bit=$O.bit"
