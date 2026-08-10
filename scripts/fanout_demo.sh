#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Emit and corroborate the verified fan-out duplication demo. The Lean side
# proves refinement and reports the technology-independent cost vector; the
# external side checks RTL behavior and reports what generic Yosys actually
# retains after optimization.
set -euo pipefail
cd "$(dirname "$0")/.."

lake env lean --run Machines/Substrate/Emit.lean fanout

iverilog -g2012 -o rtl/fanout.vvp \
  rtl/fanout_base.v rtl/fanout_split.v rtl/tb_fanout.v
RTL_OUT=$(vvp rtl/fanout.vvp | grep '^fanout_demo:')
echo "RTL: $RTL_OUT"
if [ "$RTL_OUT" != "fanout_demo: OK (visible equivalence + replica coherence, 40 cycles)" ]; then
  echo "fanout_demo: RTL DIVERGENCE" >&2
  exit 1
fi

if ! command -v yosys >/dev/null 2>&1 || ! command -v jq >/dev/null 2>&1; then
  echo "fanout_demo: yosys/jq unavailable; synthesis measurement skipped"
  exit 0
fi

MEASURE_DIR=$(mktemp -d)
trap 'rm -rf "$MEASURE_DIR"' EXIT

yosys -q -p "read_verilog -sv rtl/fanout_base.v; synth -top fanout_base; write_json $MEASURE_DIR/base.json"
yosys -q -p "read_verilog -sv rtl/fanout_split.v; synth -top fanout_split; write_json $MEASURE_DIR/split.json"
yosys -q -p "read_verilog -sv rtl/fanout_split.v; hierarchy -top fanout_split; proc; \
  select -assert-count 4 w:source %ci1 w:source__dup %ci1; \
  setattr -set keep 1 w:source %ci1 w:source__dup %ci1; \
  synth -top fanout_split; write_json $MEASURE_DIR/preserved.json"

cell_count() {
  jq -r --arg top "$2" '.modules[$top].cells | length' "$1"
}

dff_count() {
  jq -r --arg top "$2" \
    '[.modules[$top].cells[].type | select(contains("DFF"))] | length' "$1"
}

net_max_load() {
  jq -r --arg top "$2" --arg net "$3" '
    .modules[$top] as $module |
    ($module.netnames[$net].bits // [] | map(select(type == "number"))) as $bits |
    [$module.cells[] as $cell |
      $cell.port_directions | to_entries[] | select(.value == "input") |
      .key as $port | $cell.connections[$port][] | select(type == "number") |
      select(. as $bit | $bits | index($bit))] |
    group_by(.) | map(length) | max // 0' "$1"
}

BASE_CELLS=$(cell_count "$MEASURE_DIR/base.json" fanout_base)
SPLIT_CELLS=$(cell_count "$MEASURE_DIR/split.json" fanout_split)
BASE_DFFS=$(dff_count "$MEASURE_DIR/base.json" fanout_base)
SPLIT_DFFS=$(dff_count "$MEASURE_DIR/split.json" fanout_split)
BASE_LOAD=$(net_max_load "$MEASURE_DIR/base.json" fanout_base source)
SPLIT_SOURCE_LOAD=$(net_max_load "$MEASURE_DIR/split.json" fanout_split source)
SPLIT_REPLICA_LOAD=$(net_max_load "$MEASURE_DIR/split.json" fanout_split source__dup)
ALIASED=$(jq -r \
  '.modules.fanout_split.netnames.source.bits == .modules.fanout_split.netnames.source__dup.bits' \
  "$MEASURE_DIR/split.json")
PRESERVED_CELLS=$(cell_count "$MEASURE_DIR/preserved.json" fanout_split)
PRESERVED_DFFS=$(dff_count "$MEASURE_DIR/preserved.json" fanout_split)
PRESERVED_SOURCE_LOAD=$(net_max_load "$MEASURE_DIR/preserved.json" fanout_split source)
PRESERVED_REPLICA_LOAD=$(net_max_load "$MEASURE_DIR/preserved.json" fanout_split source__dup)
PRESERVED_ALIASED=$(jq -r \
  '.modules.fanout_split.netnames.source.bits == .modules.fanout_split.netnames.source__dup.bits' \
  "$MEASURE_DIR/preserved.json")

echo "Yosys $(yosys -V | sed 's/^Yosys //')"
echo "  base:  cells=$BASE_CELLS dffs=$BASE_DFFS source_max_pin_load=$BASE_LOAD"
echo "  split: cells=$SPLIT_CELLS dffs=$SPLIT_DFFS source_max_pin_load=$SPLIT_SOURCE_LOAD replica_max_pin_load=$SPLIT_REPLICA_LOAD"
if [ "$ALIASED" = "true" ]; then
  echo "  result: generic synthesis merged source/source__dup; no physical fan-out split survives"
else
  echo "  result: distinct source/source__dup nets survive generic synthesis"
fi
echo "  preserved split: cells=$PRESERVED_CELLS dffs=$PRESERVED_DFFS source_max_pin_load=$PRESERVED_SOURCE_LOAD replica_max_pin_load=$PRESERVED_REPLICA_LOAD"
if [ "$PRESERVED_ALIASED" = "true" ]; then
  echo "fanout_demo: Yosys keep constraint did not preserve distinct replicas" >&2
  exit 1
fi
echo "  preserved result: a checked Yosys keep constraint retains distinct source/source__dup flops"

echo "fanout_demo: OK (proof + RTL corroboration + synthesis measurement)"
