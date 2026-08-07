#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# W6 calibration: fit CostTarget weights from MEASURED synthesis output.
#
# The weights in Loom/Hw/CostTarget.lean are empirical metadata, and this is
# the only thing allowed to produce them. A weight nobody fitted is marked
# `.provisional` and the report says so -- the ECP5 MemTarget profile is the
# standing example of a datasheet reading that could be mistaken for a
# measurement, and the point of this script is that xc7z020 need not be one.
#
# Input: (design, cost-vector, measured LUT cells) rows, where the cost vector
# comes from `lake exe costreport` and the LUT count from the netlist JSON the
# board flow already produces:
#   python3 -c "import json;from collections import Counter; ..."  (see README)
#
# Model: LUTs ~= wState*stateBits + wBitOps*bitOps + wSoft*softBits, weights in
# milli-units. Non-negative least squares over whatever rows are supplied, then
# the residual per row is REPORTED -- a fit whose residual is large is a fit
# that has not earned its provenance upgrade.
import sys, json, itertools

def fit(rows):
    # Tiny non-negative grid/refine search: three weights, few rows, no numpy.
    best = None
    grids = [range(0, 2001, 200), range(0, 41, 4), range(0, 4001, 400)]
    for _ in range(4):
        for ws, wb, wsoft in itertools.product(*grids):
            err = 0.0
            for r in rows:
                pred = (r["stateBits"]*ws + r["bitOps"]*wb + r["softBits"]*wsoft) / 1000.0
                err += (pred - r["luts"]) ** 2
            if best is None or err < best[0]:
                best = (err, ws, wb, wsoft)
        _, ws, wb, wsoft = best
        grids = [range(max(0, ws-200), ws+201, 40),
                 range(max(0, wb-4), wb+5, 1),
                 range(max(0, wsoft-400), wsoft+401, 80)]
    return best

def main():
    rows = json.load(open(sys.argv[1]))
    err, ws, wb, wsoft = fit(rows)
    print(f"fitted (milli-units): wStateBits={ws} wBitOps={wb} wSoftBits={wsoft}")
    worst = 0.0
    for r in rows:
        pred = (r["stateBits"]*ws + r["bitOps"]*wb + r["softBits"]*wsoft) / 1000.0
        rel = abs(pred - r["luts"]) / max(1, r["luts"]) * 100
        worst = max(worst, rel)
        print(f"  {r['name']:24} predicted {pred:9.0f}  measured {r['luts']:7}  ({rel:5.1f}%)")
    print(f"worst residual: {worst:.1f}%  -- rows: {len(rows)}")
    if len(rows) < 4:
        print("NOTE: fewer rows than weights+1. The fit is UNDERDETERMINED;")
        print("      keep the provenance at .provisional until more designs are measured.")
main()
