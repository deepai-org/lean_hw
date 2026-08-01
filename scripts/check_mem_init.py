#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
"""Guard: does the synthesis flow actually deliver the design's memory reset image?

Loom expresses a `MemDecl`'s reset image as a Verilog `initial` block.  On the
openXC7 path (yosys -> nextpnr-xilinx -> fasm2frames -> xc7frames2bit) that
image survives *only* for memories yosys maps to block RAM: the distributed-RAM
mapping (RAM32M / RAM64M / RAM*X1S) silently discards a non-zero init and emits
INIT_A..INIT_D = 0.  Nothing in the flow reports this, and the design then boots
on silicon with a memory the proofs say is initialized and the fabric says is
zero.  That is exactly how `epochengine`'s `cell_flags` (occupancy) was lost on
the ZC702 -- see `Machines/Epoch/EPOCH_SPEC.md` deviation E13.

This script re-derives the reset image from the emitted RTL and checks it
against the yosys netlist:

  * every memory with a non-zero reset image must be mapped to a BRAM
    primitive, and that primitive must carry a non-zero INIT_xx string;
  * every memory mapped to a distributed-RAM primitive must have an all-zero
    reset image (which the flow does deliver), and the primitive's INIT_x
    parameters must be zero to match.

Usage:  check_mem_init.py <synth.json> <emitted.v> [<emitted2.v> ...]
Exit 0 = the flow delivers every reset image; exit 1 = it does not.
"""

from __future__ import annotations

import json
import re
import sys

# yosys/Xilinx primitives that carry a configuration-time memory image.
BRAM_TYPES = {"RAMB18E1", "RAMB36E1", "RAMB18", "RAMB36"}
LUTRAM_TYPES = {"RAM32M", "RAM32M16", "RAM64M", "RAM64M8", "RAM32X1D", "RAM64X1D",
                "RAM128X1D", "RAM256X1S", "RAM32X1S", "RAM64X1S", "RAM128X1S"}

# `  name[123] = 32'd7;` inside an `initial` block.
INIT_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_$]*)\[(\d+)\]\s*=\s*(\d+)'([dhb])([0-9a-fA-FxXzZ_]+)\s*;")


def parse_reset_images(paths: list[str]) -> dict[str, dict[int, int]]:
    """memory name -> {index: value} from the emitted RTL's `initial` blocks."""
    images: dict[str, dict[int, int]] = {}
    for path in paths:
        with open(path) as fh:
            for line in fh:
                m = INIT_RE.match(line)
                if not m:
                    continue
                name, idx, _w, base, digits = m.groups()
                digits = digits.replace("_", "")
                if any(c in "xXzZ" for c in digits):
                    continue
                val = int(digits, {"d": 10, "h": 16, "b": 2}[base])
                images.setdefault(name, {})[int(idx)] = val
    return images


def mem_of_cell(cell_name: str) -> str:
    """`u_dual.ep_cell_flags.0.7` -> `ep_cell_flags`.

    yosys names a mapped memory's primitives `<mem>.<slice>.<bit>`; strip the
    trailing numeric groups and the instance path."""
    parts = cell_name.split(".")
    while len(parts) > 1 and parts[-1].isdigit():
        parts.pop()
    return parts[-1]


def init_is_nonzero(params: dict) -> bool:
    for key, val in params.items():
        if not re.fullmatch(r"INITP?_[0-9A-Fa-f]{2}|INIT_[A-D]", key):
            continue
        s = str(val)
        if any(c == "1" for c in s):
            return True
    return False


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        sys.stderr.write(__doc__)
        return 2
    netlist_path, rtl_paths = argv[1], argv[2:]

    images = parse_reset_images(rtl_paths)
    nonzero = {n for n, img in images.items() if any(v != 0 for v in img.values())}

    with open(netlist_path) as fh:
        design = json.load(fh)

    # Group the mapped primitives by the memory they came from.
    mapped: dict[str, dict[str, list[tuple[str, dict]]]] = {}
    for mod in design["modules"].values():
        for cname, cell in mod.get("cells", {}).items():
            ctype = cell["type"]
            kind = ("bram" if ctype in BRAM_TYPES else
                    "lutram" if ctype in LUTRAM_TYPES else None)
            if kind is None:
                continue
            mem = mem_of_cell(cname)
            mapped.setdefault(mem, {}).setdefault(kind, []).append((cname, cell))

    failures: list[str] = []
    checked = 0
    for mem, bykind in sorted(mapped.items()):
        if mem not in images:
            continue  # not a Loom memory we can account for
        checked += 1
        want_nonzero = mem in nonzero
        kinds = sorted(bykind)
        if want_nonzero and "lutram" in bykind:
            cname = bykind["lutram"][0][0]
            failures.append(
                f"{mem}: reset image is NON-ZERO but yosys mapped it to distributed "
                f"RAM ({bykind['lutram'][0][1]['type']}, e.g. {cname}); that path "
                f"discards the init and the bank comes up all-zero on silicon")
            continue
        if want_nonzero:
            if not any(init_is_nonzero(c["parameters"]) for _n, c in bykind["bram"]):
                failures.append(
                    f"{mem}: reset image is NON-ZERO but every mapped BRAM "
                    f"primitive has an all-zero INIT")
                continue
            print(f"ok   {mem}: non-zero reset image, {kinds} with non-zero INIT")
        else:
            bad = [n for kind in bykind for n, c in bykind[kind]
                   if init_is_nonzero(c["parameters"])]
            if bad:
                failures.append(
                    f"{mem}: reset image is all-zero but {bad[0]} carries a "
                    f"non-zero INIT")
                continue
            print(f"ok   {mem}: all-zero reset image, {kinds} with zero INIT")

    for f in failures:
        print(f"FAIL {f}")
    if failures:
        print(f"check_mem_init: {len(failures)} memor"
              f"{'y' if len(failures) == 1 else 'ies'} of {checked} are NOT "
              f"initialized by this flow")
        return 1
    print(f"check_mem_init: OK -- {checked} memories, every reset image delivered")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
