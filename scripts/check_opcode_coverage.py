#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# Every opcode the design defines must be EXERCISED by the generated matrix, or
# be on an explicit exclusion list with a written reason.
#
# This exists because of the 2026-08-05 renumbering, which passed every gate and
# then panicked on silicon. The defect class was not "an opcode was renumbered
# wrongly" -- it was **the list was incomplete**. `opDiffSelftest`'s `aluOpsIMM`
# stopped at `sltiu`, so `liu` and `auipc` were never executed by any generated
# program, and `liu` is how 64-bit constants are built.
#
# Hand-appending those two would reproduce the hazard for the next opcode added.
# So coverage is checked against the SAME table the design is built from --
# `Machines/Lnp64mini/Core.lean`'s `OP_` constants -- and a new opcode with no
# coverage and no stated exclusion is a red gate, not a silent hole.
#
# This is the opcode analogue of `StateCover.lean`: the design enumerates
# itself, the harness declares what it covers, and the difference is a named
# failure rather than an accident.

import pathlib
import re
import sys

HW = pathlib.Path(__file__).resolve().parent.parent
CORE = HW / "Machines/Lnp64mini/Core.lean"
HARNESS = HW / "Machines/Lnp64mini/Harness.lean"

# Opcodes the generated matrix cannot drive, each with the reason and the test
# that covers it instead. An entry here is a CLAIM that something else checks
# it; it is not permission to ignore it.
EXCLUDED = {
    "NOP":        "no architectural effect; executed as padding by every program",
    "INVALID":    "the deliberate unknown-opcode trap; covered by progTrapReal",
    "MOV":        "assembler alias of addi rd, rs, 0 -- same encoding path",
    "EXIT":       "terminates every generated program, so every entry executes it",
    "THREAD_EXIT":"covered by selftest's SCH script (CLONE + YIELD + THREAD_EXIT)",
    "SLEEP":      "covered by selftest's SLP script (sleep-scan wake + S_WAIT)",
    "YIELD":      "covered by selftest's SCH script and preemptselftest",
    "CLONE_SPAWN":"covered by smpselftest and domselftest (inheritance rule)",
    "FUTEX_WAIT": "needs a doorbell input; covered by smpselftest DOORBELL",
    "FUTEX_WAKE": "needs the wake bank; covered by smpselftest WAKEOUT",
    "LR_D":       "reservation pair; covered by selftest LRSC and smpselftest",
    "LR_D_ACQ":   "reservation pair; covered by selftest LRSC",
    "LR_D_ACQ_REL":"reservation pair; covered by selftest LRSC",
    "SC_D":       "reservation pair; covered by selftest LRSC and smpselftest",
    "SC_D_REL":   "reservation pair; covered by selftest LRSC",
    "SC_D_ACQ_REL":"reservation pair; covered by selftest LRSC",
    "MINI_GATE_CALL":  "changes domain; covered by gateselftest and capxferselftest",
    "MINI_GATE_RETURN":"changes domain; covered by gateselftest and capxferselftest",
    "MINI_CAP_SEND":   "covered by capxferselftest (right and wrong domain)",
    "MINI_CAP_RECV":   "covered by capxferselftest (right and wrong domain)",
    "GET_PCR":    "reads a control register; covered by selftest's progLS",
    "FENCE":    "ordering only, no architectural result to compare",
    "FENCE_D1": "ordering only, no architectural result to compare",
    "FENCE_D2": "ordering only, no architectural result to compare",
    "FENCE_D3": "ordering only, no architectural result to compare",
    "FENCE_D4": "ordering only, no architectural result to compare",
}


def design_opcodes():
    src = CORE.read_text()
    return {m.group(1): int(m.group(2), 16)
            for m in re.finditer(r"^def OP_([A-Z0-9_]+) : Nat := (0x[0-9a-f]+)",
                                 src, re.M)}


def matrix_opcodes():
    """Names the generated matrix executes, read out of its own lists."""
    src = HARNESS.read_text()
    names = set()
    for listname in ("aluOpsRRR", "aluOpsRR", "aluOpsIMM", "selOps",
                     "memOpsLoad", "memOpsStore", "brOps",
                     "wideImmOps", "jumpOps"):
        m = re.search(rf"def {listname} : List \(Nat × String\) :=(.*?)(?=\n\ndef |\n/-)",
                      src, re.S)
        if m:
            names |= set(re.findall(r"OP_([A-Z0-9_]+)", m.group(1)))
    return names


def main() -> int:
    design = design_opcodes()
    covered = matrix_opcodes()
    missing = sorted(n for n in design
                     if n not in covered and n not in EXCLUDED)
    stale_excl = sorted(n for n in EXCLUDED if n not in design)

    print(f"opcode coverage: {len(design)} defined, {len(covered)} in the "
          f"generated matrix, {len(EXCLUDED)} explicitly excluded")

    if stale_excl:
        print("\n  exclusions naming opcodes the design no longer defines:")
        for n in stale_excl:
            print(f"    OP_{n}")

    if missing:
        print(f"\n  NOT COVERED — {len(missing)} opcode(s) are neither in the "
              f"generated matrix nor excluded:")
        for n in missing:
            print(f"    OP_{n}  (0x{design[n]:02x})")
        print("\n  Add them to the matrix, or to EXCLUDED with the test that")
        print("  covers them instead. An opcode nothing executes is an opcode")
        print("  no renumbering can be trusted through: that is exactly how")
        print("  `liu` reached silicon and panicked the guest.")
        return 1

    if stale_excl:
        return 1
    print("check_opcode_coverage: ok — every defined opcode is executed or "
          "explicitly excluded")
    return 0


if __name__ == "__main__":
    sys.exit(main())
