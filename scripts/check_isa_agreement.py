#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# Cross-repo opcode agreement: lnp64mini (Core.lean) vs the assembler
# (lnp64/src/main.rs) vs the LLVM backend (LNP64InstrInfo.td).
#
# This exists because of the 2026-08-04 outage. `lnp64` and `lean_hw` are
# separate repositories holding two halves of one ISA. A revert applied to one
# and a reapply applied to the other left BOTH repos internally consistent --
# every selftest green, `check_stale.sh` green -- and the board bricked: core 1
# retrapped forever on `op=cb`, the old FUTEX_WAIT, because the mini had moved
# to 0x99 and nothing else had. No single-repo check can see that, by
# construction. This one compares across the split.
#
# Mnemonic-mapped, never regex-paired against a table: pairing a byte column
# with a name column has produced three wrong conclusions on this project.

import json
import os
import pathlib
import re
import sys

HW = pathlib.Path(__file__).resolve().parent.parent
LNP64 = pathlib.Path(os.environ.get("LNP64_ROOT", HW.parent / "lnp64"))

CORE = HW / "Machines/Lnp64mini/Core.lean"
ASM = LNP64 / "src/main.rs"
TD = LNP64 / "llvm/lib/Target/LNP64/LNP64InstrInfo.td"

# mini's OP_ name -> the name the assembler's disassembler table uses.
# Only opcodes all three implement are compared; mini-local ops (loads, stores,
# selects, fences, the gate/capability block) have no counterpart and are
# listed in `MINI_LOCAL` so that adding one does not silently skip the check.
MINI_LOCAL = {
    "NOP", "MOV", "INVALID", "SLEEP", "EXIT",
    "THREAD_EXIT", "SEL", "SEL_41", "SEL_42", "SEL_43", "SEL_44", "SEL_45",
    "CLONE_SPAWN", "LR_D_ACQ_REL", "SC_D_ACQ_REL", "FENCE_D1", "FENCE_D2",
    "FENCE_D3", "FENCE_D4", "MINI_GATE_CALL", "MINI_GATE_RETURN",
    "MINI_CAP_SEND", "MINI_CAP_RECV",
}

# mini OP_ name -> LLVM backend `def` name, where they differ.
TD_ALIAS = {"LSL": "SLL", "LSR": "SRL", "ASR": "SRA",
            "LSLI": "SLLI", "LSRI": "SRLI", "ASRI": "SRAI",
            # Loads and stores. These were wrongly declared MINI_LOCAL at first,
            # which is exactly how the lw/lb split reached silicon: the mini
            # implements sign-extended loads at 0x70/0x09/0x72 while the backend
            # emitted 0x05/0x09/0x08, so every byte and word load in the guest
            # trapped to the JTAG servicer. The known-good boot ran with
            # traps=0; the mismatched one was still grinding at 12 832.
            "LD": "LD", "LD_31": "LWU", "LD_32": "LBU", "LD_36": "LHU",
            "LD_S_70": "LW", "LD_S": "LH", "LD_S_72": "LB",
            "ST": "SD", "ST_34": "SW", "ST_35": "SB", "ST_37": "SH"}

# Mini opcode -> assembler disassembler-table name, where they differ.
ASM_ALIAS = {"LD_S_70": "LD_W_S", "LD_S": "LD_H_S", "LD_S_72": "LD_B_S"}


def mini_ops():
    src = CORE.read_text()
    return {m.group(1): int(m.group(2), 16)
            for m in re.finditer(r"^def OP_([A-Z0-9_]+) : Nat := (0x[0-9a-f]+)",
                                 src, re.M)}


def asm_ops():
    """The disassembler table `0xNN => "NAME"` is the assembler's name<->byte map."""
    src = ASM.read_text()
    out = {}
    for m in re.finditer(r'(0x[0-9a-f]{2}) => "([A-Z0-9_]+)"', src):
        out.setdefault(m.group(2), int(m.group(1), 16))
    return out


def td_ops():
    src = TD.read_text()
    return {m.group(1): int(m.group(2), 16)
            for m in re.finditer(r"^def ([A-Z0-9_]+) :.*let Opcode = (0x[0-9a-f]+)",
                                 src, re.M)}


def main():
    missing = [p for p in (CORE, ASM, TD) if not p.exists()]
    if missing:
        print(f"check_isa_agreement: SKIP (not found: "
              f"{', '.join(str(p) for p in missing)})")
        return 0

    mini, asm, td = mini_ops(), asm_ops(), td_ops()
    fail = []

    # The authored backend (TD, above) is the single source of truth and is
    # git-tracked. `target/llvm-project-src/...` is NOT a rival source: it is a
    # git-ignored build checkout that run_real_llvm_lnp64.sh regenerates by
    # `cp -a` from the authored tree before every build. This check verifies
    # that derived checkout is SYNCHRONIZED with the authored tree — i.e. that
    # a rebuild has happened since the authored source last changed. If it is
    # stale, the authored edit is real but the compiled clang still reflects the
    # old source (the 2026-08-04 symptom); the fix is to rebuild, which re-syncs.
    build_td = (LNP64 / "target/llvm-project-src/llvm/lib/Target/LNP64"
                / "LNP64InstrInfo.td")
    if build_td.exists() and build_td.read_text() != TD.read_text():
        fail.append(f"authored {TD} and build checkout {build_td} differ — the "
                    f"checkout is stale; rebuild (run_real_llvm_lnp64.sh) to "
                    f"re-sync it from the authoritative authored tree")

    for name, byte in sorted(mini.items()):
        if name in MINI_LOCAL:
            continue
        aname = ASM_ALIAS.get(name, name)
        if aname in asm and asm[aname] != byte:
            fail.append(f"{name}: mini=0x{byte:02x} assembler({aname})=0x{asm[aname]:02x}")
        tname = TD_ALIAS.get(name, name)
        if tname in td and td[tname] != byte:
            fail.append(f"{name}: mini=0x{byte:02x} backend({tname})=0x{td[tname]:02x}")

    unknown = sorted(n for n in mini if n not in MINI_LOCAL
                     and ASM_ALIAS.get(n, n) not in asm
                     and TD_ALIAS.get(n, n) not in td)
    if unknown:
        fail.append("mini opcodes in neither the assembler nor the backend, and "
                    "not declared MINI_LOCAL: " + " ".join(unknown))

    if fail:
        print("check_isa_agreement: FAILED — the two repos disagree on the ISA")
        for f in fail:
            print("  " + f)
        print("\nA disagreement here bricks the board even though every "
              "single-repo check is green: the guest image is compiled by the "
              "backend and executed by the mini.")
        return 1

    n = len([x for x in mini if x not in MINI_LOCAL])
    print(f"check_isa_agreement: ok — {n} shared opcodes agree across "
          f"mini, assembler and LLVM backend")
    return 0


if __name__ == "__main__":
    sys.exit(main())
