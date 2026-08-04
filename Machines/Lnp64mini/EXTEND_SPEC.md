# LNP64mini architectural extensions

The current mini core includes bounded versions of several LNP64 mechanisms:

- a preemption quantum;
- protection-domain state;
- fail-stop/poison plumbing;
- a park/wake directory;
- gate operations;
- cross-domain capability transfer; and
- VMA/TLB translation machinery.

These features are implemented in the current `Core.lean`, `Iss.lean`, SoC
composition, assembler/opcode agreement checks, and board artifacts. They are
not a complete implementation of every LNP64 profile.

## Required agreement

The hardware and emulator/toolchain must use the same opcode set and state
transition contract. `scripts/check_isa_agreement.py` is the maintained
shared-opcode check. Core selftests and the zero-trap gate catch unsupported or
misdecoded instructions before board claims are accepted.

Each extension must also preserve:

- Design/FastEval agreement;
- the ISS trace comparison;
- emitted-RTL simulation where available;
- explicit memory-target and observability checks; and
- the dual-core boot workload on actual hardware.

Passing a decode check alone is not sufficient.

## Translation boundary

The VMA/TLB implementation is bounded. Translation state, tags, and invalidation
must agree across the hardware, ISS, loader, and DMA conventions. A DMA window
is an explicit physical grant, not an identity-mapping shortcut. External DDR
and the PS interconnect remain outside the Lean core proof.

## Current state

Opcode agreement covers 70 shared opcodes, the emulator zero-trap gate is
green, and silicon reports zero traps. The full board regression is still
failing: network service is down, core 0 halts, and core 1 remains in futex
wait after 20 retires.

Raw console-ring data shows each guest byte write replicated into a 64-bit
word at stride eight, while adjacent 32-bit metadata is correct. Guest C and
clang generate a packed byte store; the Loom design, ISS, and emitted-RTL
simulation all produce the expected single-lane merge on both modeled memory
paths. This localizes the unresolved mismatch to the physical HP AXI write
path or a downstream artifact. The next diagnostic is a tiny known-pattern
write-and-halt program followed by JTAG readback.

Accordingly, the extension set is implemented and source-level checks are
useful, but the present combined hardware head is not release- or demo-ready.
The immediate task is to isolate the board regression, not to add another
extension. See `STATUS.md` and `NEXTSTEPS.md`.

## Out of scope

The mini target does not currently promise the FP or vector profiles, the
full Mover/DMA architecture, state-stream round trips, an unbounded capability
table, or production MMU performance. Those belong in future work only after
the current regression and repository gates are green.

### Correction: byte stores are fine. The "stride 8" was a misreading.

The previous entry claimed the guest's byte writes land somewhere no model
predicts. That is wrong, and the check that settles it is reading the same
address through both masters — the PS DAP (`mrd`) and the mini's own HP master
(regs 40/43/45/46, the path `test/ddr_st.tcl` uses):

```
MINI-VIEW  0x13000008 = 0x202020202020204E
DAP-VIEW   13000008:   2020204E   13000010:   6C6C6C20
```

They agree exactly, so there is no address-mapping difference between masters.
And the word itself is a **correct merge**, not a smear: byte 0 is `0x4E` (`N`)
and bytes 1–7 are `0x20` (space) — `N` stored at offset 0, then spaces merged
into lanes 1–7, each leaving the others alone. Precisely what `st_merge`
specifies and what `subwordselftest` and iverilog predict.

What misled me was rendering before decoding. Runs of eight identical bytes in
a console buffer look like replication, and I read them as a hardware fault
through three board cycles of increasingly elaborate destriding, when the
memory was simply holding the characters the guest actually wrote.

**So the ring content is real.** The guest is printing runs of repeated
characters — `N`, eight spaces, eight `l`, eight `d`, eight `e` — 420 000 of
them, where the same image off-hardware prints 131. That is now a *software*
question about what the guest is emitting, not a hardware one, and the
hardware side of the ladder is fully closed:

* every layer EDSL → ISS → iverilog agrees byte-exact on sub-word stores;
* both bus masters agree on DDR contents;
* guest reads of host-written DDR work (115 M instructions, `traps=0`).

`subwordselftest` stays — the coverage gap it closed was real, `sb`/`sh` had
never been executed below silicon, and it is what made this correction cheap.
