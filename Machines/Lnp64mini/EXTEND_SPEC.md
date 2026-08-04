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
green, and the silicon trap count has been reduced to zero. The full board
regression is still failing: network service is down, core 0 halts, and core 1
remains in futex wait after 20 retires in the current diagnostic trace.

Console-ring data shows byte-store smearing even though neighboring 32-bit
metadata is intact. The compiled `subwordselftest` produces the exact expected
lane merge on both on-chip and DDR paths with zero EDSL/ISS mismatches. The
current source models therefore do not reproduce the board symptom; fresh
executable, RTL, bitstream, and downstream-path validation is required.

Accordingly, the extension set is implemented and source-level checks are
useful, but the present combined hardware head is not release- or demo-ready.
The immediate task is to isolate the board regression, not to add another
extension. See `STATUS.md` and `NEXTSTEPS.md`.

## Out of scope

The mini target does not currently promise the FP or vector profiles, the
full Mover/DMA architecture, state-stream round trips, an unbounded capability
table, or production MMU performance. Those belong in future work only after
the current regression and repository gates are green.

### Reading the guest's own console, and what it ruled out

The board now dumps the in-guest console rings at `LOOPEND`, inside the
servicer session (`test/lnp64_rump_run_dual.tcl`). Three things had to be right
before a single byte was readable, and each was wrong first:

* a **fresh `xsdb connect` leaves the DDR controller in reset** — the dump has
  to run in the session that already has DDR up, not a separate one;
* the servicer drives the **PL over BSCAN**, so `mrd` needs the A9 DAP selected
  first, the same selection `fastload.tcl` makes;
* **guest physical is not PS physical.** The guest DDR window is based at
  `0x10000000`, so the ring at guest `0x3000000` is PS `0x13000000`. Reading the
  guest address returns unrelated DDR and looks exactly like "the guest never
  printed a thing" — which is how it was first misread.

**What the ring says.** Core 0's ring has a valid magic and
**`wptr = 420 305`**. The same image, off-hardware, prints **131** bytes. The
guest is emitting roughly three thousand times its normal output and the ring
has wrapped six times, which is why it reads as noise from the start. Core 1
has no ring at all — consistent with it never leaving `__lnp_futex_wait`.

**A theory the ladder killed.** The raw dump looked like every character was
smeared across eight bytes while the 32-bit `magic` and `wptr` in the same
struct read back perfectly — a textbook broken byte-store. It is not. `sb` and
`sh` had **no coverage anywhere in this harness** (only `sd` 0x33 and `sw` 0x34
were ever encoded), so the new `subwordselftest` was written to check exactly
that, on both memory paths, since `ea < 0x1000` (on-chip `dmem`) and
`ea >= 0x1000` (the DDR read-modify-write) are different hardware:

```
OK   SUBWORD dmem  word=0x1122bbcc5566aa88 lbu=0xaa  EDSL≡ISS mismatches=0
OK   SUBWORD DDR   word=0x1122bbcc5566aa88 lbu=0xaa  EDSL≡ISS mismatches=0
iverilog r8=0x1122bbcc5566aa88 r9=0xaa
```

EDSL ≡ ISS ≡ iverilog, byte-exact, and `ddrEaRaw` word-aligns
(`DATA_BASE + (ea & ~7)`) as it should. **Sub-word stores are not the bug.**
The coverage gap was real and is now closed, but the theory it was built to
confirm is dead — recorded here so it is not re-derived from the same dump.

**What is actually established.** The guest boots, runs 115 M instructions at
`traps=0`, prints ~420 000 characters, and halts; core 1 is never released.
Off-hardware the identical image prints 131 characters and passes. The next
question is what the guest is saying 420 000 times, and the way to get it is to
read the ring **in `wptr` order from the write head** with the layout confirmed
rather than assumed — dump raw hex around `wptr % 0x10000` and derive the
stride from the bytes instead of guessing it, which cost three board cycles
here.

**Also fixed:** `check_stale.sh` ran `lake build`, which in this project builds
the library and *stops* — then section 5 ran a `minitest` binary that could
predate the sources it had just verified. It did: a newly added selftest fell
through the arg match into the emit fallback because the running binary still
had the previous dispatch. The gate now names the executables explicitly.

### The boundary is now sharp: everything below silicon is verified correct

Reading raw hex at three addresses instead of guessing a stride settles the
layout. Character *k* occupies bytes `[8k+1 … 8k+8]` of the ring — **stride 8,
one character per 64-bit word**, with the byte replicated across the word:

```
13000008:  2020204E   -> 'N'
1300000C:  20202020      ' ' x8   (bytes 1..8)
13000010:  6C6C6C20      'l' x8   (bytes 9..16)
13000014:  6C6C6C6C
13000018:  6464646C      'd' x8   (bytes 17..24)
```

Every layer beneath the silicon says this should not happen:

| layer | says |
|---|---|
| guest C | `buf[i] = c` on a `volatile unsigned char *` — packed |
| clang | `zext.w r3,r3; add r2,r2,r3; sb r4,0(r2)` — unscaled index, real `sb` |
| Loom design | `ddrEaRaw = DATA_BASE + (ea & ~7)`, `st_merge` overlays one lane |
| ISS + EDSL | `subwordselftest`: `0x1122bbcc5566aa88`, both memory paths |
| iverilog | `r8=0x1122bbcc5566aa88 r9=0xaa` — byte-exact |

And in the same struct, on the same path, the 32-bit `magic` and `wptr` at
`base+0` and `base+4` land **correctly** — they read back as `0xC0FFEE01` and a
plausible count. So sub-word stores into the first word are right while byte
stores into the buffer are strided, which no layer above silicon predicts.

That is the whole remaining question, and it is now well-posed: **guest reads of
host-written DDR are fine** (the image executes, 115 M instructions, `traps=0`)
and **32-bit guest writes are fine**; it is the guest's *byte* writes whose
placement on the HP AXI path does not match what every model says. The next
move is to instrument that path directly — a tiny guest program that writes a
known byte pattern to a known DDR address and halts, then read it over JTAG —
rather than inferring from a 420 000-character console ring that has wrapped.

Do not re-derive the byte-store theory from this dump: `subwordselftest` exists
precisely so that question stays answered.
