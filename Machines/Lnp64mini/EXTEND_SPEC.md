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

### The demo blocker, reproduced off-hardware

The board failure now reproduces in the emulator in about seven minutes, with
the guest's console readable, instead of a six-minute board cycle that shows
almost nothing. That is the main result of this pass.

**The recipe.** The zero-trap gate never sets `LNP64_SMP_CORES`, so core 1
never runs off-hardware and the gate passes on a configuration the board does
not have. Adding it reproduces the board exactly:

```
LNP64_BOARD_DDR=1 LNP64_CON_RING_DUMP=1 LNP64_SMP_CORES=2 \
LNP64_SMP_CORE1_ENTRY=$(awk '$NF=="lnp64_core1_entry"{print "0x"$1}' $ELF.map) \
LNP64_SMP_GATE=$(awk '$NF=="lnp64_smp"{print "0x"$1}' $ELF.map) \
LNP64_MAX_SECONDS=420 lnp64 run-elf --namespace-root /tmp/x $ELF
```

Result: console `IHLF`, `core1=20`, core 0 spinning — the board's signature
(`core1=20`, `status0=0xa`) to the instruction.

**Where it stops.** The markers are single characters from
`userland/rump_shmif_telnet_probe.c`: `I` rump kernel up, `H` shmif0 created,
`L` lwp forked, `F` address assigned, `U` interface up, `T` listener bound.
Stopping after `F` means the hang is inside
`rump___sysimpl_ioctl(cfg, R_SIOCSIFFLAGS, &ifr)` — bringing `shmif0` up.

**Ruled out, each by experiment rather than argument.**

* *The release ordering.* Core 1 is released by `lnp64_smp_release_core1()`,
  and its position was the obvious suspect. Three placements were built and
  run: after the NIC is up (original — stops at `F`), immediately after
  `rump_init()` (stops at `H`, both cores burning ~310 M instructions in a
  livelock over process 1's lwp state), and after `lwproc_rfork` (stops before
  `F`). Every placement stalls at the next kernel call. The ordering is not the
  variable.
* *The vCPU count.* `LNP64_RUMP_NCPU` is **independent of `LNP64_SMP`** and
  defaults to `1`, so every image built here — and the silicon-proven one — has
  a single rump vCPU. Building with `LNP64_RUMP_NCPU=2` changes nothing:
  still `IHLF`, still `core1=20`.

**What is left.** The stall needs core 1 to *exist and be parked*: the
identical image with `LNP64_SMP_CORES=1` reaches `RUMP_SHMIF_ON_CORE_OK` and
passes the zero-trap gate. Core 1 parks in `__lnp_futex_wait` on
`lnp64_smp.ready`, and core 0's kernel issues many `FUTEX_WAKE`s — so the
next thing to test is whether a `FUTEX_WAKE` with a cross-core waiter parked
stalls the waker, which would explain why the first kernel operation that
starts a kthread is where core 0 dies. That is a question for the mini's own
selftests, not another guest rebuild.

**Also fixed.** `build_rump_shmif_image.py` printed
`SMP: core-1 stub + kernel worker (RUMP_NCPU=2)` on one line and
`rump vCPUs = 1` a few lines below. The first is what got believed. It now says
where the number actually comes from.

### What the guest is actually doing while it "hangs"

`LNP64_STEP_DUMP` on the reproduction gives the shape precisely. The suffix on
each entry is the core (`c0`/`c1`):

```
ready=2  t1,t3..t31 @0x8d4630c0 (c0)   t2 @0x8ca830c1 (c1)   t5, t32 advancing
futex 0x404b020:[14, 1, 19, 16]  ... later  [14, 1, 19, 16, 31]
       0x940240:[2]
```

* **31 rump kthreads are parked at one address** (`0x8d4630c0`, the rumpuser
  condvar wait), all on core 0. Only **two** threads are runnable.
* `t2` on core 1 waits on `0x940240` — `lnp64_smp`, the SMP gate. Expected.
* The waiter list on `0x404b020` **grows** across dumps (`…16]` → `…16, 31]`):
  threads keep arriving at that condvar and nothing ever signals it.
* `t5` advances a few hundred bytes of PC across 80 M steps. That is a spin,
  not progress.

So it is not a hard deadlock and not slowness: it is a condvar with an
ever-growing waiter list and no signaller, with one thread spinning. The
question is which thread is supposed to signal `0x404b020` and why it is not
running — and the fact that `LNP64_SMP_CORES=1` boots the identical image means
the answer involves core 1's presence, not the guest logic alone.

This is where the next session should start, and it now costs seven minutes an
iteration with full thread visibility rather than a blind board cycle.

### Retraction: there is no off-hardware dual-core failure. I truncated the boot.

The two entries above are wrong and are withdrawn.

I ran the reproduction with `LNP64_MAX_SECONDS=200`–`420`. The boot needs about
**1100 s** of emulated time — the figure `run_zero_trap_gate.sh` has used all
along (`secs="${LNP64_ZERO_TRAP_SECONDS:-1100}"`). Every "hang" I recorded was
the run being cut off mid-boot. At the correct budget, with core 1 present:

```
IHLFUTX
RUMP_SHMIF_ON_CORE_OK SHMIF_RING_BASE=0x20e000 SHMIF_RING_SIZE=0x100000
SMP_CORE1_RELEASED
SMP_RETIRE core0=644775110 core1=124224889
```

Core 1 runs 124 M instructions in the shared kernel. **The dual-core guest is
fine off-hardware.** Specifically withdrawn:

* "reproduces the board's signature exactly" — it does not; it reproduced a
  stopwatch;
* "release ordering ruled out by experiment" — the three placements were three
  truncated boots and distinguish nothing. The original ordering (release after
  the NIC is up) stands, and the probe is back to it;
* "vCPU count ruled out" — likewise untested. `LNP64_RUMP_NCPU` really is
  independent of `LNP64_SMP` and really does default to 1, but nothing here
  shows what it does to the boot.

**How this happened, and the guard.** The markers `I H L F U T X` advance over
hundreds of millions of instructions, so a short run always stops part-way
through them and *looks* like a hang at whichever letter it reached — and the
letter moves when you change the budget, which reads as "the fix changed
something". Three different placements produced three different letters and I
took that as signal. It was elapsed time.

A bounded run that does not reach its terminal marker is **inconclusive, not a
failure**, and must be reported as such. The one number that would have caught
this immediately is the retire count: 644 M to reach `RUMP_SHMIF_ON_CORE_OK`
against the 150–300 M my runs were stopping at.

**Where the board investigation actually stands.** Unchanged from before any of
this: on silicon core 0 halts (`status0=0xa`) after ~115 M retires with core 1
parked at 20. The emulator now says that is *not* an inherent dual-core
problem, which is useful — but the board's `halted=1` is a real halt, not a
truncation, and that is still unexplained.

### The byte-store question is still open, and the two-master check did not settle it

Earlier I wrote that byte stores are fine because the PS DAP and the mini's own
HP master return identical words. **That argument is weaker than I claimed.**
Two masters agreeing on what memory *contains* says nothing about whether the
store *placed* the bytes correctly — both read the same memory, correct or not.
What the design-level evidence (`subwordselftest`, iverilog) does establish is
that the RTL merges a byte into its lane; it does not speak for the synthesised
AXI path.

The facts that still need explaining:

* the same image writes **packed** console text in the emulator and
  **one character per 64-bit word** on silicon;
* on silicon the guest emits ~420 000 characters and core 0 halts at ~115 M
  retires, where off-hardware it emits 131 and runs to 644 M.

**A direct probe is the way to settle it, and it is half-built.**
`fpga/zc702/probes/bsprobe.tcl` + `bsprobe_words.txt` load a 22-word program
that seeds one 64-bit word and then stores `'A'..'H'` into its eight byte lanes,
then read the result back through both masters:

```
packed (correct) : 0x13200000 = 0x44434241   0x13200004 = 0x48474645
one-per-word     : the characters land 8 bytes apart
```

It does not run yet, and the reason is recorded so the next attempt does not
rediscover it:

* `loadw` (regs 10/11/12) targets an IMEM this SoC does not fetch from — the
  core runs with `retire=0` and `pc` pinned at `TEXT_BASE`;
* `gwrite` (regs 40/41/42) does not land either: writing `0xCAFEBABE12345678`
  to `0x13200000` reads back unchanged. The rump servicer uses the same helper
  successfully inside `bulk_write`, so the missing piece is that sequencing
  (and probably a strobe), not the helper itself;
* status bit 0 is *running*, bit 1 *halted*, and bit 3 is set throughout —
  its meaning is still unknown and is worth pinning down, since
  `test/ddr_st.tcl` treats it as a stop condition.

Finish the write sequencing and this answers in one board cycle a question that
has now cost several.

### Settled on silicon: byte stores are packed and correct

`fpga/zc702/probes/bsprobe.tcl` now runs, and the answer is unambiguous:

```
PROBE: write-path check = 0xCAFEBABE12345678 (want 0xCAFEBABE12345678)
PROBE: status=0xa halted=1 retire=22 pc=0x10a8
MINI-VIEW  0x13200000 = 0x4847464544434241     bytes 0..7 = A B C D E F G H
MINI-VIEW  0x13200008 = 0xDEADBEEF01020304     neighbour untouched
DAP-VIEW   13200004: 48474645  13200008: 01020304  1320000C: DEADBEEF
```

Eight `sb` instructions into the eight byte lanes of one word land **packed**,
in order, and leave the adjacent word alone. Both masters agree. The core ran
the whole program (`retire=22`, halted at the `EXIT`). This is the silicon
itself, with no NetBSD in the way — the question that cost several board cycles
is closed by measurement rather than inference, and the `subwordselftest`/
iverilog result is confirmed rather than merely assumed to extend.

**What made the probe work.** `gwrite` in `jtag_lib.tcl` is not usable
standalone. `bulk_write` does two things it does not:

* register 40 takes `addr - 8`, because the auto-increment bitstream latches
  the address *post*-increment;
* each word needs an idle dwell, or the HP write is silently dropped.

`bulk_write_v` additionally reads back and re-writes dropped words — its own
comment notes ~30 % of raw loads corrupt without it. A standalone `gwrite`
therefore reads back unchanged and looks exactly like a dead write path. Also:
the program must go to **DDR** via `bulk_write_v`, not through `loadw`
(regs 10/11/12), which targets an IMEM this SoC does not fetch from.

**So the console ring's eight-fold repetition is real guest output.** The
hardware wrote what the guest asked for. Combined with the guest emitting
~420 000 characters on silicon against 131 off-hardware for a byte-identical
image, the remaining question is no longer about memory at all: **some
instruction behaves differently on the mini than in the emulator**, and the
guest diverges onto another path early.

That is exactly what the differential test noted after the gate-call finding
would catch — one program through both the emulator and the ISS with observable
state compared. The gate-call divergence proved numeric opcode agreement does
not imply behavioural agreement; this is the second symptom pointing the same
way, and it is now the highest-value thing to build.
