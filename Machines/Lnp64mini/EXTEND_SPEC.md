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

### And the console idiom itself is correct on silicon

`fpga/zc702/probes/conprobe.tcl` runs `lnp64_con_put`'s exact sequence — 32-bit
load of the write pointer, byte store into the buffer, 32-bit store of the
incremented pointer — sixteen times, in twelve instructions, with no NetBSD
around it:

```
PROBE: status=0xa halted=1 retire=117
0x13200004 = 0x00000010                    wptr = 16
0x13200008 = 0x4847464544434241            'A'..'H'  packed
0x13200010 = 0x504F4E4D4C4B4A49            'I'..'P'  packed
```

Sixteen characters, packed, in order, with the write pointer landing at 16.
The idiom is not the problem either.

**Where that leaves it.** The hardware has now been exonerated twice by direct
measurement on silicon, not by inference: byte stores land in their lanes
(`bsprobe`), and the guest's own load/store/increment loop produces packed
output (`conprobe`). So the console ring's eight-fold repetition **is what the
guest actually wrote** — 420 000 characters of it, against 131 for the
byte-identical image off-hardware.

The remaining question is therefore entirely about *execution*: the guest takes
a different path on the mini than in the emulator, early enough to change how
much it prints and to halt core 0 at ~115 M retires instead of running to
644 M. Two independent symptoms now point at the same missing tool — a
differential test between the emulator and the ISS. The gate-call divergence
showed numeric opcode agreement does not imply behavioural agreement; this
shows it again from the other end.

`step-op` already provides a single-instruction interface into the emulator,
but only for the eleven-opcode trap tail (`div udiv srem urem mulh mulhu clz
ctz popcnt rol ror`). Widening it to the mini's full implemented set, and
driving the ISS with the same vectors, is the concrete next build — and both
probes here are the pattern for confirming any candidate on silicon in one
board cycle.

### The differential found six broken opcodes in the ISS on its first run

`scripts/diff_emulator_iss.py` drives one instruction through both the mini's
ISS (`minitest stepop`) and the emulator (`lnp64 step-op`) with the same 32
register values and diffs the registers each writes. 180 vectors over 30 ALU
opcodes, values drawn from boundary cases plus random noise.

**12 mismatches, in `SLTU` and `NOT` — the ISS wrote no register at all.**
Tracing them out gave six broken opcodes, all in `Machines/Lnp64mini/Iss.lean`:

| opcode | what the ISS did |
|---|---|
| `not` (`0x1f`) | missing from `is_alu` → no destination write |
| `sltu` (`0x26`) | in **`is_branch`** → branched instead of computing |
| `bgeu` (`0x68`) | absent from `is_branch` → trapped as an unknown opcode |
| `srli` (`0x4d`), `srai` (`0x4e`), `sltiu` (`0x51`) | not in `is_alu`; the stale raw bytes `0xa5`, `0xa6`, `0x1e` were still there instead |

`is_alu` had literal `0x1c`, `0xa5`, `0xa6`, `0x1e` left over from the
td-anchored map. `is_branch` had replaced the range `0x21 ≤ o ≤ 0x26` with a
membership list — the right idea, W1.5d — but captured `OP_SLTU` as its sixth
member because `0x26` *was* `BGEU` before the renumbering moved `SLTU` onto it.
The comment warning that "an opcode's number must not carry semantic grouping"
sits directly above the line that got it wrong, in the same edit.

**`Core.lean` was correct throughout.** The EDSL's `is_alu` and `is_branch`
both name the right opcodes, so the *design* — and therefore the RTL and the
bitstream — never had this defect. **It was the hand-written mirror, i.e. the
oracle, that was wrong.** So this does not explain the board hang, and it is not
being claimed as the fix; what it does mean is that every EDSL≡ISS result over
those six opcodes was meaningless, because both legs of the ladder were being
compared while one of them mis-decoded.

**Why nothing caught it:** no selftest program executed any of the six. The
whole ladder stayed green over a broken oracle — the same shape as EXT-2's
`tdom` and EXT-7's TLB, but in decode rather than in state.

`alugapselftest` now executes all six and checks every value, and it was
confirmed to **fail** on the pre-fix ISS (114 EDSL≡ISS mismatches, with
`trapped_op: edsl=0 iss=104` — the ISS trapping on `0x68` while the EDSL
executed it). The differential is wired into `check_stale.sh` as section 6, so
a behavioural divergence now fails the gate the way a numeric one already does.

### The demo is back. The board bug was `lw`/`lb` not sign-extending.

```
PASS 20260804-230158
core1_entry=0x00000000008ca300
10 packets transmitted, 10 received, 0% packet loss
core$ NetBSD lnp64mini3 (rump) on ZC702 PL fabric
== PASS: NetBSD serving native GEM0, dual-core, BSCAN quiet ==
```

Against the last known-good run (08-03 21:27), to the instruction:

| | known-good | now |
|---|---|---|
| `core0` retire | 30 136 595 | 30 219 007 |
| `core1` retire | 1 717 838 | 1 749 469 |
| `halted` | 0 | 0 |
| console | — | 132 bytes: `IHLFUTX`, `RUMP_SHMIF_ON_CORE_OK` |
| traps | 0 | 0 |

Core 1 runs 1.75 M instructions in the shared kernel, so **dual-core NetBSD is
back**, not a single-core fallback.

**The cause.** `Core.lean`'s `ld_wb` chose a load's extension with raw hex, and
two arms were stale: `0x05` and `0x08` were `lw` and `lb` under the td-anchored
map, and after the renumbering those ops live at `0x70` and `0x72`. Both fell
through to the default and returned the **raw 64-bit word instead of
sign-extending**. The guest image contains ~4 180 `lw` and ~599 `lb`
instructions; every one of them produced a wrong value on silicon.

That is why the guest diverged on the board and not in the emulator — the
emulator's semantics were correct all along — why it emitted ~420 000 console
characters instead of 131, and why core 0 halted at ~115 M retires.

**How it was finally found.** Not by staring at the board. The generated
EDSL≡ISS matrix was extended from ALU opcodes to loads, stores and branches,
and failed on its first run:

```
FAIL lb @0x40:   rf[4] edsl=255 iss=18446744073709551615
FAIL lb @0x2000: same
```

Store 255, load it as a signed byte: the answer is −1, and the design said 255.

**What this episode actually cost, and what to keep.** Several days went to
theories that measurement later killed — EXT-7 stage B, timing margin, the
servicer binary, a byte-store placement fault, a dual-core deadlock that turned
out to be a truncated emulator run. Every one of those was reasoning from a
symptom. The bug was found in thirteen seconds by a test that enumerates
opcodes instead of guessing which one is interesting, and the same mechanism
had already found six mis-decoded opcodes in the ISS an hour earlier.

The rule this pays for: **when an opcode numbering changes, the thing that
finds the fallout is exhaustive generated coverage, not a hand-written program
and not a hypothesis about the failure.** Raw opcode literals are the specific
hazard — `is_alu`, `is_branch` and `ld_wb` each held stale ones, in two
different files, and only `ld_wb`'s reached silicon.

### EXT-7 stage B passes on silicon

```
PASS 20260804-234424
10 packets transmitted, 10 received, 0% packet loss
== PASS: NetBSD serving native GEM0, dual-core, BSCAN quiet ==

LOOPEND halted=0 traps=0 traps1=0
RETIRE core0=30057049 core1=1724641   console: 132 bytes, IHLFUTX ... ON_CORE_OK
SLICE_LUTX 54309/106400 (51%)   sysclk 27.36 MHz routed
```

The VMA-range TLB is on the board, under a live dual-core NetBSD, with core 1
running 1.72 M instructions in the shared kernel and the boot at `traps=0`.

**Stage B was innocent the whole time.** It was reverted on 08-04 for breaking
the boot; the actual cause was `ld_wb`'s stale `0x05`/`0x08`, which made every
signed byte and word load return an unextended raw word. That bug was present
with or without stage B — which is precisely why the stage-A "restore" failed
identically, the observation that should have exonerated stage B immediately
and instead was read as "the board is broken generally."

The measured numbers that were used to convict it were fine all along: 51 %
LUTs against a ~55 % practical ceiling, and 27.36 MHz routed against a 25 MHz
board clock — the same margin as the stage-A build that passes.

**What the re-land had to fix, and what caught it.** Stage B moves the TLB from
memories to per-index *registers* (D20: every entry is read at once, so it is a
register file). The derived comparator reads registers through `issRegs`, and
the 40 TLB registers were only in `cmpStates`' hand-written loop — so they
would have been invisible to the generated matrix. `coverageselftest` is what
surfaces that; the count went 152 → **192 registers**, all compared or
explicitly exempt.

That is the machinery earning its keep on the first increment after it was
built: new state arrived, and the gate demanded it be compared instead of
quietly not being.

### Stage B's software half: NetBSD runs with `mmu_en = 1`

```
MMU: identity VMA installed on core 0 (base 0, limit 0xFFFFFFFF, cell 1); mmu_en=1
MMU: identity VMA installed on core 1 after reset; mmu_en=1
LOOPEND halted=0 traps=0 traps1=0
RETIRE core0=30138194 core1=1717177
PASS 20260805-000526 — 10/10 ping, dual-core, BSCAN quiet
```

**Dual-core NetBSD now runs with translation in the path.** Every DDR access
goes through the TLB, is checked against the running domain, and is revocable
by bumping the VMA's epoch cell (`cmd 67`). Core 1 retires 1.72 M instructions
in the shared kernel — the same figure as the MMU-off run, so translation costs
nothing observable here.

**Say precisely what this is.** The VMA is the *identity*: base 0, limit
`0xFFFFFFFF`, delta 0. Nothing is relocated. What changed is that translation
is **in the path at all** — previously `mmu_en` was 0 and `ddrEa` took the raw
branch. Non-identity placement (the loader putting guest regions at separate
physical bases) is the next step and is not done. Calling this "the guest under
real translation" is fair; calling it "the guest relocated" would not be.

**Checked in the ladder first.** `ddrEaRaw` word-aligns (`ea & ~7`) and
`ddrEaXlat` does not (`DATA_BASE + eaLo + delta`), so it was not obvious that an
identity VMA computes what bypass computes. `mmuidentityselftest` proves it
does, at several alignments and across byte/half/word/doubleword accesses —
seconds in the ladder instead of a six-minute board cycle guessing.

**One ordering bug, and it is worth recording.** Installing core 1's VMA with
core 0's left core 1 with `mmu_en = 1` and *no valid entry*: `wr [c1 13] 1`
resets core 1, and cmd 13's reset zeroes `tlb_vld`. Every core-1 access then
failed closed, and it retired 20 instructions and parked — while the demo still
PASSed, because the GEM pump runs on core 0. A green ping is not evidence that
both cores are alive; the retire counters are. The install now happens after
the reset, and core 1 is back to 1.72 M.

Note the fail-closed behaviour is exactly right: a core with the MMU on and no
mapping got nothing, rather than getting the raw address. That is the property
working, observed by accident.

### The authority-complete demo

The mechanisms exercised **together**, on silicon, against a guest that was
serving traffic — not each proven separately in its own selftest.

```
1. baseline                    retire 148094479 -> 148566996  (delta 472517)  ADVANCING
   installed VMA#1: base 0x100000 limit 0x200000 dom 3 cell 2
2. after installing dom-3 VMA  retire 148629997 -> 149104238  (delta 474241)  ADVANCING
   bumped epoch cell 2 (revokes VMA#1 only)
3. after revoking cell 2       retire 149128463 -> 149600882  (delta 472419)  ADVANCING
   bumped epoch cell 1 (revokes the GUEST's mapping)
4. after revoking cell 1       retire 149613504 -> 149613504  (delta 0)       STOPPED

AUTHORITY_DEMO_OK
```

Four properties, each measured rather than asserted:

* **domain isolation** — a VMA installed in domain 3 does not perturb a guest
  running in domain 0. `tlbMatch` requires `dom == domCur`, and the retire rate
  is unchanged across the install (472 517 → 474 241 per 700 ms).
* **scoped revocation** — bumping epoch cell 2 destroys that VMA and *only*
  that VMA. The guest, mapped on cell 1, keeps running at the same rate. This
  is the property that makes revocation usable: it is addressed to a cell, not
  to the machine.
* **fail-closed** — bumping cell 1, the guest's own cell, stops it dead.
  `delta 0`, from a core that had been retiring ~470 k instructions per 700 ms.
* **translation is load-bearing** — which is the point of the previous line. A
  guest that kept running after its mapping was revoked would prove the MMU was
  decorative. This one cannot run without it.

Step 4 is destructive on purpose and the script says so; the next `netbsd_up`
rebuilds the world. `fpga/zc702/probes/authority_demo.tcl`.

**What it does not cover.** Capability transfer (`cap_send`/`cap_recv`) and gate
calls are *guest instructions*, so the host cannot drive them over BSCAN — they
are covered by `capxferselftest` and `gateselftest` in the ladder, and by the
generated matrix, but not by this on-silicon demo. Saying "authority-complete"
of the revocation and domain story is fair; of the whole §9/§10.2 surface it
would not be.

### Making the VMA non-identity: the design, and the constraint that shapes it

The identity VMA proves translation is *in the path* and revocable, and that is
worth having, but it does not relocate anything — so it does not exercise the
part of §15 that matters most. Making it real turns on one fact that is easy to
miss:

```lean
def ddrPc : Expr 32 := .add (.lit (BitVec.ofNat 32 DATA_BASE)) (.slice pc 0 32)
```

**Instruction fetch is not translated.** `ddrPc` bypasses the TLB entirely;
only `ddrEa` (data) goes through it. So the guest's *text* cannot be relocated
by a VMA — move it and fetches follow the old address. Any non-identity plan has
to leave text where the loader put it.

That is not a defect to fix casually: translating fetch means the TLB is in the
fetch critical path, which is exactly the timing the area/Fmax budget has been
protecting. Data-only translation is a legitimate design point and should be
recorded as a choice, not discovered again as a surprise.

**The plan that follows from it**, with `priTree` picking the first matching
entry, so lower index wins:

| entry | range | delta | why |
|---|---|---|---|
| 0 | shmif ring `0x20e000–0x30e000` | 0 | the host's `ring_pump` and GEM0 DMA address this **physically**; it must not move. This is the "named DMA-window grant". |
| 1 | text `0x400000–0x8dd000` | 0 | fetch is untranslated, so text must stay put |
| 2 | everything else (data, bss, stack, heap) | `+0x800000` | genuinely relocated: the guest keeps its addresses, the bytes live 8 MB away |

`fastload.tcl` then writes the data image at `DB + dbase + 0x800000` instead of
`DB + dbase`. The delta field is 24-bit (`cmd_data[23:0]`), so the shift must
stay under 16 MB — 8 MB is a comfortable choice.

The demo this buys is the right one: **the guest's data really is somewhere
else, the DMA window really is a separate grant with its own bounds, and
revoking either cell fails closed independently.** That is worth doing and is
the next step here; the identity version is the floor, not the goal.

### After the failed renumbering: coverage as an invariant, and the RTL surface

The renumbering passed every gate and panicked on silicon. The defect class was
not "an opcode moved wrongly" — it was **the list was incomplete**, and
hand-appending the missing entries would reproduce the hazard for the next
opcode added. Three things changed.

**1. Coverage is checked against the design's own table.**
`scripts/check_opcode_coverage.py` reads `Core.lean`'s `OP_` constants and
requires every one to be executed by the generated matrix or to appear on an
explicit exclusion list with the test that covers it instead. On its first run
it found **five** uncovered opcodes — `liu`, `auipc`, `jmp`, `jal`, `jalr`. Two
were the suspects; the whole jump family had not occurred to me. A new opcode
with no coverage and no stated exclusion is now a red gate.

**2. `liu`/`auipc` get a directed battery, not just a matrix entry.**
A single-instruction diff can agree on one `liu` and still get the hi/lo
assembly or the sign extension of the `ori` half wrong — which is exactly the
shape of a `-1` appearing where a CPU count belongs. `constBattery`
materialises eight exact 64-bit values (zero, one, all-ones, both sign
boundaries, high-bit patterns) and checks the value that comes out.

**3. The RTL leg — the surface that actually failed.**
`opDiffSelftest` compares EDSL against ISS; `diff_emulator_iss.py` compares
emulator against ISS. Both were green and the board still panicked, because
**nothing compared against the RTL**, which is what the bitstream is built from
and what silicon runs. An infinitely thorough emulator-vs-ISS matrix could not
have caught it.

`minitest opdiffhex` writes all 359 generated programs to `fpga/zc702/opdiff/`,
and `scripts/opdiff_rtl.sh` runs each through iverilog on the emitted SoC:

```
opdiff_rtl: simulated 359 program(s) on rtl/lnp64mini_soc.v
opdiff_rtl: OK
```

It earned its place immediately: on the first run it trapped at `op=a0` on the
first instruction, because `rtl/lnp64mini_soc.v` was still the *renumbered*
emit — a stale artifact that sections 1–3 had not caught because the revert
touched the sources and not that file.

**4. A standing literal lint.** `scripts/check_opcode_literals.py` scans for hex
literals matching any opcode value in opcode-bearing contexts, and requires each
to be generated or annotated as intentionally raw (as the four `.quad` sites now
are). It also takes `--old-map` to scan for leftovers of a previous numbering
after a renumber.

Both new checks are wired into `check_stale.sh` as section 7.

**What is still missing before the next attempt:** an on-hardware ISA smoke that
runs *before* any kernel boot, and a last-N-committed-instructions ring buffer
readable after a panic. 41 550 instructions into a rump boot is the most
expensive possible place to first learn about a decode disagreement, and the
panic string is a very thin clue compared with a trace.
