# Extending lnp64mini toward the architecture — binding plan

Goal: keep the DUAL core, add **Gates, Domains, Park/wake directory,
Preemption tick, Fail-stop/poison, VMA+MMU, Cross-domain capability
transfer**, and **keep the NetBSD telnet demo working** throughout.

Normative source: `/home/ubuntu/lnp64/lnp64_isa.md` (READ-ONLY; spec of
record). Precedents to copy: `Machines/Epoch/EPOCH_SPEC.md` and
`Machines/CapWalk/CAPWALK_SPEC.md` — every addition is a Layer-1 protocol in
Lean, a Layer-2 Loom design, and (where affordable) a Layer-3 refinement.

## The two hard constraints

1. **The demo is the regression bar.** After every increment:
   `scripts/epoch_ladder.sh`, `scripts/capwalk_ladder.sh`, the mini
   testbenches reproducing DUAL_SPEC's numbers, and — before anything is
   called done — NetBSD booting on the board and answering telnet + ping.
   A change that breaks the demo is reverted, not "fixed later".
2. **Fmax is nearly exhausted.** `lnp64mini_cap` post-routes at **25.89 MHz
   against a 25 MHz clock** — under 4 % margin. Anything on the load/store
   path (i.e. the MMU) will eat it. Rule: if post-route Fmax drops below the
   clock, **halve the clock and report the cost**, do not silently break
   timing. Measure Fmax on every increment; a design that fits but does not
   time is not done.

## Budget (measured anchors, yosys LUT cells)

dual+epoch+capwalk = ~30k ≈ **56 % placed**; each engine so far is 330–670
LUT. We are CORE-bound, not engine-bound — but the MMU is the exception
because it touches the datapath, not just a table. Estimates: domains ~1.5k,
gates ~1.5k, park/wake ~1k, preemption ~0.3k, fail-stop ~0.3k, transfer ~1k,
**MMU/TLB ~3k and the only one with Fmax risk**. Target ≤ 85 % placed.

## The MMU and the demo — the guest is TRANSLATED, not faked

Rejected: giving the NetBSD domain an identity VMA so translation is present
but does nothing. That proves the hardware exists and the architecture does
not. It also leaves dark one of §3's eight epoch-cell referents — *cached
translation*, whose cell `map.protect`/`munmap` bumps — because with an
identity map there is nothing to shoot down.

**The guest runs under a real, non-identity mapping.** Consequences, all of
which are work and none of which are optional:

* **Layout.** The rump image is linked flat (text 0x400000, data ~0x8db000,
  stacks 0x1700000–0x2000000, shmif ring 0x20e000, GEM slab 0x2000000, native
  heap 0x4000000+192 MB). Under translation these become *virtual* addresses
  and the loader must place each region at whatever physical frames the
  mapping assigns. `fastload.tcl` and the servicer write PHYSICAL DDR, so the
  page table and the loader must agree; build the table as part of the load,
  not in the guest.
* **Pages must be genuinely non-contiguous** for at least part of the image,
  or the "mapping" is an offset in disguise and we are back to faking it.
* **DMA is the one named physical window.** GEM0 is a bus master: the NIC
  reads descriptors and frames at PHYSICAL addresses, so `gem_core.c`'s
  `PHYS(g) = 0x10000000 + g` cannot survive translation unchanged. This is not
  a cheat if it is *named*: §15 has device windows with IOVA metadata, so the
  DMA region is an explicitly declared mapping the domain was granted, and the
  guest asks for a buffer's physical address instead of computing it. Write it
  down as a grant, never as an assumption.
* **The payoff, and the reason to do it this way:** with real mappings we can
  **revoke one out from under running NetBSD** — bump the VMA's epoch cell,
  the cached translation dies, the next access fails closed — which is §15 and
  §3 meeting on silicon, and is a demo nobody can run today.

**Staging (each stage keeps the demo alive):**
* **A — hardware first.** TLB + walker + VMA tables, MMU bypassed for the
  running guest. Proves the mechanism, risks nothing, gives Fmax data early.
* **B — move the guest in.** Real page table built at load time, image placed
  per the mapping, `gem_core` using the granted DMA window. This is the risky
  stage; it is where the demo can break and where the regression bar bites.
* **C — the payoff.** Shoot down a live mapping under the running guest and
  show the fail-closed, with the latency measured against the D23 bound the
  way the epoch demo already does.

## Build order (dependencies are real; do not reorder casually)

1. **Preemption tick** (Law 5). Smallest, independent, and it closes a known
   fidelity gap (`PORTING_SPEC.md`: the scheduler is cooperative). `S_F0` is
   already the instruction boundary; the sleep scan is already a timebase.
   Risk to the demo: a preempted rump guest must still work — this is the
   first real test of the regression bar.
2. **Domains** — a domain id on the core, per-domain capability/VMA table
   roots, and the tag the datapath compares. Everything below references it.
   The NetBSD guest becomes domain 0 and must not notice.
3. **Fail-stop / poison plumbing** — the architected disposition every later
   engine feeds (§3 poison, Appendix F's fail-stop rule). Small, and cheaper
   to put in before there are four clients than after.
4. **Park/wake directory** (Appendix F #6) — §3 calls it "the epoch machine's
   client annex"; grow it from mini's existing futex + the cross-core
   doorbell rather than building fresh.
5. **Gates** (§9, Law 1) — frame push/pop, the continuation stack, and the
   delivery-targeting rule. The crown jewel and the reason domains matter.
6. **Cross-domain capability transfer** — send/recv/gate re-key; needs
   domains (2) + gates (5) + the existing CapWalk engine.
7. **VMA + MMU** (§15) — last, because it is the Fmax risk and the only item
   that touches the load/store path. Identity for domain 0 per above.

## Per-increment definition of done

Lean protocol + theorems (traced to ISA sentences) · Loom design ·
FastEval selftest · iverilog leg byte-identical to the oracle · byte-identical
re-emit of every design not deliberately changed · `lake exe audit` green ·
**measured Fmax and placed utilisation** · the demo still boots and serves.
Deviations appended here, never silently narrowed.

## Explicitly NOT in scope

FP profile (§14), vector profile (§18), the Mover/DMA (§11), state-stream
round-trip (§16.8), and the full 2^24-slot capability table (the cache+DDR
design stands).

## Toolchain impact — in scope, and load-bearing for the oracle

Targeted edits to `/home/ubuntu/lnp64` ARE in scope for this campaign (the
big lnp64 rewrite is not). They are not garnish: the verification story is
emulator ≡ ISS ≡ iverilog ≡ silicon, and **a feature the emulator does not
model has no oracle** — we would be reduced to comparing the hardware against
itself. So each increment states its toolchain delta and pays it.

| increment | assembler / ISA tables | emulator | guest runtime / loader |
|---|---|---|---|
| preemption | — (no new op) | quantum + forced switch, so traces still match | — |
| domains | domain-id PCR read, if exposed | domain tag on the core model | — |
| fail-stop | poison/fault dispositions surfaced | fault outcome + containment | trap-server op list |
| park/wake | — (grows futex) | directory model replacing ad-hoc futex | — |
| **gates** | **new ops** (`gate_call`/return shape, §9) | frame push/pop + continuation stack | crt/ABI if the guest calls one |
| **cap transfer** | **new ops** (send/recv re-key, §10.2) | install-time transaction | — |
| **VMA/MMU** | **new ops** (`map.protect`, `munmap`, §15) | translation + TLB + shootdown | **`fastload` builds the page table**; `gem_core.c`'s `PHYS()` becomes a granted DMA-window lookup |

Concretely, the files that will move: `src/isa.rs` (opcode tables),
`src/asm.rs` (mnemonics), `src/emulator.rs` (the model — the oracle),
`src/loader.rs` + `scripts/board/*` (page-table construction at load time),
`toolchain/gem_core.c` (DMA addresses via grant, not arithmetic), and the
trap-server's op manifest (each new op partitioned HW-native vs trap-to-host).

**Rule:** an increment that adds an opcode without adding it to the emulator
is not done — it has silently dropped the strongest leg of the ladder. If a
feature genuinely cannot be modelled in the emulator, say so explicitly in
that increment's deviations and state what replaces the oracle for it.

---

# Increment log

## EXT-1 — the preemption tick (Law 5). 2026-08-02

Closes the fidelity gap `PORTING_SPEC.md` records: every write of `cur` was
a voluntary yield, so a spinning thread owned the core forever. Law 5 says
*"Every instruction boundary is a preemption point. Unconditionally. The
machine contains no non-preemptible region."*

### What it is

Two per-core registers and one BSCAN index:

| | | |
|---|---|---|
| `quantum` (32 b, reset 0) | the reload value, in **core cycles** | `Core.lean` |
| `qctr` (32 b, reset 0) | the running thread's remaining quantum | `Core.lean` |
| **cmd 57** (`CMD_QUANTUM`) | writes `quantum` **and** arms `qctr` with the same word | `cmdRule` + `quantumRule` |

`quantum = 0` is **disabled**: `quantumOn` is false, so nothing decrements,
nothing reloads, nothing preempts, and the core is the cooperative machine
of §63 bit for bit. That is the safety valve, the byte-identity story, and
the reason the wrapper and the NetBSD loader need no change at all to keep
today's behaviour.

**Where it fires:** `s_f0`, and nowhere else. `preemptAtF0 = fsmEn ∧
st = S_F0 ∧ ¬bus_req ∧ ¬trap_active ∧ qExpired`. `fsmEn` already excludes
`zeroing`, `hold` and a stopped core; `st = S_F0` excludes every
mid-instruction state including `S_WAIT`, `S_PAUSE` and `S_TRAP`; `S_F0` is
also the state in which no bus transaction is in flight, which is exactly
the argument that makes the D15 `hold` input safe.

**What it saves:** exactly what `YIELD` saves — `tpc[cur]` (through the one
`tpc` write funnel, `tpcTriples` entry 6), then `cur <= next_ready`,
`pc <= tpc[next_ready]`. `st` is not written, so the core stays at `S_F0`
and fetches the new thread's instruction next cycle.

**When nobody else is READY** (`next_ready = cur`) it reloads `qctr` and
issues the fetch in the same cycle: preempting to yourself is a no-op, not
a stall — measured, not asserted (a one-thread program runs in the *same
cycle count* with and without a quantum).

### Deviations

1. **The saved pc is `pc`, not `pc8`.** The instruction to build this
   increment said "`tpc[cur] <= pc8`, as `YIELD` does". At `S_EX` a `YIELD`
   has already consumed the instruction at `pc`, so its resume point is
   `pc+8`. At `S_F0` **nothing has been consumed** — `pc` is the instruction
   about to be fetched — so the resume point is `pc`. Writing `pc8` here
   would silently skip one instruction of the preempted thread per tick,
   i.e. precisely the "guest corrupts silently" failure the instruction
   warned about. The *mechanism* is `YIELD`'s; the datum is the boundary's.
   `preemptAudit` checks this at every fire, and `progSpin`'s poison word
   turns a resume slip into a trap rather than a wrong answer.
2. **The quantum counts cycles, not instructions.** The spec sketched "the
   serialized sleep scan is already a per-cycle timebase"; a cycle counter
   is what that timebase is, it needs no new comparator per thread, and it
   is the quantity a scheduler actually wants to bound (an instruction
   counter would let one 68-cycle divide outlast a hundred ALU ops). It
   ticks only under `hp_core_owns`, so a thread is not charged for cycles
   the core spent parked in `S_WAIT`/`S_PAUSE` or trapped.
3. **`cmd 13` (soft reset) re-arms `qctr := quantum`** so a run never
   inherits a half-spent counter, but it does **not** clear `quantum`: the
   quantum is host configuration and survives a soft reset, like `reg_sel`
   and the JTAG address registers.
4. **No emulator leg.** The toolchain table above asks the Rust emulator to
   model the quantum. This pass was explicitly scoped to leave
   `/home/ubuntu/lnp64` untouched, so that leg is **not** done. It costs
   less than it would for an opcode: preemption adds **no instruction**, so
   every existing emulator trace remains a valid oracle for `quantum = 0`
   (and the six system testbenches confirm the RTL still matches them). For
   `quantum > 0` the oracle is the Lean ISS, and the iverilog leg is diffed
   against it byte for byte. Owed: emulator quantum + forced switch.
5. **Post-route Fmax was NOT measured on this host.** `nextpnr-xilinx` is
   not installed here (it lives on the board host, via the openXC7 snap), so
   only yosys numbers are reported below. **This is an open item against the
   second hard constraint, not a claim that timing is fine** — the board
   host must run `oxc7/build_oxc7.sh` on `lnp64mini_dual_top` /
   `lnp64mini_soc_top` before EXT-1 is called done.
6. **The index is 57, not the "next free" 56.** 56 is the first index the
   *core* does not use, and it was the first choice — but
   `lnp64mini_dual_top.v` and `lnp64mini_epoch_top.v` already own 56 as a
   **wrapper** register (`CORE1_HOLD`) and consume the write before it is
   forwarded to either core. Had that gone unnoticed the quantum would have
   been unreachable on exactly the two bitstreams the demo runs on, and a
   later wrapper that did forward it would have retimed the guest by
   accident. Free-index arithmetic has to be done against the *wrapper*
   decode, not just the core's. 57 is free in every wrapper write decode and
   every readback mux.
7. **The NetBSD acceptance run is not in this pass** (the board is driven by
   the operator). What is owed there: boot with `quantum = 0` (must be
   indistinguishable from §63 — the safety valve), then boot with a quantum
   set and confirm the rump guest still serves telnet + ping.

### Evidence

* `lake env lean --run Machines/Lnp64mini/Emit.lean preemptselftest` — three
  EDSL≡ISS lockstep scripts over **every** register (`quantum`/`qctr`
  included) plus `rf[0..64)`, `dmem[0..64)` and the four thread-table
  memories, and five architectural claims: expiry switches threads
  (4 fires); every fire passes the resume audit; `quantum = 0` is
  state-identical to a run that never touches cmd 57; a single-threaded
  program takes the same 75 cycles with and without a quantum; and the
  **Law-5 spinner** — thread 0 spins on a flag only its child can set —
  terminates with `r9 = 42` under a quantum and *never* terminates without
  one (child left `tstate = READY`, having never run).
* `scripts/preempt_ladder.sh` — the ladder: selftest, D19, emit,
  `iverilog == ISS oracle` byte for byte on the spinner in **both** modes
  (`fpga/zc702/tb_lnp64mini_preempt.v` against `Emit.lean preemptpredict`),
  then all six pre-existing system testbenches reproducing DUAL_SPEC's
  numbers (273 / 372 / 12540 / 14933 / 2014 / 346) with the quantum **off
  and on**. Those six programs are single-threaded, so a quantum that only
  ever switches to a *different* READY thread cannot move them — and does
  not, byte for byte.
* `epoch_ladder.sh`, `capwalk_ladder.sh`, `scripts/ci.sh`, `eqcheck.sh`,
  `lake exe audit` — green; no `sorry`, no `native_decide`, no new axioms.

### Cost (yosys `synth_xilinx -flatten -nowidelut`, `lnp64mini_dual`)

| | before | **after (shipped, cmd 57)** | Δ | *(same design at cmd 56)* |
|---|---|---|---|---|
| LUT cells (LUT2..6) | 27501 | **28223** | +722 (+2.6 %) | *27580 (+79)* |
| FDRE/FDSE | 12389 | **12517** | **+128** = 2 cores × 64 b, exactly the two registers | *12517* |
| CARRY4 | 1049 | **1065** | +16 (the two 32-bit decrementers) | *1065* |
| RAMB36E1 | 26 | **26** | — | *26* |
| est. LCs | 21738 | **22239** | +501 (+2.3 %) | *21908 (+170)* |

**Read that last column before believing the LUT delta.** The two "after"
netlists differ in **exactly one character** — the constant `7'd56` vs
`7'd57` in the cmd decode, one wire, everything else byte-identical — and
yosys/ABC mapped them 643 cells apart. So the *structural* cost is the part
that is stable and countable: **+128 flops** (the two registers, exactly),
**+16 CARRY4** (the two 32-bit decrementers), and a small comparator; the
LUT figure carries roughly ±650 cells of mapper noise at this scale and
should be quoted as a band (+0.3 % … +2.6 %), not a point. Either way it is
inside the budget's "preemption ~0.3k LUT" line and it is a counter, not
datapath.

Placed utilisation and post-route Fmax are **not** in this table: see
deviation 5 — `nextpnr-xilinx` is not on this host, and yosys cell counts do
not convert to `SLICE_LUTX` (the recorded dual is 52134 SLICE_LUTX = 48 %
placed at 27501 yosys LUT cells). The board host must produce the real
numbers.

### EXT-1 board finding: the HARDWARE is fine, the GUEST is not preemption-safe

Measured 2026-08-02 on the ZC702, and it is the reason the demo is the
regression bar rather than a formality.

**What passed.** Post-route **Fmax 34.58 MHz** (up from 25.89 on the previous
epoch build — the tick cost no timing margin) at **46 % SLICE_LUTX**. NetBSD
at **quantum = 0**: `PASS`, ping 10/10, **traps = 0**, both cores retiring —
indistinguishable from §63, so the cooperative default is intact on silicon.
Arming a 1 ms quantum (25 000 cycles @ 25 MHz) on a *live* guest did not crash
it: ping stayed 8/8 with zero loss, which is the first time this guest has ever
been involuntarily interrupted.

**What failed.** Throughput collapsed 4x under that quantum (RTT ~565 ms →
~2350 ms), and a subsequent sweep found the guest **wedged**: retire delta 0
over 2 s at every quantum *including 0*, ping dead. Setting the quantum back to
zero did not revive it — the damage was already done. Recovered by the
autonomy service.

**Reading it honestly.** The slowdown is *policy*, not switch cost: a switch is
one cycle against a 25 000-cycle quantum (~0.004 %). Cooperative scheduling was
implicitly prioritising the thread that had work; round-robining ~21 rump
threads starves the GEM pump. The wedge is the sharper finding — **the rump
guest is not preemption-safe.** Our runtime was written against a machine where
a thread runs until it blocks, so somewhere it depends on that (candidates, not
yet bisected: multi-word non-atomic updates in the shmif ring codec or the GEM
pump, an LR/SC window, or a rump_schedule() vCPU-holder assumption).

**Consequences.**
* `quantum = 0` stays the shipping default; the demo is unaffected.
* Law 5 compliance for the *guest* is its own increment, not a side effect of
  EXT-1. It needs the guest audited for preemption-unsafe sequences, and
  probably a way for a thread to mark a bounded critical region — which is
  itself an architectural question (§6 says the machine contains no
  non-preemptible region, so the answer cannot be "disable preemption").
* The hardware claim stands and is unchanged: preemption fires only at `S_F0`,
  saves `pc` not `pc8`, is silicon-verified, and the Law-5 spinner test passes.

### Guest preemption-safety: the architecture already answers it (do NOT add a preempt-off)

The reflex after EXT-1's wedge is "give the guest a way to disable preemption".
The ISA forbids it (Law 5: no non-preemptible region) and — more usefully —
already ships a replacement for every reason `cli`/`sti` sections exist. The
next increment must be scoped as *mapping each unsafe site to its architected
mechanism*, not as adding a carve-out.

| why a conventional kernel disables preemption | LNP64's mechanism | verdict |
|---|---|---|
| atomicity vs. same-CPU interrupt handlers | there are no such handlers — an interrupt is an InterruptWaitable consumed by a thread, or a machine call at an instruction boundary, governed by the per-thread **`EVENTMASK`** PCR (§8 table row 3: "atomic vs delivery") | equivalent power, and per-*thread* rather than a CPU-global mode: composable, serializable, visible in `EVENTPENDING` |
| atomicity vs. other CPUs | `cli` never provided this. amo / `casq` / futex / serialized gate | strictly better |
| **per-CPU fast paths (`preempt_disable`)** | **`thread.rseq`** (§6, quoted verbatim at isa line 1257): `{start, end, abort_ip, cpu_id_ptr}`, any resumption into `[start,end)` resumes at `abort_ip`; `cpu_id_ptr` kept current with the view-tile ID at every resume, pinned so it cannot fault | **the one genuine loss, and the spec architects the endpoint** — common case pays zero, only actual preemption restarts |
| bounded-latency RT sections | Law 5 makes the longest non-preemptible interval **one bounded instruction**, so preemption latency is a named constant; the RT critical section is the serialized gate, which priority-*inherits* (§9.2) | better: `cli` never inherited, and RT Linux's decade of pain is exactly hunting unbounded preempt-off regions — here they are unconstructible |
| "write these three device registers uninterrupted" | dissolves: the device cannot see preemption. What the idiom needs is *ordering* (fill, `fence.rel`, doorbell — preemption between those stores is harmless) or *mutual exclusion vs other threads* (a lock, row 2) | folklore was one of the other two wearing a trench coat |
| multi-object atomic update | unpublished builders + atomic publication; seqlocks (§6 blesses the torn read); 16 B `casq` | equivalent coverage (§1.1's HTM-replacement row) |
| "don't migrate me" | `rseq`'s `cpu_id_ptr` + restart-on-migration; `dplace` pinning for the strong form | equivalent |

**Applied to our wedge — the leading hypothesis is row 3.** Our runtime keeps
per-*core* state that assumes run-until-block: `LNP64_ZP_COREID` lives in the
core-private zero page, the §64 work put `curlwp` slot lookup on a fast path,
and the shmif ring codec and GEM pump do multi-word updates that cooperative
scheduling made atomic for free. Those are exactly the per-CPU-fast-path and
cross-thread-atomicity patterns, so the fix is `rseq` for the former and real
atomics/locks for the latter — NOT a preempt-off.

**Consequence for scope:** if the guest is to run preempted, `thread.rseq`
becomes a hardware dependency of this campaign (a per-thread descriptor and a
resume-PC edit — small, and it is §9.3's machinery minus the payload), and
`EVENTMASK` becomes one as soon as machine-call delivery exists. Both are
cheap engine-side; neither is in the seven items as originally listed. Bisect
the wedge FIRST, then add only what the sites actually require.

### CORRECTION to the EXT-1 board finding (2026-08-02, later the same day)

The finding above says "the rump guest is not preemption-safe". **That is not
supported by the evidence and is withdrawn.** Controlled re-testing:

| test | result |
|---|---|
| core 1 only, 1 ms, 2 s | retire 538K → 543K per 2 s, ping 5/5 — unaffected |
| core 0 only, 1 ms, **21 s** | retire +16 M, healthy throughout, **no wedge** |
| **both cores**, 1 ms, **17 s** | both retiring (c0 386→400 M, c1 145.7→149.1 M), **no wedge** |
| both cores, 1 ms, RTT measured **while armed** | 608 ms → **1999 ms (3.3x)**, **0 % loss**; 590 ms after disarm — fully reversible |
| both cores, 100 ms quantum | retire unchanged (1.317 M → 1.313 M per 2 s), no measurable cost |

**What is true.** Preemption works on the live guest: it survives, keeps
serving with zero packet loss, on either core or both, and the cost is
*throughput*, not correctness. The cost is policy — a switch is one cycle in
25 000 (0.004 %); cooperative scheduling had implicitly prioritised the thread
with work, and round-robining ~21 rump threads starves the GEM pump.

**What was wrong.** The single wedge that produced the original finding did not
reproduce in ~40 s of subsequent testing across three configurations, and the
"4x slowdown" measurement in that session was taken *after disarming* — an
error in my own test, not a property of the system. Cause of the one wedge:
**unknown and unreproduced**; recorded as such rather than attributed.

**The useful conclusion.** Law 5 requires preemption to be *bounded*, not
*frequent* — any finite quantum makes preemption latency a named constant. At
100 ms the cost is unmeasurable and the bound still exists. So the operating
point is a long quantum, and the guest needs no rseq/atomics work to satisfy
Law 5 today. The row-2/row-3 analysis above remains the right map IF a future
workload needs a short quantum; it is not a prerequisite now.

### EXT-1 CLOSED — the demo is Law-5 compliant by default

`lnp64_rump_run_dual.tcl` now arms a 2 500 000-cycle (100 ms @ 25 MHz) quantum
on **both** cores immediately after start; `LNP64_QUANTUM=0` restores the
cooperative machine for bisecting. Full unattended acceptance from power-off
(`/home/kevin/autonomy/20260802-164008`):

```
PREEMPT: core0 quantum=2500000 cycles
PREEMPT: core1 quantum=2500000 cycles
[16:41:50] GEM up after ~60s
== lnp64 micro-shell on the ZC702 fabric (NetBSD stack on the core) ==
10 packets transmitted, 10 received, 0% packet loss
rtt min/avg/max/mdev = 408.324/619.968/966.594/183.847 ms
RETIRE core0=30362005 core1=2074676  status0=0x5 status1=0x5
traps=0
== PASS: NetBSD serving native GEM0, dual-core, BSCAN quiet ==
```

620 ms RTT against 598–608 ms cooperative baselines — no measurable cost. So
the shipping demo is *preemptively scheduled* with traps=0, zero-BSCAN steady
state, and unattended power-on boot, and the cooperative machine survives only
as a debugging switch. Hardware: post-route **Fmax 34.58 MHz** (up from 25.89
— EXT-1 improved timing), **46 % SLICE_LUTX**.

---

## EXT-2 — protection domains. 2026-08-02

The unit every later increment is scoped by: gates cross *between* domains,
capability transfer re-keys *across* them, and a VMA root is a property *of*
one. Nothing below EXT-2 can be stated without it.

### What it is

| | |
|---|---|
| `tdom` | 32x8 memory — the per-thread domain tag |
| `domCur` | `tdom[cur]`, read **combinationally** — the domain the core is executing in |
| `cur_dom` | 8-bit register, observation mirror for the BSCAN path only |
| `cmd 58` | set one thread's domain: `data[4:0]` = slot, `data[15:8]` = domain |

Two decisions carry the increment.

**The tag is per thread, and the core's domain is derived — not a register.**
Threads are what the scheduler moves, so a core's domain is whatever its
current thread's is. A `dom` register updated at each switch would lag `cur`
by a cycle, and the cycle after a context switch is precisely when a stale
tag is a privilege hole: the incoming thread's first instruction would run
under the outgoing thread's authority. An async `memRead` at `cur` is always
right, costs one LUTRAM read port, and — the practical part — has no write
sites to keep in sync with the **eight** places that assign `cur`.

**A thread cannot leave its domain by spawning.** `CLONE` writes the
parent's `domCur` into the child's slot, in the same cycle and the same
guarded branch that allocates `free_slot` and writes the child's entry PC,
so the two cannot disagree. Without this, one instruction escapes a domain.
No instruction moves a thread between domains; `cmd 58` is a host/debug
operation.

### Deviations

* **No per-domain root table (`droot`) yet.** A domain's capability/VMA root
  is real state, but nothing in EXT-2 *reads* it. A write-only memory is
  dead silicon: yosys deletes it, and the emitted netlist then no longer
  matches the design the proofs are about. It lands with its first consumer
  (EXT-6/EXT-7). This is the D30/D37 lesson applied early — do not put state
  in the design that the flow will quietly not carry.
* **The tag is installed, not yet enforced.** Every comparison EXT-2 adds is
  against a constant, because every thread is in domain 0. Enforcement
  arrives with gates (EXT-5) and the MMU (EXT-7). Said plainly here so it is
  not later mistaken for a working boundary.

### Toolchain

**No emulator change was needed, and that is a finding, not a shortcut.**
`src/emulator.rs` already models domains: `Thread` carries `domain_id`, and
the thread-spawn path (`CloneProfile::SpawnEntry`) builds the child with
`self.thread()?.clone()` — so the child inherits the parent's domain, which
is exactly the rule the hardware now enforces. `smp_start_core` likewise
takes `boot.domain_id`. The oracle already agreed with the design; EXT-2
brought the hardware up to the model rather than the other way round.
EXT-2 adds no opcode, so the assembler and ISA tables are untouched.

The **Lean ISS** did need the work, and this is where the campaign rule bit:
the ladder passed *before* the ISS modelled anything, because the state the
increment added was not in the comparison — a green test that proved
nothing. `Iss.lean` now carries `tdom`/`cur_dom` (reset sweep, `cmd 58`,
`CLONE` inheritance, mirror) and `cmpStates` compares `cur_dom` plus **all
32 `tdom` slots every cycle**. Slot-wise is the point: inheritance is a claim
about a slot the running program never reads, so a spot check at `cur` cannot
see a violation.

### Evidence

`domselftest` makes both claims, and the second is deliberately non-vacuous
— the parent is put in domain **7**, not 0, because with everything at zero
the test passes even if inheritance is deleted outright.

`lake env lean --run Machines/Lnp64mini/Emit.lean domselftest`:

```
  OK  DOMAIN (EDSL≡ISS on cur_dom + all 32 tdom slots, 60 cyc)
  domain: parent tdom[0]=7 (want 7) child tdom[1]=7 (want 7) other non-zero slots=0 (want 0) cur_dom=7
LNP64MINI DOMAIN SELFTEST OK — EDSL≡ISS on the tag + CLONE cannot leave its domain
```

Full ladder (`scripts/preempt_ladder.sh`) green: the iverilog leg still
matches the Lean ISS oracle byte for byte, and the six system testbenches
still reproduce DUAL_SPEC's numbers with the quantum off **and** on.

**Silicon (`lnp64mini_epoch_top`, openXC7):**

| | EXT-1 | EXT-2 | |
|---|---|---|---|
| post-route Fmax (`sysclk`) | 34.58 MHz | **31.74 MHz** | vs a 25 MHz clock — 27 % margin |
| SLICE_LUTX | 49 251 (46 %) | **52 753 (49 %)** | +3 502 cells |

NetBSD acceptance on the EXT-2 bitstream (`/home/kevin/autonomy/20260802-180005`):
`PASS`, ping **10/10, 0 % loss, 633 ms** (vs 620 ms at EXT-1 and 598–608 ms
cooperative), **traps=0**, BSCAN quiet, unattended from power-off.

**The +3 502 LUTs is over the ~1.5k budget estimate and is recorded as a
miss, not rounded away.** At 49 % against an 85 % target it does not
threaten the campaign, but the estimate was wrong by ~2.3x and the later
per-increment estimates in the budget table should be treated as optimistic
until measured. Fmax fell 8 % for a tag that is not yet read by anything on
the critical path — worth revisiting if EXT-7 (the one increment with real
Fmax risk) arrives with less than the current 27 % margin.

---

## EXT-3 — fail-stop / poison. 2026-08-02

The architected disposition every later engine feeds. §3's epoch machine and
Appendix F's fail-stop rule both need one answer to "this thread's authority
is gone" that is not "raise a fault and hope the handler is correct" — the
machine must stop the thread, not trust software to.

### What it is

`poison`, a 32-bit bitmap, one bit per thread slot, plus `cmd 60` to load it
whole-word. Two enforcement points, and they are **not** the same rule:

1. **A poisoned thread is never scheduled.** The mask lands on `readyBm` —
   the scheduler's single ready bitmap — so `next_ready`, `nr_any` and every
   picker downstream inherit it from one `and`. This is why poison is a
   *bitmap* and not a per-thread memory: the picker reads every slot at once
   (D20's rule), so the mask must be readable at every index at once too.
2. **A poisoned thread executes no further instruction.** Masking the picker
   alone is *not* fail-stop — the running thread is not re-picked, so a
   thread poisoned mid-run would continue until it happened to yield. `S_F0`
   therefore stops the core outright (`running := 0`) when `curPoisoned`, at
   the instruction boundary with nothing fetched and `bus_req` already
   excluded — the same property that makes EXT-1's preemption point safe.

Stopping the core rather than switching threads is the fail-*stop* reading
of Appendix F: the disposition is "this machine has lost the right to
proceed", and quietly running someone else would hide it. The host sees
`running = 0` and the bitmap says which slot.

`cmd 60` is whole-word because the raise is meant to be **atomic across
slots**: a domain losing authority poisons every thread it owns in one
cycle, and a host read-modify-write could interleave with a `CLONE` that
adds one.

### What writing the test taught (kept, because it is the real content)

The first version poisoned the child mid-run, at cycle 24, and failed — the
parent never ran again. That was not a bug: at cycle 24 the *child* is the
thread on the core, so poisoning it took the claim-1 path and stopped the
machine. **"Descheduled" and "fail-stopped" are only distinguishable when
the poisoned slot is provably not `cur`**, so the test now poisons the child
at cycle 2, before `CLONE` has even admitted it. A single-claim test would
have hidden this: a bug that stopped *everything* passes claim 1 alone,
which is why the parent's progress to `EXIT` is the control.

### Evidence

```
  OK  FAILSTOP (EDSL≡ISS with poison live, 60 cyc)
  running-thread: poisoned running=false retire=4 vs unpoisoned retire=9 halted=true
  ready-thread:   parent halted=true (want true) r9=2 (want 2) child tstate=1 child tpc=0x1028
LNP64MINI FAILSTOP SELFTEST OK — poison stops the runner AND deschedules the ready
```

`child tstate=1` is the point of claim 2: the child is **READY** and still
never ran.
