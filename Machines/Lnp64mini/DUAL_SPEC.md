# Dual-core SMP lnp64mini spec — binding decisions

Goal: two identical composed core instances, safe+efficient SMP, on the
ZC702 (LUT budget: single SoC = 41% of LUT sites; dual ≈ 80% — tight but
routable; the 31.69 MHz margin funds the degradation; accept ≥25 MHz).

## Memory model (document in Soc file header)
Uncached DDR through one arbiter = sequential consistency per the
interleaving the arbiter serializes. zp dmem, UART rings, rf: core-private
ABI. All shared data lives in DDR.

## Core extensions (Machines/Lnp64mini/Core.lean — small, faithful; ISS +
selftest updated in lockstep; parameterize nothing else)
1. New D15 input `res_kill` (1): when pulsed, clears `lr_valid`. (Global
   LR/SC: the arbiter kills a core's reservation when the OTHER core
   writes any address; address-precise filtering optional v2 — spurious
   kill only makes SC fail→retry, always safe.)
2. New D15 input `doorbell` (1): when pulsed, every thread in FUTEX state
   (tstate=3) → READY (1). Spurious wakes are SAFE: woken FUTEX_WAIT
   re-executes its DDR compare and re-blocks if unchanged. This is the
   cross-core wake path.
3. New register `wake_out` (1): pulses 1 for one cycle when FUTEX_WAKE
   executes (S_EX op 0xcc) — regardless of local matches. o_wake_out
   drives the OTHER core's doorbell (via arbiter/SoC wiring, 1-cycle
   delayed register is fine and avoids combinational cross-core paths:
   route through a register stage in the SoC wiring).

## New Loom design: HpArbiter (Machines/Lnp64mini/HpArbiter.lean)
Two requester ports (c0_rd/c0_wr/c0_addr/c0_wdata, c1_*) → one
downstream simple-handshake master (the existing HpMaster instance);
round-robin grant at op boundaries; per-core done/rdata routing
(c0_done/c0_rdata registers, c1_*). Reservation kill: when core j's WRITE
completes, pulse res_kill_i (i≠j) — v1 kills on ANY remote write.
ISS mirror + selftest (interleaved read/write scripts, both cores).

## SoC (Machines/Lnp64mini/DualSoc.lean)
dual = (core.prefixed "c0_") ∥ (core.prefixed "c1_") ∥ arbiter ∥
(hp master) ∥ (gpm master, core0-only v1: GEM belongs to core 0;
core 1's GP aperture traps — acceptable, NetBSD runs on core 0) with
connect wiring: cores' m_done/m_rdata ← arbiter per-core outputs;
arbiter downstream ← hp master; cross doorbells via one-cycle register
stage (regs `db0`,`db1` in a tiny glue design or extra rules — a third
tiny Loom design `CrossGlue` is cleanest); res_kill wiring from arbiter.
JTAG DDR window: core 0's jtag path only (c0 owns the loader); the HP
ownership mux generalizes: JTAG owns when BOTH cores yield (c0 parked ∧
c1 parked/held).

## CORE1_HOLD + BSCAN
Wrapper DR bit dr[39] (unused in the mini map) = core-select for cmd
writes: 0→core0 cmd ports, 1→core1 (jtag_lib: wr [expr 0x80|idx] targets
core 1 — library-compatible). New wrapper-level cmd (core-1 idx 13 bit2
reserved? NO — simpler: dedicated hold: core-select write idx 56 data
bit0 = CORE1_HOLD register in wrapper) gates c1 running via... cores have
no run input — HOLD = wrapper forces c1 cmd 13 reset? Cleanest: a
`hold` D15 input on the core (extension 4): when high, the FSM treats
running as 0 (guard fsmEn with ¬hold) and the sleep scan pauses. One-line
core change, ISS mirrored. Read map: idx 56 returns {hold, c1 status}.
Per-core readbacks: existing read map serves core 0; add dr[39]-selected
variants for core 1 (wrapper muxes o_c1_* when the READ scan used
bit39 — latch region bit at UPDATE like idx).

## Validation ladder
1. Core-extension selftests (res_kill/doorbell/hold scripts) EDSL≡ISS.
2. Arbiter selftest; DualSoc emit; iverilog tb: behavioral AXI slave +
   TWO cmd drivers; test program pair: core0 loomcheck + core1 loomcheck
   at different DDR windows (shared-nothing) → both halt, both rf correct.
   Then a SHARED test: spinlock via LR/SC on a DDR word, two cores
   increment a shared counter N times each → final = 2N (atomicity), and
   a futex ping-pong (core0 waits, core1 wakes via doorbell) → no lost
   wakeup, both progress (the s13 discipline cross-core).
3. Rust emulator: assemble the same shared tests; single-core emulator
   can't model SMP interleaving — run each core's program independently
   for the shared-nothing test; the SHARED tests' oracle = the invariant
   (final=2N, both halted) not a trace. (Full dual-core emulator = guest
   SMP task, later.)
4. Board: dual bit, same tests via both BSCAN surfaces, then the NetBSD
   demo UNCHANGED on core 0 with core 1 held (regression), then core 1
   released running a counter workload while NetBSD serves (coexistence).

---

# Implementation record + deviations (2026-07-30)

Everything below is what was actually built, and where it departs from the
binding text above. Deliverables:

| artifact | what |
|---|---|
| `Machines/Lnp64mini/Core.lean` | SMP extensions (below), ISS-lockstepped |
| `Machines/Lnp64mini/Iss.lean` | mirrors every extension |
| `Machines/Lnp64mini/Harness.lean` | `smpSelftest` — 6 EDSL≡ISS scripts + outcome assertions |
| `Machines/Lnp64mini/HpArbiter.lean` | new Loom design + ISS + 4-script selftest |
| `Machines/Lnp64mini/DualSoc.lean` | `dual` = c0 ∥ c1 ∥ arb ∥ hp ∥ gpm |
| `Machines/Lnp64mini/Emit.lean` | `dual`, `arbselftest`, `smpselftest` args |
| `rtl/lnp64mini_dual.v` | 22,363 lines emitted (`… Emit.lean dual`) |
| `fpga/zc702/lnp64mini_dual_top.v` | dual BSCAN wrapper (dr[39] core-select, idx 56 CORE1_HOLD) |
| `fpga/zc702/tb_lnp64mini_dual.v` | the three ladder-step-2 tests |
| `fpga/zc702/{smpcount,pingpong0,pingpong1}.s` | assembled with `lnp64 asm-flat-exec` |

## D1 — Core extensions: four D15 inputs, not three

Spec extensions 1–3 (`res_kill`, `doorbell`, `wake_out`) are implemented
verbatim, in one new rule `smpRule` placed **after** `fsmRule` so both
overrides are deterministic. Extension 4 (`hold`) needed a refinement, and
a fourth input had to be added:

* **`hold` bites only at `S_F0`** (`holdEn = hold ∧ st = S_F0`), not
  unconditionally. Measured: an unconditional freeze parks the core in
  `S_FW`/`S_DL`/`S_DSW`, where it *misses the `m_done` pulse* and is wedged
  forever (`progLRSC` never halted in 200 cycles). `S_F0` is the
  instruction boundary with no bus transaction outstanding, so the hold is
  clean and reversible. Verified: held run ≡ free run on all of `rf`,
  `retire` and `halted`, only later in time.
* **`sc_fail` (new D15 input) + `lr_req`/`sc_req`/`sc_pending` (new
  registers)** — the global LR/SC fix, see D2. `sc_fail` adds exactly one
  `rfTriples` entry (`S_DSW ∧ sc_pending ∧ m_done ∧ sc_fail` → `rd := 1`),
  disjoint from every existing triple.

All four inputs are inert at 0 and `Soc.lean` ties them off, so the
single-core `lnp64mini_soc` keeps its exact pre-SMP behaviour. Regression:
`tb_lnp64mini_soc.v` on `loomcheck.hex` still prints
`HALTED=1 cycles=273 pc=4192 retire=25`, `r1..r9 = 6,7,42,255,36,14,42,56,14`,
`dmem32=42` — bit-identical to §63.

## D2 — Global LR/SC: the reservation lives in the arbiter (major)

The spec's v1 ("the arbiter kills a core's reservation when the OTHER core
writes any address") is **not atomic**, and the spec's suggested v2
(address-precise filtering) **livelocks**. Both were built and measured:

1. **v1.** A core checks `lr_valid` in `S_EX` and only pulses `core_wr` the
   cycle after; the write is *ordered* 2+ cycles later still. Two cores can
   therefore both pass their `SC` check before either write is ordered → a
   lost update, with the kill always arriving too late. Unsound by
   construction, whether the kill fires at the remote write's issue or its
   completion.
2. **v2 (address-precise, on any remote access).** This makes the
   reservation exclusive — the later `LR` steals it — and closes the
   atomicity hole in practice. It also **livelocks**: two cores whose loop
   bodies differ in length drift into anti-phase and steal from each other
   forever. Measured in `tb_lnp64mini_dual.v` with a 100-iteration
   `smpcount` on core 0 and a slightly longer one on core 1:
   `CYCLES=2000000` (timeout), `res_kill0=33330 res_kill1=33330`,
   `shared=2` — 2 increments in two million cycles.

**What shipped**: the arbiter is the reservation point, i.e. an `SC` is a
*conditional store validated where the memory order is decided*:

* the core tags its requests: `lr_req` (this read takes a reservation) and
  `sc_req` (this write is conditional) — one-cycle pulses beside `core_rd`
  / `core_wr`, in the same pulse-default group;
* granting a tagged read sets the arbiter's `r{i}_v`/`r{i}_a`;
* granting **any write** from core `j` to `r{i}_a` (`i≠j`) clears `r{i}_v`
  and pulses `res_kill{i}` — spec extension 1 survives verbatim, but as an
  *optimisation* (the victim's `SC` then fails locally, with no bus round
  trip) rather than the correctness mechanism;
* granting a tagged write from core `i` checks `r{i}_v ∧ r{i}_a = addr`.
  If it holds, the write goes downstream and consumes the reservation. If
  not, the write is **dropped** — it never reaches DDR — and the request
  completes immediately with `c{i}_sc_fail`, which the core turns into
  `rd = 1` at `S_DSW`.

Atomicity is then exact (two `SC`s to one word are ordered by the arbiter;
the second finds its reservation consumed) and progress is guaranteed
(reservations die only when a write *succeeds*, so every failed `SC` is
paid for by another core's committed store). The anti-phase program that
livelocked under v2 now finishes in **14,933** cycles with `shared=200`
(= 2N), 100 committed increments per core and 40 reservation kills.

## D3 — No `CrossGlue`

The spec offers "a third tiny Loom design `CrossGlue`" for the one-cycle
doorbell register stage. Not needed: `wake_out` **is** a register, so
`c1_doorbell ← .reg 1 "c0_wake_out"` is already a register-output→input
connection — a full register stage with no combinational cross-core path.
The extra design would only have added a second cycle of latency.

## D4 — JTAG DDR window: no "both cores yield" gate in the datapath

The spec asks for "JTAG owns when BOTH cores yield". In the *datapath* this
is unnecessary and would be a regression: the arbiter already serializes,
so core 0's JTAG requests simply interleave with core 1's traffic through
requester port 0's existing ownership mux (`owns0 ? core_* : jtag_*`), and
`arb_c0_done` only ever pulses for core 0's own ops, so core 0's `ddr_rd_l`
latch is unchanged. The "both cores yield" formula *is* used, in the
wrapper, for the `bus_granted` status bit the host polls (idx 20).

## D5 — Core 1's GP aperture completes instead of trapping

The spec says core 1's GP aperture "traps". The core has no trap path for
GP; it enters `S_GPL`/`S_GPS` and waits for `gp_done`, so tying `gp_done`
to 0 would wedge it. Core 1's GP responses are tied to *instantly done,
reads 0*, so a stray core-1 GP access completes harmlessly. GEM still
belongs to core 0 only.

## D6 — Shared test addresses come from `.data`

The shared word is the first `.data` symbol, byte address **0x10000**. It
is ≥ 0x1000 (so the mini core routes it to shared DDR, not the private
zero page) *and* it is backed by the Rust emulator's flat-exec data image,
so `smpcount.s` also runs single-core on the emulator (`r10 = N`), giving
ladder step 3 a real oracle. Core 1 runs a second copy of its text at
0x4000 (`cmd 53 SET_PC`); all control transfers in these programs are
pc-relative, so the image is position-independent.

## D7 — `wake_out` in the emitted single-core SoC

`lnp64mini_soc.v` gains the `o_wake_out`/`o_lr_req`/`o_sc_req`/
`o_sc_pending` output ports (every register is an `o_*` port). The §63
wrapper leaves them unconnected, which is legal and changes nothing.

## Ladder results (iverilog, `rtl/lnp64mini_dual.v`)

Step 1 — `lake env lean --run Machines/Lnp64mini/Emit.lean smpselftest`:
six EDSL≡ISS scripts (`res_kill`, global-SC refused, global-SC accepted,
`doorbell`, `wake_out`, `hold`) over every register, plus the outcome
assertions (SC result, park/wake, exactly one `wake_out` pulse, held-run ≡
free-run `rf`/`retire`).

Step 2 — `arbselftest` (4 scripts) and `tb_lnp64mini_dual.v`:

| test | result |
|---|---|
| shared-nothing dual `loomcheck` | both HALTED, retire 25/25, both `r1..r9 = 6,7,42,255,36,14,42,56,14`, `dmem32=42` each |
| LR/SC shared counter, N=100 each | `shared[0x10000]=200`, `r9=100`/`r10=200` per core |
| the same with `smpcount_skew.s` on core 1 | `shared[0x10000]=200`, 40 reservation kills, 14,933 cycles |
| futex ping-pong | both HALTED, `r9=8` each, `wake_out` 8/8, 210/240 cycles parked in `S_WAIT` |
| `-DONLY_C0` (CORE1_HOLD) | core 0 correct; core 1 started but `retire=0`, `pc=0x1000`, `rf` zero |

Step 3 — Rust emulator: `smpcount.hex` and `smpcount_skew.hex` reach
`r9 = r10 = 100` single-core.

Step 4 (board) is **not** done: this pass stops at a synthesis datapoint.

## Synthesis datapoint (openXC7, xc7z020clg484-1)

### Before D19 — the dual did not fit

Reference — the single-core `lnp64mini_soc_top` on the same flow:
`SLICE_LUTX 44567/106400 (41%)`, `SLICE_FFX 9659 (9%)`, `RAMB36E1 1/140`,
`Max frequency for clock 'sysclk': 31.69 MHz` post-route.

The dual, with the repository's stock recipe
(`yosys synth_xilinx -flatten -nowidelut` -> `nextpnr-xilinx`):

```
Info: Device utilisation:
Info:           SLICE_LUTX: 99072/106400    93%
Info:            SLICE_FFX: 18912/106400    17%
Info:            RAMB36E1:      2/  140      1%
Info:            BUFGCTRL:      5/   32     15%
ERROR: Unable to find legal placement for all cells, design is probably
       at utilisation limit.
```

Two cores cost **2.22x** the single-core LUTs and `nextpnr-xilinx` could
not legalize the placement. Allowing widelut was *worse*: `synth_xilinx
-flatten` gives `SLICE_LUTX 107229/106400 (100%)` and `ERROR: Failed to
expand region (0,0) |_> (186,156)`, because nextpnr-xilinx accounts each
fractured `LUT6_2` as two `SLICE_LUTX` bels.

The cause: µVerilog's only memory kind has *asynchronous* in-expression
reads, so the 1024x64 `rf` — with six read sites per core — synthesized to
distributed LUTRAM (`RAM64M`) while 138/140 block RAMs sat idle.

### After D19 — same recipe, same testbench outputs, block RAM

`Loom/Hw/D19_SPEC.md` (the decision) and `PORTING_SPEC.md` deviation 5
(the two value-preserving shape fixes to `Core.lean`: drop the state-muxed
shared read address, drop the redundant `x0` zero-mux). Nothing in Loom's
syntax, semantics, compiler or printer changed; the D19 contribution is a
decidable check, `Design.syncReadOkB`, that every emit path discharges:

```
$ lake env lean --run Machines/Lnp64mini/Emit.lean d19
  rf: syncReadOk=true sites=6 [reg_rd,a,b,rdval,sel_t,sel_f]
  dmem: syncReadOk=true sites=1 [dmem_rd]
  uart_mem: syncReadOk=true sites=1 [uart_byte]
  rx_mem: syncReadOk=false sites=0 []  (STRAY combinational read)
```

Single-core `lnp64mini_soc_top`, same flow:

| | before | after |
|---|---|---|
| `SLICE_LUTX` | 44567 (41%) | **37606 (35%)** |
| `SLICE_FFX` | 9659 (9%) | 9275 (8%) |
| `RAMB36E1` | 1/140 | **13/140 (9%)** |
| `sysclk` post-route | 31.69 MHz | **32.53 MHz** |

(yosys `stat` on the bare `lnp64mini_soc` module shows where it went:
`RAM64M` 1432 -> 24, `RAMB36E1` 1 -> 13.)

Dual `lnp64mini_dual_top`, same flow:

```
Info:     Created 83734 SLICE_LUTX cells from: ...
Info: Device utilisation:
Info: 	          SLICE_LUTX: 83926/106400    78%
Info: 	           SLICE_FFX: 18144/106400    17%
Info: 	            RAMB18E1:     0/  280     0%
Info: 	            RAMB36E1:    26/  140    18%
Info: 	            BUFGCTRL:     5/   32    15%
...
Info: Creating initial analytic placement for 73771 cells
Info: Running main analytical placer.
ERROR: Unable to find legal placement for all cells, design is probably
       at utilisation limit.
```

**93% -> 78% (-15,146 SLICE_LUTX, -15.3%), 2 -> 26 RAMB36E1 — and
`nextpnr-xilinx` still cannot legalize the placement.** D19 did what it was
designed to do (the regfiles are in block RAM; the LUTRAM `RAM64M` cells
are gone), and it was necessary, but it is **not sufficient**: the HeAP
placer fails at the same step it failed at 93%, so the binding constraint
is not raw LUT headroom alone. No post-route Fmax number exists for the
dual yet.

The failure is reproducible, not seed luck: re-running `nextpnr-xilinx`
on the cached synthesis JSON with `--seed 7` (and a `--seed 1` attempt)
fails at the same step with the same message.

Remaining options, updated:

* ~~`rf`/`dmem` into BRAM~~ — **done (D19)**, 15% of the LUT budget
  recovered, still short;
* ~~dropping `-nowidelut`~~ — tried pre-D19, worse (`SLICE_LUTX
  107229/106400`, nextpnr counts a fractured `LUT6_2` as two bels);
* shrinking the per-core thread table `NT` (32 -> 8) — the 32-way
  `tpc`/`tstate`/`tsleep`/`tfutex`/`tp_arr`/`sigmask_arr` dynamic
  read/write trees are now, by elimination, the biggest LUT consumer left
  in the core. `tpc`/`tsleep`/`tfutex`/`tp_arr`/`sigmask_arr` are also
  32x64 arrays with one dynamic write index — i.e. plausible **D19
  candidates in their own right** if their reads are restaged through
  latch registers;
* a bigger part.

Ladder evidence that the meaning did not move: `selftest`, `smpselftest`,
`arbselftest`, `hpselftest`, `gpselftest`, `progtest` all OK (EDSL == ISS
bit-exact, ISS untouched), and all **six** iverilog system testbenches
(soc `loomcheck`; dual shared-nothing / LR-SC / LR-SC-skew / futex
ping-pong / `-DONLY_C0`) produce **byte-identical** output before and
after — same cycle counts (372 / 12540 / 14933 / 2014 / 346), same
reservation-kill counts (39/1), same `wake_out` 8/8, same `S_WAIT` 210/240.

Ladder step 4 (board) is still **not** done: this pass deliberately stops
at the fit, and the D19 cross-port collision obligation
(`PORTING_SPEC.md` deviation 5) has not been confirmed on silicon.
