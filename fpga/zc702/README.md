# Loom on a real FPGA — ZC702 bring-up (first light)

This directory is the board half of the substrate ports
(`Machines/Substrate/`): Loom-emitted cores running on a real Xilinx Zynq
XC7Z020 (ZC702 board) through an entirely open-source flow. It is the
first hardware realization of the CHARTER Phase-2 gate "first light on
FPGA".

Everything here is **untrusted wrapper** in the same role as a testbench:
LVDS clock buffers, power-on reset, LED pins, and a BSCANE2 JTAG register
bridge for observing the core. All synchronous logic comes from
`rtl/*.v` emitted by the verified compiler + printer.

## The two ported designs

Both are ports of the `remote-fpga` substrate-0 bring-up RTL (the designs
that brought this board up originally), re-expressed as Loom `Design`s:

**S0Blinky** (`Machines/Substrate/S0Blinky.lean` → `rtl/s0blinky.v`):
the toolchain smoke test — a 28-bit counter, top four bits on the LEDs.

**S13Soak** (`Machines/Substrate/S13Soak.lean` → `rtl/s13soak.v`): the
board-endurance soak engine — an LFSR randomizes the interleaving of
event injection into 8 IRQ sources, a periodic timer that also injects, a
DMA submit/complete countdown, and a round-robin server draining pending
sources, with in-fabric checkers for lost wakeups and accounting
violations. The port is **self-timed**: a closed Loom design that runs
exactly K=100000 cycles from reset and freezes; `SoakIss` in the same
file is the fast executable mirror whose K-cycle state is the oracle for
both simulation and silicon.

## Flow

```console
# 1. emit (repo root; also run `selftest` for the Design ≡ ISS check)
lake env lean --run Machines/Substrate/Emit.lean
lake env lean --run Machines/Substrate/Emit.lean selftest
lake env lean --run Machines/Substrate/Emit.lean predict > /tmp/prediction.txt

# 2. build (on the board host, which has openXC7 + the ZC702 on USB-JTAG;
#    build_oxc7.sh = yosys -> nextpnr-xilinx -> fasm2frames -> xc7frames2bit)
oxc7/build_oxc7.sh s13soak_top loom/s13soak.xdc loom/s13soak_top.v loom/s13soak.v

# 3. program + read back over the BSCAN bridge (xsdb; jtag_lib.tcl rd/wr)
xsdb loom_s13_read.tcl        # prints the frozen engine state
diff <(that output) /tmp/prediction.txt
```

## Evidence (2026-07-30, ZC702, openXC7 flow)

* **S0Blinky**: bitstream built and programmed; the four user LEDs blink
  at the staggered rates (camera-verified across timed snapshots — change
  hotspots localize to the LED row).
* **S13Soak**: after the self-timed 100000-cycle run on silicon, every
  register read back over BSCAN equals the Lean model bit-for-bit —
  including the LFSR after 10^5 steps, all four traffic counters, and all
  eight age counters:

  | register | Lean ISS | silicon |
  |---|---|---|
  | cyc | 100000 | 100000 |
  | injected / serviced | 6339 / 6339 | 6339 / 6339 |
  | dma_sub / dma_comp | 5838 / 5838 | 5838 / 5838 |
  | err | 0 | 0 |
  | maxout | 3 | 3 |
  | tmr_exp | 332 | 332 |
  | lfsr | 39260 | 39260 |
  | tmr | 68 | 68 |
  | pending | 0x00 | 0x00 |
  | age0..7 | 1,6,7,2,1,7,1,3 | 1,6,7,2,1,7,1,3 |

  The run is reproducible: holding reset over the bridge (`RSTCTL`) and
  releasing re-runs the engine to the identical frozen state. The soak
  verdict itself is the s13 acceptance: err=0, injected==serviced,
  dma_comp==dma_sub, engine quiescent.

  The same emitted `.v` at the same K matches the Lean ISS in iverilog
  (`RTL_LOCKSTEP_OK`, all 29 registers), so the chain
  Lean `Design` → verified compile → printed text → synthesized silicon
  is corroborated end-to-end at two independent points.

## Trust status

The invariant/refinement story for these two designs is deliberately not
started (per the port's scope). What holds today: the `.v` files are the
verified pipeline's output (same `compile`+`print` as the release cores),
the EDSL data equals its fast mirror at small depth (`selftest`), and the
silicon equals the mirror at full K. The synthesis tools (yosys,
nextpnr-xilinx) and the wrapper are corroborated, not proved — the same
boundary as `CONCRETE_SSA_BOUNDARY.md` states for the release artifacts.

## Board-side specifics

The ZC702 lives at the `remote-fpga` project's board host with openXC7
(`oxc7/build_oxc7.sh`), xsdb, a relay power-cycle script, and a camera;
the BSCAN bridge speaks the `jtag_lib.tcl` 41-bit USER1 protocol (the
library shifts 42 bits per scan — the Zynq PS TAP sits in BYPASS in the
same chain and eats one bit; a 42-bit DR is the classic first-build bug).
See `remote-fpga/fpga_dev.md` §62 for the full bring-up log of this port.

## Open designs: S0BscanRegs (D15 ports, first silicon proof — 2026-07-30)

`Machines/Substrate/S0BscanRegs.lean` ports the substrate-0 M0 register
file — the design the closed discipline could not express (JTAG *writes*
into it). It is the first user of the D15 input-port extension
(`Loom/Hw/DESIGN.md` §D15): inputs are environment-owned state
coordinates; the BSCAN DR shift + UPDATE→sysclk toggle-sync CDC live in
the untrusted wrapper (`s0bscan_top.v`) and deliver one command per JTAG
transaction as a one-cycle `cmd_valid` pulse on the module's ports.

Evidence: the 33-command acceptance trace (ID, scratch write/readback,
heartbeat, LED write, full 19-char banner drain + exhaustion + re-arm,
BRAM write/readback) matches the Lean ISS at all three points —
`Design.cycleOpen` lockstep (`selftest`), iverilog on the emitted module
(all 33 responses), and the ZC702 over `jtag_lib.tcl`
(`loom_s0bscan_accept.tcl`: all 31 static responses equal, heartbeat
ticking; the banner text "SUBSTRATE-0 M0 OK\r\n" served byte-by-byte from
a Loom ROM on real silicon). The emission theorem extends to open designs
as `Compile.compile_cycleOpen` — a corollary, not a re-proof.

## Lnp64mini: NetBSD on the Loom-emitted core (2026-07-30)

`Machines/Lnp64mini/` is the full port of the lnp64mini3 soft-core (the
processor that runs NetBSD in the remote-fpga project): all 21 FSM states,
the complete opcode set, MUL/DIV, the 32-thread hardware scheduler,
LR/SC/futex, UART, GP MMIO, traps, and the BSCAN command surface — an open
design over D15 ports, with the AXI masters/PS7/JTAG plumbing in the
untrusted wrapper (`lnp64mini_top.v`, a drop-in mini3_top replacement with
the identical BSCAN register map).

The verification ladder, every rung bit-exact:
1. `Design.cycleOpen` ≡ cycle-accurate Lean ISS (7 directed scripts, all
   registers, every cycle).
2. Emitted RTL in iverilog ≡ ISS ≡ **Rust lnp64 emulator** on a real
   assembled program (`loomcheck.s`: r1..r9 = 6,7,42,255,36,14,42,56,14).
3. **ZC702 silicon** ≡ all of the above: same program loaded through the
   core's own JTAG DDR window, run from PS DDR over the AXI HP master,
   identical rf/retire/pc readback (core at 12.5 MHz; emitted netlist
   routes at 13.4 MHz max).
4. **The NetBSD demo**: the §61 zero-BSCAN rump/NetBSD GEM image booted
   on the Loom core by the unmodified remote-fpga flow (power_cycle →
   fastload → trap servicer). The core walked the exact mini3 trap
   trajectory (first trap ERRNO_SET@0x4000b8; total inventory = the same
   4 one-shot boot traps at the same pcs), brought up native GEM0
   Ethernet, answered ping (5/5) and served a telnet shell — and after
   stopping the trap server (BSCAN quiet, xsdb dead): **ping 10/10, 0%
   loss**. NetBSD + native Ethernet, indefinitely, on a processor that is
   a Lean value.

## All-Lean SoC on silicon (2026-07-30)

The composed `lnp64mini_soc` (core ∥ HP master ∥ GP master via
`Design.prefixed/par/connect`, HP ownership mux in Lean wiring) is
silicon-proven: loomcheck rf bit-exact on the ZC702, and the full NetBSD
demo — boot with the same 4 one-shot traps, native GEM0, telnet, and
ping 8/8 at 0% loss after servicer stop with BSCAN quiet — behind a thin
wrapper holding only clock buffers, POR, BSCANE2+DR+CDC, and the PS7.
Every single-clock sysclk LUT in the bitstream is Lean-emitted
(13.11 MHz max route, 12.5 MHz clock).

## Fmax: 13.11 -> 31.69 MHz, core clock 12.5 -> 25 MHz (2026-07-30)

Semantics-preserving restructuring of `Machines/Lnp64mini/Core.lean` only
(the ISS is untouched, selftest and the iverilog soc tb are bit-identical):
every linear `foldr`/`foldl` mux/or/add chain became a balanced tree
(`priTree`/`orTree`/`addTree`/`actPriTree`), and the 20 `st`-dispatched FSM
rules were merged into one balanced dispatch rule. nextpnr-xilinx post-route:
`Max frequency for clock 'sysclk': 13.11 MHz` -> `31.69 MHz`, so
`lnp64mini_soc_top.v` now divides 200/8 = 25 MHz (`divc[2]`).

## Dual-core SMP: `lnp64mini_dual` (2026-07-30)

`Machines/Lnp64mini/DualSoc.lean` composes **two** cores onto one HP
master through a new Loom design, `HpArbiter`:

```
dual = (core.prefixed "c0_") ∥ (core.prefixed "c1_")
     ∥ (HpArbiter.prefixed "arb_") ∥ (HpMaster.prefixed "hp_")
     ∥ (GpMaster.prefixed "gpm_")
```

emitted with `lake env lean --run Machines/Lnp64mini/Emit.lean dual`
(`rtl/lnp64mini_dual.v`, 22,363 lines). The single arbiter is the memory
serialization point, so uncached shared DDR is sequentially consistent;
`rf`, the zero-page `dmem`, the UART rings and the 32 thread slots are all
core-private, and every shared datum lives in DDR.

Core extensions (all inert at 0, so `lnp64mini_soc` is byte-for-byte the
old machine): `res_kill`, `doorbell`, `hold`, `sc_fail` (D15 inputs) and
`wake_out`, `lr_req`, `sc_req`, `sc_pending` (registers). See
`Machines/Lnp64mini/DUAL_SPEC.md` for the design record and the deviations
— in particular why the LR/SC reservation had to move into the arbiter.

Wrapper (`lnp64mini_dual_top.v`): the mini BSCAN DR gains a core-select
region bit `dr[39]` (which is exactly `jtag_lib.tcl`'s `wr [expr 0x80|idx]`),
latched at UPDATE for both the cmd path and the readback mux, plus
wrapper register idx 56 = `CORE1_HOLD` (reset 1). ID = 0x53301018.

`tb_lnp64mini_dual.v` runs the three ladder-step-2 tests against a single
behavioral AXI3 slave (iverilog):

| test | evidence |
|---|---|
| shared-nothing dual `loomcheck` (core 1's copy at 0x4000) | both HALTED, retire 25/25, both `r1..r9 = 6,7,42,255,36,14,42,56,14`, private `dmem32=42` each |
| `smpcount.s` ×2, LR/SC on one shared DDR word, N=100 | `shared[0x10000]=200` = 2N, `r9=100` per core, 1 reservation kill |
| `smpcount.s` vs `smpcount_skew.s` (anti-phase, N=100 each) | `shared[0x10000]=200`, `r9=100` per core, **40** reservation kills — heavy contention, no livelock |
| `pingpong0.s`/`pingpong1.s` futex ping-pong over the doorbell | both HALTED, `r9=8` turns each, `wake_out` 8/8, 210/240 cycles genuinely parked in `S_WAIT` |
| `-DONLY_C0` (CORE1_HOLD asserted) | core 0 runs `loomcheck` to a correct EXIT; core 1 started but `retire=0`, `pc=0x1000`, `rf` all zero |

Ladder step 3 (Rust emulator, single core): `smpcount.hex` /
`smpcount_skew.hex` reach `r9 = r10 = N = 100` — the shared word is the
first `.data` symbol (0x10000), which is both ≥ 0x1000 (shared DDR on the
fabric) and backed by the emulator's flat-exec data image.

**[SUPERSEDED 2026-07-31 — D20 got the dual to 48 % and it placed; see
"Dual-core SMP on silicon" below. The paragraph is kept because the failure
and the two fixes are the useful record.]**

**Silicon: not yet at the time of writing; D19 (2026-07-30) got the dual from 93% to 78% but it still did not place.** With the
stock recipe (`synth_xilinx -flatten -nowidelut`) the dual originally came
out at `SLICE_LUTX 99072/106400 (93%)` and nextpnr-xilinx reported
*"Unable to find legal placement for all cells"*, because µVerilog's only
memory kind has asynchronous reads and the 1024×64 `rf` synthesized to
distributed LUTRAM while 138/140 block RAMs sat idle. `Loom/Hw/D19_SPEC.md`
fixes the *shape* of the `rf` read path (no Loom syntax/semantics change —
a decidable `Design.syncReadOkB` check plus two value-preserving edits in
`Core.lean`), and the regfiles land in block RAM.

Result: the dual drops to `SLICE_LUTX 83926/106400 (78%)` — but
`nextpnr-xilinx` **still** reports *"Unable to find legal placement"*, so
D19 was necessary and not sufficient.

**D20 (2026-07-31) closes it: the dual fits, routes and produces a
bitstream.** `DUAL_SPEC.md` §D20 — four of the six per-core thread-table
arrays (`tpc`, `tsleep`, `tp_arr`, `sigmask_arr`) become 32×64 Loom
memories with plain **asynchronous** reads (LUTRAM). `tstate` and `tfutex`
stay per-element, because those two are read at *every* index at once (the
priority encoders and the `FUTEX_WAKE` comparator bank). Nothing is
restaged: `memRead` is pre-cycle-state at a pre-cycle address (D9), which
is definitionally what the 32-way mux over 32 pre-cycle registers
computed — so every register keeps its exact cycle-by-cycle value.

| | pre-D19 | post-D19 | **post-D20** |
|---|---|---|---|
| soc `SLICE_LUTX` | 44567 (41%) | 37606 (35%) | **21524 (20%)** |
| soc `sysclk` post-route | 31.69 MHz | 32.53 MHz | **35.11 MHz** |
| dual `SLICE_LUTX` | 99072 (93%) | 83926 (78%) | **52134 (48%)** |
| dual `RAMB36E1` | 2/140 | 26/140 | 26/140 |
| dual placement | ERROR | ERROR | **legal — `OXC7_BUILD_DONE`** |
| dual `sysclk` post-route | — | — | **29.46 MHz** |

The whole ladder is unchanged and bit-exact through both passes — all six
iverilog testbenches produce byte-identical output, cycle counts included
(273 / 372 / 12540 / 14933 / 2014 / 346). See `DUAL_SPEC.md` §D20.

## Dual-core SMP on silicon (2026-07-31)

The dual (two composed core instances, arbiter-resident global LR/SC,
cross-core futex doorbell) passed all seven silicon ladder steps on the
ZC702: bit-exact dual loomcheck; LR/SC shared counter = 2N on hardware
(both phase variants); futex ping-pong 8/8; CORE1_HOLD live
(held: retire=0 → released: completes); the NetBSD demo unchanged on the
dual bitstream (same 4 one-shot traps, ping 8/8 BSCAN-quiet, telnet);
and coexistence — NetBSD serving native GEM0 on core 0 (~883k retires/s)
while core 1 ran an 8M-instruction workload to completion, ping 8/8
after, arbiter share cost ~31% with RTT unaffected. Numbers: 48% LUTs,
26 RAMB36, 29.46 MHz post-route at a 25 MHz clock.

## Epoch engine (LNP64 §3) — IN PROGRESS (2026-08-01)

`Machines/Epoch/` mechanizes the ISA's freshness primitive and refines a Loom
design to it. Status, stated exactly:

**Done and green.** Layer 1 `Protocol.lean`: the §3 protocol as a `TSys` with
T-E1…T-E6 proved and T-E7 (a use concurrent with a bump *may* succeed —
§3 permits it) exhibited as a run, plus an independent netlist
model-checking leg (`Bmc.lean`, 1-induction + BMC depth 2, LRAT certificates
re-checked in-kernel). Layer 2 `Engine.lean`/`EpochSoc.lean`: the engine as an
open Loom design composed with the dual core, one request port per referent
volume (volume identity wired, not addressed), engine-internal acks. Layer 3
`Refines.lean`: a `StutterSimulation` from the design to the protocol, with
T-E1/T-E2/T-E3/T-E4/T-E6 transported to every reachable state of the compiled
RTL **unconditionally over all input traces** — adversarial cores included —
and a cycle bound (D28): 15 cycles via the transported spec bound, 4 by a
direct ranking on the cycle-accurate system.

**Simulation.** `scripts/epoch_ladder.sh` passes: engine ladder byte-identical
to the FastEval oracle, and the cross-core demo (`tb_lnp64mini_epoch.v`) shows
core 0 bumping, core 1 reading `-STALE`, poison failing closed, GEM0 still
unreachable from core 1, bump latency 5 cycles.

**Silicon.** `lnp64mini_epoch_top.bit` builds (49 % LUTs, 33.63 MHz post-route)
and NetBSD boots dual-core on it. The engine answers over MMIO (its ID register
reads correctly and checks execute), but a check that returns `ok` in
simulation returns `-BADREF` on hardware; the leading hypothesis under
investigation is that BRAM initial contents do not survive the openXC7 flow,
which would make it an instance of the portability rule "never rely on memory
initial contents" (`LOOM_GAPS.md`). **The live demo is therefore not yet
demonstrated on silicon, and nothing here should be read as claiming it is.**

**Update 2026-08-01 (D30, then D31).** The hypothesis was right and sharper
than stated: BRAM initial contents *do* survive openXC7 — the three 512x32
epoch banks came up correct — and the bank that came up zero was `cell_flags`,
512x3, which yosys maps to distributed LUT RAM, whose image the configuration
path does not carry. Occupancy left memory (`b510caf`), the demo then ran on
silicon end to end (`EPOCH_SPEC.md` E13 acceptance, `47b2a4f`), and the defect
is now caught **inside the certified path**: `lake exe eqcheck` checks every
bank's reset image against the netlist, and `scripts/eqcheck_memfixture.sh`
keeps the pre-fix netlist as a regression fixture that eqcheck must reject,
naming the bank, with no board and no simulation (D31).
