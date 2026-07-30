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
