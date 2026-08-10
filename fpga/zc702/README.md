# ZC702 FPGA integration

This directory contains the Xilinx ZC702 wrappers, constraints, simulations,
test programs, and debug scripts used with Loom-emitted RTL.

The board wrapper is outside the proved core. It contains vendor primitives,
clock and reset logic, BSCAN/debug shifting, clock-domain crossings, PS7/AXI
wiring, and pins. Loom owns the connected single-clock logic represented by
the emitted module; Yosys, nextpnr-xilinx, bitstream tools, programming, and
the physical board are corroborated rather than proved.

## Maintained designs

- Substrate smoke and soak designs exercise closed and open EDSL modules.
- `lnp64mini_soc_top.v` integrates the single-core SoC.
- `lnp64mini_dual_top.v` integrates the dual-core arbiter and masters.
- `lnp64mini_epoch_top.v` integrates the epoch/capability extension path.

Related contracts are in `Loom/Hw/CDC_SPEC.md`, the machine specifications,
and `TRUST.md`.

## Local source and simulation flow

From the repository root:

```sh
lake build
lake env lean --run Machines/Substrate/Emit.lean selftest
scripts/epoch_ladder.sh
scripts/capwalk_ladder.sh
```

LNP64mini emission is selected through `Machines/Lnp64mini/Emit.lean`; the
testbenches in this directory exercise the emitted modules with behavioral
AXI peers. Optional Icarus, Yosys, CaDiCaL, and openXC7 steps require those
tools on the host.

The dual wrapper's board-only BSCAN probes are generated from the single list
in `Machines/Lnp64mini/DebugMap.lean`:

```sh
lake exe debugmap          # regenerate board/lnp64mini_debug_map.{vh,tcl}
lake exe debugmap --check  # fail if the checked-in include is stale
```

Typed taps validate their emitted dual-core output names at build time. Raw
level and first-event sticky taps are the deliberately unverified escape hatch
for throwaway probes: they generate wrapper state, CDC sampling, port wiring,
and read decode without adding ISS or lockstep state. The generated include
and observed board values remain outside the release theorem.
Register-only typed EDSL expressions derive their child-port dependencies and
wrapper logic automatically. The current map uses this for a sticky
`running ∧ halted` predicate at BSCAN index 54; it reuses the top's existing
running/halted bindings instead of connecting either port twice. Its sticky
valid bit generates a persistent core-1 halt request, ORed into the existing
S_F0-safe CORE1_HOLD path and cleared by reset. `scripts/debugmap.sh` runs a
small behavioral test of per-core triggering, persistence, and reset in
addition to elaborating the actual emitted dual and board top.

A typical openXC7 build host runs the equivalent of:

```sh
oxc7/build_oxc7.sh <top> <constraints.xdc> <wrapper.v> <emitted.v>
```

Programming and BSCAN readback use the local XSDB/JTAG environment. Those
host-specific tools and hardware access are not packaged by this repository.

## Acceptance

A current board claim requires all of the following from the same source
revision and generated artifacts:

1. source/FastEval/ISS agreement for the selected design;
2. emitted-RTL simulation against the same workload;
3. memory-deliverability and configured equivalence checks;
4. successful place-and-route with positive timing margin;
5. bitstream programming and expected debug readback; and
6. the live workload, including network behavior where claimed.

## Current status

The current dual-core LNP64mini head passes the full NetBSD mission workload
on one accounted bitstream and guest image. Ping completes 4/4; `uname` and
`echo e2e-ok-through-gate` return through gate 1/domain 1; and the shmif
driver uses the domain-2 path. The same artifact includes direct generic
`MUL`, the sentinel gate ABI, and the current CDC snapshot structure. The
accepted image uses roots `0x913000` and core-1 entry `0x8cae00`.

The accepted build uses the stock-openXC7-compatible `-nodsp` path: 59,035 of
106,400 LUTs (55%), routed at iteration 17, with a reported 32.86 MHz
`sysclk` maximum. The host's openXC7 0.8.2 rejects an unused terminal DSP48
`PCOUT`; openXC7 0.9.2 contains the upstream fix, but a DSP-enabled artifact
has not replaced the accepted LUT-mapped result. `STATUS.md` is the
repository-wide current-state summary.

## CDC and reset boundary

Debug commands cross into `sysclk` through a latched-field toggle protocol.
The Lean CDC model proves the digital pulse contract under event spacing and
the stated synchronizer-resolution assumption. Analog metastability, MTBF,
placement, tear-tolerant counter reads, and reset electrical behavior remain
wrapper/physical obligations.
