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

The substrate and machine test programs provide regression assets. The
present extended LNP64mini board head is not green.
Opcode agreement covers 70 shared opcodes, the emulator zero-trap gate passes,
and silicon shows zero traps, but the network is down. Current diagnostics
show core 0 halted and core 1 remaining in futex wait after 20 retires. Raw
console data shows guest byte writes replicated across 64-bit words at stride
eight, while guest C, clang, the Loom/ISS models, and emitted-RTL simulation
all specify packed single-byte writes. The next diagnostic is a known-pattern
write-and-halt probe with JTAG readback of the physical DDR location.

There is no accepted NetBSD, ping, telnet, SMP, epoch, or capability result
for the current head. The next accepted board result must reproduce the ladder
above and resolve this regression. `STATUS.md` is the repository-wide
current-state summary.

## CDC and reset boundary

Debug commands cross into `sysclk` through a latched-field toggle protocol.
The Lean CDC model proves the digital pulse contract under event spacing and
the stated synchronizer-resolution assumption. Analog metastability, MTBF,
placement, tear-tolerant counter reads, and reset electrical behavior remain
wrapper/physical obligations.
