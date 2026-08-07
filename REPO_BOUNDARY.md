# What lives here, and what lives in `lnp64`

Settled 2026-08-07, after a review found the same trap servicer checked into
both repos and a 10k-line RTL tree in `lnp64` that nobody compared to
anything.

## The rule

**This repo owns the machines:** Loom (the verified EDSL, compiler and
printer), `lnp64mini` and the engines, and **everything that drives them on
the board** — bitstream wrappers, `jtag_lib.tcl`, the loader, the trap
servicer, and the acceptance orchestration under `fpga/zc702/board/`.

**`lnp64` owns the architecture and the software:** the frozen spec, the
opcode and func tables, the LLVM backend, the assembler, the emulator, the
NetBSD guest images, and the derived Appendix D conformance suite.

## The dependency is one-way: here → `lnp64`

An implementation may depend on its specification and toolchain; a
specification must not depend on any one implementation. Six gates here
reach into `lnp64` for the assembler, the emulator, the built clang and the
ISA tables — deliberately. **Nothing in `lnp64` references this repo**, and
its gates must pass with this repo absent.

All six say where `lnp64` is exactly once, via `scripts/lnp64_root.sh` and
`LNP64_ROOT`, instead of six independent guesses at `../lnp64`.

## Why board bring-up lives here and not with the guest

`netbsd_up.sh` and friends look like guest work — they boot NetBSD — but
each programs an `lnp64mini_*` bitstream and pokes BSCAN command indices
that are *defined in* `Machines/Lnp64mini/Core.lean`. Authority follows the
definition. Keeping the orchestrator beside the guest while the surface it
drives is defined here is what produced the §69 incident: the board host's
copies had drifted from both repos, and the fix had to be reconstructed from
a running machine.

Those scripts consume `lnp64` artifacts (the guest image, the trap-server
binary), which is the allowed direction.
