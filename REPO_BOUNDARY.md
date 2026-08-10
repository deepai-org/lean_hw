# What lives here, and what lives in `lnp64`

## The rule

This repository owns Loom, LNP64mini and the engines, and everything that
drives those machines on the board: wrappers, loaders, the trap servicer, and
acceptance orchestration under `fpga/zc702/board/`.

The `lnp64` repository owns the architecture and software: the specification,
opcode tables, LLVM backend, assembler, emulator, guest images, and derived
conformance programs.

## Dependency direction

The dependency is one way: this implementation may consume its architecture
and toolchain from `lnp64`; the architecture repository must not depend on one
implementation. Cross-repository gates resolve `lnp64` through
`scripts/lnp64_root.sh` and `LNP64_ROOT`.

## Board ownership

Board scripts program `lnp64mini_*` bitstreams and drive command indices
defined by `Machines/Lnp64mini/Core.lean`, so they live with the machine. They
may consume `lnp64` guest images and binaries, which preserves the dependency
direction.

The repository copy is authoritative. `scripts/board_sync.sh` deploys every
board file and verifies its digest. Board-host locations are centralized in
`board_env.sh` and `board_env.tcl`; deployment identity, roots, tool paths,
logs, and artifacts are configuration rather than developer-specific paths.
