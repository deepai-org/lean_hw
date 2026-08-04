# Synchronous-read memory discipline

`Loom/Hw/SyncRead.lean` defines the decidable shape check used to make
synchronous FPGA and SRAM reads explicit in a `Design`.

## Contract

A synchronous read site must feed a declared register in the supported
one-cycle shape. Loom expressions observe pre-cycle memory contents and rule
writes commit at the cycle boundary. The corresponding emitted register can
therefore be absorbed into a block-RAM read port without changing the stated
cycle behavior.

Emission applies the check; it is not an optional machine-local lint. The
supporting results connect the Boolean checker to its propositional form and
the run semantics.

## Why it exists

An arbitrary combinational `memRead` commonly maps to LUTs, mux trees, or
flip-flops. Merely adding a register after such a read does not establish the
intended latency or guarantee block-RAM inference. The D19 discipline makes
the latency-bearing structure visible before synthesis.

LNP64mini uses this shape for the memory paths selected for block-RAM
inference. Target suitability is checked separately with `MemTarget`; actual
mapping is confirmed from synthesis and, where supported, by the post-
synthesis checker.

## Boundary

The check does not prove a vendor will choose a particular primitive, model
analog timing, or resolve simultaneous cross-port read/write collisions for
every technology. Loom's language semantics remain the source-level
last-write-wins/pre-cycle-read contract. A target whose collision behavior
does not implement that contract needs a target-specific proof or exclusion.
