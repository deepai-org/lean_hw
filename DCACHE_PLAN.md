<!--
Copyright (c) 2026 Kevin Baragona
SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
-->

# The D-cache, and why it is not the I-cache again

The instruction cache was easy in the way that mattered: guest text is
read-only, both cores fetch the same bytes, and a stale line can only ever be
*correct-but-old* for memory nobody writes. Invalidation exists (EXT-9's
generation tag, bumped on the commands that change translation) but it is a
safety net, not a coherence protocol.

None of that survives contact with data. The shipping configuration is
**dual-core SMP NetBSD**: two cores, one DDR, a futex word, a trace ring, a
GEM descriptor ring, and an `ldd`/`sdd` pair the kernel uses as its
synchronisation primitive. A private write-back D-cache on each core breaks
every one of those, silently, in a way that looks like a scheduler bug three
million retires later.

## What the design has to promise

1. **Atomics are not cacheable.** `LR.D`/`SC.D` and the futex path must reach
   DDR through the arbiter, because the arbiter is where the reservation and
   the SC-fail answer live. A cached LR is a lie about exclusivity. These
   bypass, unconditionally, and the bypass is structural (keyed on the
   opcode) rather than a range check somebody can get wrong.
2. **MMIO is not cacheable.** The GP aperture (`ea[31:20] == 0x0A0`) carries
   the epoch and capability engines; a cached read of a status word never
   completes a check. Also structural — the aperture decode already exists.
3. **The DMA window is not cacheable.** The GEM ring is written by hardware
   the core does not see. This is the one that would pass every selftest and
   fail on the board, because no simulation models the MAC.
4. **Write-through, no write-allocate.** It halves the interesting cases: a
   line is never dirty, so eviction is free and a core crash cannot lose a
   store. The cost is that stores run at DDR speed, which the store-heavy
   kernel paths will feel — but correctness first, and the read side is where
   the miss traffic actually is.
5. **Cross-core invalidation.** With write-through, core 0's store must
   invalidate core 1's copy of that line. The cheap version is a broadcast of
   the store address to the other core's tag bank; the honest version admits
   this is a coherence protocol and that "cheap version" is where coherence
   bugs live.

## The measurement that decides the shape

Before any of it: the I-cache's hit rate on a real boot is already
measurable, and the D-side's is not yet. `fpga/zc702/tb_lnp64mini_boot.v`
counts hits and misses on a real guest image. Run it for the data stream
first. If the D-side miss rate is dominated by the ring and the futex word —
the three things that must bypass anyway — then a D-cache buys much less than
the I-cache did, and the honest answer is to spend the fabric elsewhere. That
is a measurement, and it has not been taken.

Two things follow from the §70 retraction and belong here in advance: the
area cost of the D-cache must be an **A/B against a build of the same tree
without it**, not against any number written in a journal; and the "one more
rung" instinct should not outrun the question of whether the rung is worth
climbing. The user's direction was memory-first — L1/L2 and bursts over
Fmax — which argues for the D-cache. It does not argue for a D-cache that
breaks SMP.
