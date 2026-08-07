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

**Taken, 2026-08-07.** `tb_lnp64mini_boot.v` now models a D-cache of the
I$'s own shape (4096 x 8 B direct-mapped, index `addr[14:3]`) over the real
guest image's read channel, classifying a read as a fetch iff its
window-relative address is the pc — exact here, because this tb runs identity
translation. On the boot to the `subr_vmem` divergence:

```
IC  hits=168516 misses=13263 rate=92%
D   reads=86221 hits=82263 misses=3633 rate=95%
    bypass(out-of-window)=325   writes=31992
```

The hedge above was wrong, and the measurement is why it is worth taking one.
The bypass traffic is **325 reads out of 86 221** — four thousandths. The
data stream is not dominated by the ring and the futex word at all; it is
ordinary kernel data with 95% reuse at 32 KB, and a D-cache would remove
**82 263 DDR reads**, roughly half again as much bus traffic as the I-cache's
168 516 fetches. On this tb's timing that is worth about a third of the
remaining cycles. Build it.

Three honesty limits on that number. It is a **trace model**, not fabric: it
says what a cache of that shape would have done to this sequence, not what
one placed and routed will do. It is **single-core** — this tb runs core 0
alone, so the 95% has never met an invalidation from the other core, and
rung 5 below is exactly the part it cannot predict. And the tb's DDR is a
fixed single-beat model, so the cycle share is optimistic against a board
whose real latency is longer and burstier. What the measurement settles is
the *direction*, which is what it was for.

Two things follow from the §70 retraction and belong here in advance: the
area cost of the D-cache must be an **A/B against a build of the same tree
without it**, not against any number written in a journal; and the "one more
rung" instinct should not outrun the question of whether the rung is worth
climbing. The user's direction was memory-first — L1/L2 and bursts over
Fmax — which argues for the D-cache. It does not argue for a D-cache that
breaks SMP.
