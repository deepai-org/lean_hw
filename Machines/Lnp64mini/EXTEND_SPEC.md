# Extending lnp64mini toward the architecture — binding plan

Goal: keep the DUAL core, add **Gates, Domains, Park/wake directory,
Preemption tick, Fail-stop/poison, VMA+MMU, Cross-domain capability
transfer**, and **keep the NetBSD telnet demo working** throughout.

Normative source: `/home/ubuntu/lnp64/lnp64_isa.md` (READ-ONLY; spec of
record). Precedents to copy: `Machines/Epoch/EPOCH_SPEC.md` and
`Machines/CapWalk/CAPWALK_SPEC.md` — every addition is a Layer-1 protocol in
Lean, a Layer-2 Loom design, and (where affordable) a Layer-3 refinement.

## The two hard constraints

1. **The demo is the regression bar.** After every increment:
   `scripts/epoch_ladder.sh`, `scripts/capwalk_ladder.sh`, the mini
   testbenches reproducing DUAL_SPEC's numbers, and — before anything is
   called done — NetBSD booting on the board and answering telnet + ping.
   A change that breaks the demo is reverted, not "fixed later".
2. **Fmax is nearly exhausted.** `lnp64mini_cap` post-routes at **25.89 MHz
   against a 25 MHz clock** — under 4 % margin. Anything on the load/store
   path (i.e. the MMU) will eat it. Rule: if post-route Fmax drops below the
   clock, **halve the clock and report the cost**, do not silently break
   timing. Measure Fmax on every increment; a design that fits but does not
   time is not done.

## Budget (measured anchors, yosys LUT cells)

dual+epoch+capwalk = ~30k ≈ **56 % placed**; each engine so far is 330–670
LUT. We are CORE-bound, not engine-bound — but the MMU is the exception
because it touches the datapath, not just a table. Estimates: domains ~1.5k,
gates ~1.5k, park/wake ~1k, preemption ~0.3k, fail-stop ~0.3k, transfer ~1k,
**MMU/TLB ~3k and the only one with Fmax risk**. Target ≤ 85 % placed.

## The MMU and the demo — the guest is TRANSLATED, not faked

Rejected: giving the NetBSD domain an identity VMA so translation is present
but does nothing. That proves the hardware exists and the architecture does
not. It also leaves dark one of §3's eight epoch-cell referents — *cached
translation*, whose cell `map.protect`/`munmap` bumps — because with an
identity map there is nothing to shoot down.

**The guest runs under a real, non-identity mapping.** Consequences, all of
which are work and none of which are optional:

* **Layout.** The rump image is linked flat (text 0x400000, data ~0x8db000,
  stacks 0x1700000–0x2000000, shmif ring 0x20e000, GEM slab 0x2000000, native
  heap 0x4000000+192 MB). Under translation these become *virtual* addresses
  and the loader must place each region at whatever physical frames the
  mapping assigns. `fastload.tcl` and the servicer write PHYSICAL DDR, so the
  page table and the loader must agree; build the table as part of the load,
  not in the guest.
* **Pages must be genuinely non-contiguous** for at least part of the image,
  or the "mapping" is an offset in disguise and we are back to faking it.
* **DMA is the one named physical window.** GEM0 is a bus master: the NIC
  reads descriptors and frames at PHYSICAL addresses, so `gem_core.c`'s
  `PHYS(g) = 0x10000000 + g` cannot survive translation unchanged. This is not
  a cheat if it is *named*: §15 has device windows with IOVA metadata, so the
  DMA region is an explicitly declared mapping the domain was granted, and the
  guest asks for a buffer's physical address instead of computing it. Write it
  down as a grant, never as an assumption.
* **The payoff, and the reason to do it this way:** with real mappings we can
  **revoke one out from under running NetBSD** — bump the VMA's epoch cell,
  the cached translation dies, the next access fails closed — which is §15 and
  §3 meeting on silicon, and is a demo nobody can run today.

**Staging (each stage keeps the demo alive):**
* **A — hardware first.** TLB + walker + VMA tables, MMU bypassed for the
  running guest. Proves the mechanism, risks nothing, gives Fmax data early.
* **B — move the guest in.** Real page table built at load time, image placed
  per the mapping, `gem_core` using the granted DMA window. This is the risky
  stage; it is where the demo can break and where the regression bar bites.
* **C — the payoff.** Shoot down a live mapping under the running guest and
  show the fail-closed, with the latency measured against the D23 bound the
  way the epoch demo already does.

## Build order (dependencies are real; do not reorder casually)

1. **Preemption tick** (Law 5). Smallest, independent, and it closes a known
   fidelity gap (`PORTING_SPEC.md`: the scheduler is cooperative). `S_F0` is
   already the instruction boundary; the sleep scan is already a timebase.
   Risk to the demo: a preempted rump guest must still work — this is the
   first real test of the regression bar.
2. **Domains** — a domain id on the core, per-domain capability/VMA table
   roots, and the tag the datapath compares. Everything below references it.
   The NetBSD guest becomes domain 0 and must not notice.
3. **Fail-stop / poison plumbing** — the architected disposition every later
   engine feeds (§3 poison, Appendix F's fail-stop rule). Small, and cheaper
   to put in before there are four clients than after.
4. **Park/wake directory** (Appendix F #6) — §3 calls it "the epoch machine's
   client annex"; grow it from mini's existing futex + the cross-core
   doorbell rather than building fresh.
5. **Gates** (§9, Law 1) — frame push/pop, the continuation stack, and the
   delivery-targeting rule. The crown jewel and the reason domains matter.
6. **Cross-domain capability transfer** — send/recv/gate re-key; needs
   domains (2) + gates (5) + the existing CapWalk engine.
7. **VMA + MMU** (§15) — last, because it is the Fmax risk and the only item
   that touches the load/store path. Identity for domain 0 per above.

## Per-increment definition of done

Lean protocol + theorems (traced to ISA sentences) · Loom design ·
FastEval selftest · iverilog leg byte-identical to the oracle · byte-identical
re-emit of every design not deliberately changed · `lake exe audit` green ·
**measured Fmax and placed utilisation** · the demo still boots and serves.
Deviations appended here, never silently narrowed.

## Explicitly NOT in scope

FP profile (§14), vector profile (§18), the Mover/DMA (§11), state-stream
round-trip (§16.8), and the full 2^24-slot capability table (the cache+DDR
design stands).
