# EXT-9 plan: 32KB I$ + 32KB D$ (BRAM), staged (2026-08-07)

Design plan produced against the §69 area ceiling and the memory-first
direction. Summary of record; the numbers were derived from Core.lean's
actual FSM and the D19/D38 disciplines.

## Organization
- **I$**: direct-mapped, physically-indexed/tagged on `ddrPc`.
  Stage 1: 1-word (8B) lines — 4096 lines, index `ddrPc[14:3]`, tag
  `{v, ddrPc[31:15]}` (18b). NO AXI change (miss = today's single-beat read).
  Stage 5 (last): 32B 4-beat lines via an `m_arlen` input on HpMaster
  (today a constant-0 register) + beat counter; fill writes beats straight
  into BRAM (no line buffer).
- **D$**: direct-mapped, **write-through, write-allocate, 1-word lines,
  permanently**. The RMW store path already materializes the full merged
  64-bit word in `S_DST` (`st_merge`), so write-through is one extra funnel
  triple; no dirty bits, no writeback machinery, ever. DDR stays the truth
  (host JTAG reads stay correct with zero work).
- **Bypasses** (never consult the cache): LR reads (reservation must be
  taken at the arbiter), the `S_FTX1` futex-compare read, and an
  **uncacheable window** (`uncache_base`/`uncache_limit` regs, new cmds)
  covering the shmif ring / DMA grant `0x20e000–0x30e000`. SC success
  updates the line; SC failure invalidates that index.
- BRAM: ~20 RAMB36 total per cached core (138 idle). D19: all four arrays
  in `syncReadMems`, one latch site each (`ic_tag_q`…), one funnel write
  site each (D38 single write port). All-zero reset images (valid in the
  tag word) — D30/D37 trivial. Flash invalidate is a 12-bit **sweep**
  engine (zeroing-clone), never a 4096-bit register.

## FSM
New states from 21: `S_IC` (I$ tag check), `S_DC` (D$ check), stage-2
`S_FB`. `s_f0` latches tag+data → `S_IC`; hit = 3-cycle fetch, miss =
today+1. `s_ex` DDR-load/RMW-read arms latch → `S_DC`; hit skips the AXI
round trip. `s_dst` adds the write-through funnel write. New cmds:
`CMD_IC_INV=70`, `CMD_DC_INV=71`, `CMD_UNCACHE_BASE/LIMIT=72/73`; `cmd 13`
reset triggers both sweeps.

## Transparency (the proof shape)
1. EDSL≡ISS lockstep unchanged in kind: the ISS models the caches
   cycle-exactly (arrays + new st codes); MatrixTheorem stays.
2. **Transparency is an ISS-vs-ISS theorem**: cached vs uncached systems
   agree on all architectural state at every `S_F0` boundary, over the
   generated matrix, by `native_decide` (the W5 pattern). Invariant CInv:
   every valid line equals the DDR word it names; write-through preserves
   it, fills establish it, sweeps shrink it, bypasses never consult it.
   CInv's external-writer premise is discharged by the coherence story
   below, not by Lean — stated, not glossed.

## Coherence (honest table)
- Host loader: `cmd 70/71` in fastload/boot scripts while the core is
  parked (same shape as TLB shootdown).
- GEM DMA / ring_pump: PS-side writes never cross the fabric; the ring is
  the uncacheable window anyway — structurally never cached.
- Other core: guest never writes text → **I$ on both cores is safe day
  one**. D$ on dual tops waits for stage 4's arbiter snoop broadcast
  (the arbiter already sees every write; registered `snoop_wr/addr` to the
  other core's invalidate funnel). Until then D$ is single-core-top only,
  behind an enable defaulting off.
- LR/SC + futex bypasses keep the serialization-at-the-arbiter argument
  untouched.

## Staging
1. I$ 1-word, single-core top — **prerequisite for translated fetch**
   (the TLB then sits on the S_IC miss arm, off the hit timing path;
   I$ becomes per-domain — flash-invalidate on map changes, or domain in
   the tag).
2. I$ on the dual top + boot-script invalidates; board soak.
3. D$ write-through single-core + bypasses + uncacheable window.
4. Arbiter snoop → D$ on dual.
5. Burst lines (the only HpMaster/ISS-DDR change).

## Area (~1.4–2.1k LUTs total; synth per rung against the dual top before
writing the next rung — §69's rule applied literally)
I$ ctl ~300–450; sweep ~100–150 (shared); D$ ctl ~400–600; uncache window
~100; snoop ~150–250; burst ~200–350; cmds ~100.

## Test ladder
Build gates (syncReadOk, realizableOnB xc7+asicSram) → ISS-vs-ISS
transparency theorem → EDSL≡ISS matrix + directed cache battery (cold/hit/
alias-evict/store-load/subword-through-hit/inval-mid-run/LR-SC-cached/
futex-cached/uncacheable/sweep-during-hold) → RTL leg (opdiff_rtl) →
tb_lnp64mini_boot with the real image + invalidate cmds → yosys RAMB36
count per rung (a wrong count = D19 silently demoted a cache to LUTRAM) →
board (retire-rate delta measured, dual zero-trap, telnet soak,
authority_demo, power-cycle regression).

## Files
Core.lean +450–650; Iss.lean +200–300; Harness.lean +200–300;
HpMaster.lean +80–150 (burst rung only); HpArbiter/DualSoc +60–100
(snoop rung); EXTEND_SPEC.md EXT-9 section; boot/fastload scripts ~10
lines each.

## Area projection against the ceiling (W6 model, 2026-08-07)

Run before writing a line of it, which is what the cost model is for:

| rung | predicted sites | % of xc7z020 |
|---|---|---|
| epoch top today | 56 791 | 53 % |
| + I$ stage 1 control (plan's 450 LUT upper bound) | 57 358 | 53.9 % |
| + invalidate sweep engine | 57 547 | 54.1 % |
| + D$ control (600 upper bound) | 58 303 | 54.8 % |

BRAM: 29 macros used today; I$ 10 + D$ 10 → 49 of 140. Free, as expected.

**Read this as risk, not permission.** The calibrated closure threshold is
50 % and the epoch top is *already past it* — the seed that eventually routed
(seed 11, 25.01 MHz against a 25 MHz board clock) took four attempts. Adding
1.8 points of LUT on top of that is not obviously survivable, and the model
explicitly cannot tell us: it did not separate the design that routed from the
one that did not (§69).

So the sequencing follows the numbers rather than the wish list:

1. **Build the I$ rung on the DUAL top first** (48 %, routed first try at
   30.43 MHz, ~4 points of headroom). That validates the cache against a part
   that will actually close, and it is the rung translated fetch needs.
2. Only then attempt it on the epoch top, and expect to pay for a seed.
3. If the epoch top will not take I$ + D$ together, the honest split is the
   one Appendix F already gestures at: engines and caches need not be the
   same core.

The area-reduction work (`LOOM_GAPS.md` W6 / the hotspot analysis) is
therefore on the critical path for the *epoch* variant, not for the caches
themselves.

## Rung 1 delivered (2026-08-07)

**PASS 20260807-135454**: NetBSD dual-core, native GEM0, BSCAN quiet, on the
I-cache build. Off-board: all 13 selftests, RTL ≡ ISS on 596 generated
programs. Synthesis: **46 RAMB36 (+20, exactly 10 per core)** — both banks in
block RAM on both cores, which is the D19/D38 discipline paying out rather
than being asserted. `realizableOnB` holds on `xc7` and `asicSram`. Build:
dual top, **first routing seed, 29.34 MHz, 51 %**.

Three defects the toolchain caught during construction, recorded because the
point of the machinery is that it fires while you work:

1. W1.1's emit gate refused the design when the sync-read latches were read
   but never declared — before any RTL existed.
2. The EDSL/ISS lockstep found the fill writing `(tag&1) << 17` (the tag
   shifted into the valid position), surfacing as `st: edsl=S_FW iss=S_RD` —
   one model hitting where the other missed.
3. The `Oracle` closed-list check forced the oracle to learn the new banks
   (`UNDECLARED-UNMODELLED ic_tag[...]`) instead of silently comparing less.

**Area, measured against the projection — with a correction.** A controlled
A/B (same wrapper, same seed, cache present vs absent) says the I-cache costs
**essentially nothing in LUTs**: 44 112 cells / 55 234 sites without it,
43 999 / 55 129 with it — 105 sites *fewer*, i.e. noise — plus 20 BRAMs. The
W6 projection (+0.5 pp) was therefore right, and the packing expansion is
near-constant across the pair (1.252 vs 1.253).

The first version of this section claimed +3.8 pp and "packing is not a
constant". Both were artifacts of comparing the new build against a
utilization figure recorded in the journal for a *different* build instead of
rebuilding the baseline — the same error `boot_sim.sh`'s own header warns
about for simulation. The correction is the lesson: **an A/B needs both legs
built, in area exactly as in behaviour.**

**Still open on this rung**: the ISS-vs-ISS transparency theorem (today the
claim is backed by the generated matrix, not a proof over it), and the
retire-rate delta — the number that justifies the memory-first direction.
Note the measurement is conservative by construction: the cached build routes
at 29.34 MHz against the uncached 30.43 MHz, so a speedup has to overcome a
3.6 % clock disadvantage before it shows at all.
