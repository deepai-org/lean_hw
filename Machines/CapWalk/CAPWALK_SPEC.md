# Capability table walk + fill — spec-to-silicon plan (LNP64 §2.2, Appendix F machine 2)

Normative source: `/home/ubuntu/lnp64/lnp64_isa.md` §2.2 ("How a capability is
unforgeable — the handle model, not tagged memory") and Appendix F row 2
("Capability table walk + fill … the fill path is a page-walker-class
sequencer"). `/home/ubuntu/lnp64` is READ-ONLY here: it is the spec of record,
not a repo this campaign edits.

This is the second Appendix-F machine. The first (Epoch, §3) is done
spec-to-silicon with its refinement discharged; this one **validates against
it** — §2.2's two invalidation mechanisms, the slot's embedded cell and the
shared lineage cell, *are* §3 epoch cells. Engine #2 lands on engine #1.

## Why this engine, and why it is the hard one

Forced by the encoding, not chosen: a handle is `bit63=0 | slot[62:39] |
epoch[38:0]`, i.e. **2^24 slots per domain**. No on-chip table holds that, so
the entry store spills to DDR and the design becomes cache + walker + fill —
the page-walker-class sequencer Appendix F names.

And the security asymmetry that makes it the right forcing function for the
adversarial-state doctrine (`Machines/Epoch/EPOCH_SPEC.md`, SUPERSEDING
DOCTRINE):

* For the **epoch** engine, adversarial DDR was harmless: a stale value fails
  the freshness check by construction, so safety needed nothing of memory.
* For **capabilities it is not**. An entry carries *rights*. A forged or
  corrupted entry served by memory is **rights amplification** — the one thing
  §2.2 exists to make impossible ("no instruction turns data into authority,
  and arithmetic on a handle cannot widen rights").

So this engine cannot get zero-assumption safety for free; it must **earn** it
with an authenticated backing store (task #41): MAC/Merkle over the spilled
table, epoch-bound against cross-epoch replay, verified on fill. That is the
whole point of doing this engine second.

## What §2.2 fixes (do not re-derive; port these exactly)

Handle layout: `bit63 = 0`, `slot = bits[62:39]` (24), `epoch = bits[38:0]`
(39). Epoch `0` is reserved-invalid, which makes `u64 0` unconstructible as a
live handle — **the null handle is an encoding theorem, not a convention**, and
that theorem should be *proved*, not commented.

Entry fields (hardware-owned, no instruction writes them directly): class,
rights, range, the slot's embedded epoch cell, a shared lineage-cell
reference, lifetime class `{PERSIST, DROP_ON_STATE_REPLACEMENT}`, `SEALED`,
reserved bits.

Check order on every use — §2.2 says "Checks occur in that order. No section or
operation may choose a different condition for the same predicate":
1. slot occupied
2. handle epoch == slot-cell epoch
3. lineage-cell epoch current
4. required rights present
5. range/class valid

Condition mapping, total and universal:
* `-BADREF` — null where not admitted; malformed/out-of-range slot index; an
  **empty slot whose current embedded epoch nevertheless matches**; a live
  entry of the wrong object/interface class.
* `-STALE` — any embedded slot-epoch mismatch (drop, move, reuse) **or**
  shared lineage/stamp epoch mismatch.
* `-DENIED` — valid live reference lacking required rights/range.

## Layers (same ladder as Epoch)

1. `Protocol.lean` — the §2.2 use-check and the fill transaction as a
   `Loom.TSys`, over an abstract entry map. Theorems, each traceable to a
   §2.2 sentence: **T-C1 null unconstructible** (the encoding theorem);
   **T-C2 check order** (the outcome function is exactly the stated priority,
   decidably, exhaustively at small widths); **T-C3 no amplification**
   (`cap_dup` narrows monotonically — no reachable state has an entry whose
   rights exceed its authorizing entry's); **T-C4 revocation reaches every
   descendant** (one lineage-cell bump fails all entries referencing it —
   this is where §3's T-E1 is *used*, not restated); **T-C5 reuse safety**
   (a stale handle to a recycled slot fails forever); **T-C6 fill fidelity**
   (a filled entry equals the backing entry it claims to be — the hook the
   authenticated store discharges).
2. `Engine.lean` — hot cache (on-chip, the checking interface) + walker + fill
   sequencer. Per the doctrine: **the safety-critical check runs against
   on-chip state; DDR holds re-validatable bulk behind the fill contract.**
   The engine owns the cache and the tags; software may only present handles.
3. `Refines.lean` — StutterSimulation to Protocol, transporting T-C1..T-C5
   unconditionally over input traces (adversarial cores AND adversarial
   memory, once #41's authentication is in). T-C6 is the seam where the
   memory assumption is discharged rather than assumed.
4. Silicon — on the dual core beside the epoch engine; demo: a domain holds a
   capability, `cap_revoke` bumps the lineage cell, the holder's next use
   fails `-STALE` within the measured bound, and a deliberately corrupted
   backing entry is *detected* rather than obeyed.

## Scope for v1 (name what is out; do not silently narrow)

IN: use-check against a cached entry; cold fill from a backing store; slot
drop (embedded bump) and `cap_revoke` (lineage bump) via the epoch engine;
`cap_dup` with narrowing.
OUT, staged and named: cross-domain transfer (`send`/`recv`/gate re-key — it is
Appendix F machine 2's *transfer* half and wants the endpoint machinery),
`SEALED` delegation refusal, lifetime classes / `dreplace.commit`, and the
Merkle *tree* (v1 authenticates entries individually; the tree is a scaling
optimization, not a safety change).
