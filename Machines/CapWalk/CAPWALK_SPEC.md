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

## Deviations (Layer 1, recorded against the plan above)

Every item below is a departure from, or a refinement of, this file's
§"Layers" item 1 as mechanized in `Machines/CapWalk/Protocol.lean`. Nothing
was silently narrowed, and nothing is a `sorry` or an axiom: every theorem
named here is proved with the 3-axiom kernel closure (`propext`,
`Classical.choice`, `Quot.sound`), reported by `#print axioms` at the foot of
the file and re-checked by `lake exe audit`.

**C1 — the entry is split: embedded cell on-chip, static fields spillable.**
§2.2 lists "the slot's embedded epoch cell" among the entry fields. The model
puts it in `St.cell : Fin N → Epoch.Protocol.Cell W` and everything else in
`EntryData`, which is what `St.backing` holds. This is `EPOCH_SPEC.md`
§"Design decision" rule 1 (the safety-critical check runs against on-chip
state) applied at the point where it first bites: freshness never spills.
§2.2's "slot occupied" is `Cell.occupied` — the same field §3's empty-slot
clause reads (Epoch D1), so occupancy is not duplicated either.

**C2 — T-C3 is qualified by the authorizer's *incarnation*, and must be.**
`CAPWALK_SPEC.md` above says "no reachable state has an entry whose rights
exceed its authorizing entry's". The derivation record `EntryData.parent` is
§2.2's `{slot, epoch}` pair, not a bare slot number, and

```
T_C3_no_amplification : Reachable s → (s.ent i).parent = some (j, e) →
    e = (s.cell j).epoch → rightsSub (s.ent i).rights (s.ent j).rights = true
```

carries the hypothesis `e = (s.cell j).epoch`. The unqualified statement is
**false**, and stating it would be the silent narrowing this file forbids:
drop slot `j` and mint a *different, narrower* capability into it, and the
old descendant's rights may exceed the new occupant's — but that occupant is
not its authorizing entry, it is a different capability that happens to reuse
the slot number. §2.2's own handle discipline says a slot number without its
epoch names nothing. The invariant that makes this airtight is `Inv.parentLe`
(a derivation record never runs ahead of its authorizer's cell), together
with the model's requirement that a mint bump the destination cell (C3), so
the qualified antecedent is unreachable for a superseded incarnation rather
than merely unproved. `T_C3_narrows` gives the full order (rights, range,
class, **and the same lineage cell and stamp**), and `T_C3_no_forge` is
§2.2's "arithmetic on a handle cannot widen rights" as a statement about
`use` over *all* handle values.

**C3 — minting bumps the destination slot's embedded cell.** §2.2 names the
bump only on drop. The model's `cap_dup` requires the destination slot to be
empty (`occupied = false`) and not retired (`dead = false`) and installs at
`satInc` of its current epoch, i.e. a fresh incarnation. This is what §2.2's
"one slot retires only after 2^39 reuses" counts, and it is load-bearing for
C2. `EntryData.parent` itself is additive: §2.2 does not name a derivation
field, but it is engine-owned state no instruction writes, and without it
"minted only from an authorizing capability" is unstatable.

**C4 — saturated death is a freshness-class failure (`-STALE`).** §2.2's
condition mapping gives a retired slot no error value of its own. `outcome`
returns `-STALE` for `dead`, immediately after the embedded-epoch compare
(step 2). Inherited verbatim from Epoch D3.

**C5 — there is no corruption event; T-C6 is the fidelity invariant.** v1 has
`fill`/`evict` and the invariant `Inv.fidelity : backing i = ent i`
(`T_C6_store_faithful`), from which `T_C6_fill_fidelity` (a fill installs
exactly the backing entry, and leaves the abstract table unchanged) and
`T_C6_fill_use_neutral` (the fill/evict pair is observationally neutral)
follow. This is exactly the hook §"Why this engine" names: **the model does
not yet quantify over an adversarial store**, and an authenticated backing
store (task #41) is what will let `Inv.fidelity` be *established* rather than
assumed. Until then T-C6 is a contract on the store, and it is stated as one.

**C6 — v1's invalidations are `lazy`, so `Outcome` has four constructors.**
`-POISONED` is a §3 bump *policy*, not a §2.2 condition; `Inv.linClean`
records that no lineage cell is ever poisoned in v1, so the capability layer
observes only §2.2's `{ok, badref, stale, denied}`. A v2 issuing `poison`
bumps on `cap_revoke` must widen `Outcome` and re-derive T-C4's sharp form
(`T_C4_revocation_is_stale`); the `≠ ok` form
(`T_C4_revocation_reaches_descendants`) already survives.

**C7 — `SEALED` and `lifetime` are carried, not checked.** As §Scope stages
out. They are fields of `EntryData` so that a v2 delegation refusal and
`dreplace.commit` are additive, and no v1 theorem depends on them.

**C8 — `use` is an enabled stutter step.** §2.2's check is a pure read; it is
modelled as a state-preserving transition so uses interleave with drops and
revocations inside a single run. Epoch D7, unchanged.

**C9 — the §3 embedding of the lineage cells uses one referent volume.**
`absLin : St W N L → Epoch.Protocol.St W L 1` presents the lineage cells as a
settled one-volume §3 system, and `revoke_absLin` proves `cap_revoke` is a
*complete* §3 bump/ack/return (three `Epoch.Protocol` steps), so every
lineage read in `check` is a post-return read and §3's `T_E1_never_ok`
applies directly. `run_absLin` is the simulation; T-C4 is one application of
it plus §3's theorem — **no freshness argument is made in this file.**
Consequence, stated rather than hidden: T-C4 does not exhibit §3's in-flight
liberty (T-E7). A multi-volume v2 (capability tables replicated across
domains) must re-derive T-C4 against a `pending` bump, where a concurrent use
may still succeed. The embedded (per-slot) cells are *not* transported this
way — §3's `use`/`bump` alphabet has no occupancy transition, and drop/mint
change occupancy — so T-C5 is proved directly from cell-epoch monotonicity
and death stickiness over `Run`.

**C10 — concrete field types.** `Rights` is `BitVec 8` with containment
`a &&& b == a`; range is a `Nat` `base`/`len` pair; class is a `Nat`. §2.2
fixes none of these widths (they are per-implementation), and every theorem
is generic in the epoch width `W`, the slot count `N`, and the lineage-cell
count `L`.

**C11 — the exhaustive form of T-C2 is over the ordered scalars.**
`T_C2_exhaustive` checks `outcome` against an independently written
`priority` at `W = 2` over all `2^2 · 2^2 · 2^7 = 2048` local views, in the
kernel (`decide`, never `native_decide`). The entry-derived values (rights
containment, class equality, range containment, the lineage verdict) are fed
in as booleans, exactly as Epoch D4 does, because the thing §2.2 freezes is
the *order*; the derivation of each value from the entry is `check`'s
definition and is exercised by the arbitrary-width theorems
`T_C2_structural_first`, `T_C2_empty_slot`,
`T_C2_embedded_epoch_before_lineage`, `T_C2_lineage_before_rights`,
`T_C2_rights_before_class`, `T_C2_class_and_range_last`. The
"empty slot whose current embedded epoch nevertheless matches is `-BADREF`"
clause is `T_C2_empty_slot`.

**C12 — the walker is a transaction shape, not a sequencer, at Layer 1.**
`fill`/`evict` move `St.resident` and carry no latency, ordering, or
multi-level walk. Appendix F row 2's "page-walker-class sequencer" is a
Layer-2 (`Engine.lean`) obligation; Layer 1 owes only what the fill may and
may not do to authority (C5).

**C13 — `N` is a parameter, not `2^24`.** The 24-bit slot field is proved
bounded by the encoding (`T_C1_slot_bounded`), and `decode` rejects a slot
index `≥ N` as `-BADREF` (§2.2's "out-of-range/malformed slot index"). So the
model is honest about both the architectural field width and the fact that no
implementation builds sixteen million entries.

**C14 — `T_C1_null_is_badref` is stated over `decode`.** §2.2's "everywhere
else handle `0` is simply an invalid handle and fails `-BADREF`" is proved
for every state and every requested rights/class/range, from the layout — the
positions §2.2 architects to *admit* the null sentinel (`mmap`'s
`backing_cap`, self-target operands, optional capability operands) are not
modelled, since they are per-operation admissions, not a property of the
check.

**C15 — non-vacuity is exhibited, not assumed.** Every T-C theorem is a
safety statement and would hold of a model where `cap_dup` is never enabled,
so `demo_dup_then_revoke` is a concrete run of `sys 3 2 1`: a root capability
mints a narrowed descendant into an empty slot, the descendant's handle
returns `ok`, and one `cap_revoke` on the shared lineage cell turns the same
use into `-STALE`. Same role as §3's T-E7 — it keeps the model honest.
