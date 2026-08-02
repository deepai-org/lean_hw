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

## Layer 2 artifacts

| file | what it is |
|---|---|
| `Machines/CapWalk/Engine.lean` | the open Loom `Design` `capwalk`: entry cache, walker/fill sequencer, authenticated fill, D18 selftest, the DDR image the testbench loads |
| `Machines/CapWalk/CapSoc.lean` | `capmmio` + `lnp64mini_cap` = the epoch SoC ∥ the capability engine ∥ its own HP master |
| `Machines/CapWalk/Emit.lean` | the runner (`selftest` / `d19` / `predict` / `ddr` / `engine` / `soc`) |
| `fpga/zc702/tb_capwalk.v` | the iverilog testbench with the hostile behavioural DDR |
| `fpga/zc702/capwalk_ddr{,_remint}.hex` | the DDR images, generated from `Engine.ddrImage` so the Lean and RTL legs cannot drift |
| `scripts/capwalk_ladder.sh` | the whole ladder, including the byte-identity regression |

## Deviations (Layer 2, recorded against §"Layers" item 2)

Every item below is a departure from, or a refinement of, this file's
§"Layers" item 2 as built in `Machines/CapWalk/Engine.lean` and composed in
`Machines/CapWalk/CapSoc.lean`. `Machines/CapWalk/Protocol.lean` (Layer 1)
is **frozen and unedited**, as are `Machines/Epoch/*`, `Loom/*` and
`Tools/*`. Nothing here is a `sorry`, a `native_decide` or a new axiom;
`lake exe audit` is green.

**Where T-C6 stands after this layer.** §Deviations C5 says T-C6 is "a
contract on the store" until authentication establishes it. Layer 2
*establishes it in hardware*: the fill path installs an entry **only** when
a tag bound to `{payload, slot, embedded epoch}` verifies, so a corrupted,
substituted or replayed entry cannot become resident. Two honest
qualifications: (i) the strength of that establishment rests on CE4's
stated assumption about the keyed compression function, not on a proof; and
(ii) **the Layer-3 refinement (`Refines.lean`) is not part of this
delivery**, so what exists today is a design plus an exhaustive-at-the-
scenario-level demonstration (D18 FastEval ladder + RTL co-simulation), not
a mechanized simulation to `Protocol.stepEv`. That is the next obligation,
and it is stated here rather than implied.

**CE1 — 32-bit epochs.** §2.2's embedded cell is 39 bits; the engine ships
`ew = 32`, exactly as §3's engine does (Epoch E1). Every Layer-1 theorem is
generic in `W`, so nothing narrows; the RTL is the narrow instance.

**CE2 — `sw = 10`: the on-chip cell table is 1024 slots, not 2^24.** The
handle's slot field stays 24 bits at the port (`req_slot : 24`); a slot
index `≥ 2^sw` is rejected structurally as `-BADREF`, which is Layer-1 C13
("`decode` rejects a slot index `≥ N`") realized in hardware as
`oobE`. This is the *architectural* honesty §2.2 demands: 2^24 slots are
nameable, 2^10 exist, and naming a non-existent one is a defined failure,
not undefined behaviour.

**CE3 — a fifth outcome code: `OUT_FAULT = 4`.** §2.2's condition mapping
is total over `{ok, badref, stale, denied}` because Layer 1 has **no
corruption event** (C5). Layer 2 has one, and Appendix F's fail-stop
disposition has to be *observable*: an operator cannot distinguish "your
handle is malformed" from "your backing store is lying" if both are
`-BADREF`. So the engine emits code 4, sets the slot's sticky `F_FAULT`
bit, and raises `fault_valid`/`fault_slot`.

What this costs, stated plainly: `Engine.codeE` is **not** literally
`Protocol.outcome`; it is `Protocol.outcome` with one extra clause between
the structural clause and step 1. Layer 3 must therefore either widen
`Protocol.Outcome` with a `fault` constructor (the honest move, mirroring
C6's note about `-POISONED`) or prove the collapse `fault ↦ badref`. The
safety-relevant half is already true by construction and is what the ladder
checks: **`FAULT` is never `ok`, and it is permanent** — nothing in the
design clears `F_FAULT`, including `OP_MINT`.

**CE4 — the authenticator, and exactly what is assumed.** The tag is a
5-round keyed `xorshift32` chain over `P0[31:0] ‖ P0[63:32] ‖ P1 ‖ slot ‖
E(slot)`, where `E(slot)` is the **on-chip** embedded epoch (`macOf` /
`xsE`; see `Engine.lean` §Authentication for the definition).

* **Architectural, and delivered.** All three §41 adversaries change an
  input of the tag computation — corruption changes `P0`/`P1`,
  substitution changes `slot`, replay changes `E(slot)` — and `mix` is
  injective in its message word for fixed `(h, k)`, so each is detected
  *with certainty* under a single-word change, not with high probability.
  And detection is fail-stop by construction: `Engine.lean` has exactly one
  code path that writes `c_tag`/`c_p0`/`c_p1`, and it is guarded by
  `mac_h == w_tag`. There is no best-effort arm.
* **Assumed, and NOT claimed.** `xorshift32` is a bijection, not a PRF.
  Against an adversary who can choose many messages and observe tags, the
  round keys are recoverable and forgery is feasible. The assumption this
  layer asks for is precisely *"the keyed compression function is
  unforgeable under the engine-held key"*, and it is confined to the
  twelve lines of `xsE`/`macRound`: replacing them with SipHash-2-4 or
  AES-CMAC changes the `W_MAC` round count and nothing else — not the
  cache, not the check order, not a disposition. **Do not read the
  selftest's "all three attacks detected" as a cryptographic claim.**

**CE5 — RETIRED 2026-08-01 by Loom D39 (declared observability).** The
deviation, as it stood: `MAC_IV` and `macK 0..4` had to appear as *literals*
inside the mixing cone, because in this emission path every register became
an `o_*` output port (that is how `HpMaster`'s AXI qualifiers are emitted),
so a key held in a register would have been **published at the module
boundary**. An EDSL that structurally cannot keep a secret is a Loom defect,
not a machine-level inconvenience, so it was written into the ledger as
`LOOM_GAPS.md` D39 rather than worked around further.

D39 added `Design.outputs : Option (List String)` (`Loom/Hw/OUTPUTS_SPEC.md`,
`Loom/Hw/Outputs.lean`) — a design declares which registers it exports;
`none`, the default, is the old "all of them". `Engine.keyRegs` is now six
ordinary registers (`mac_iv`, `mac_k0..4`), no rule writes them, and
`Engine.mkDesign`'s selection omits them, so they sit at **no port**. Loom
proves the general fact (`Loom.Hw.compile_not_exported`: for
`outputs = some ns`, a name outside `ns` is neither a port name nor read by
any port's driver) and the same statement over the emitted *text*
(`printed_not_exported`, via the independent parser). `capwalk`'s port list
is unchanged: the selection is exactly the pre-D39 register list.

**What this does and does not claim.** The key is now *architecturally*
secret — no module port carries it, so nothing above the design boundary,
including either core, can read it. It is **not** physically secret: the
registers' reset image is still a compiled-in constant and an FPGA bitstream
can be read back on this part. The v2 that wants a genuinely device-held key
still needs a configuration-time key-load path from a PUF/TRNG; what changed
is that such a path is now an added *rule over an existing coordinate*
rather than an EDSL feature request, and per-boot or per-domain re-keying is
expressible today.

**CE6 — `OP_MINT` is a new, software-requestable op.** §2.2 names the
embedded bump only on drop, and Layer 1's `cap_dup` mints *from an
authorizing capability*. Layer 2 has no `cap_dup` (CE8), so it exposes a
bare re-incarnation: bump the embedded cell and clear `F_VACANT`.

Why this is not a hole: minting installs **no authority**. The rights an
occupied slot confers come from the DDR entry, and that entry has to
authenticate under the **new** embedded epoch, which requires a tag
computed with the key — which software does not have (CE5: the key is
engine-owned state that reaches no port and no address). So an
adversarial core that mints slots at will produces slots that fail-stop on
first use, never slots that grant rights. `OP_MINT` also does not clear
`F_FAULT`. The ladder exercises exactly this: A3's control re-incarnates
slot 8 against a store that re-issued the entry, and it succeeds; A3 itself
re-incarnates slot 5 against a store that did not, and it fail-stops.

**CE7 — the capability engine is an extra §3 referent volume, outside the
acked span.** `CAPWALK_SPEC.md` says "engine #2 lands on engine #1", and
`Machines/Epoch/*` may not be edited, so the seam is the epoch engine's
existing broadcast: `cw_inval_valid/cell/epoch ← ep_inval_valid/cell/epoch`,
and `lin_repl` is written by that and by nothing else. `cap_revoke` is a §3
bump requested through the *existing* `epochmmio` word.

The deviation, stated rather than hidden: the epoch engine's `B_ACK`
sequencer collects acks from its **two** replica banks only, so the
capability engine's adoption is **not inside the acked span**, and §3's
return guarantee does not formally cover it. What is true instead:
`inval_valid` is asserted on entry to `B_ACK` and held until `B_RET`, and
`B_ACK` takes at least two cycles, so the capability replica has adopted
before the bump returns. That is an argument about the composition, not a
theorem, and Layer 3 must either prove it or extend the epoch engine's ack
span (an edit to `Machines/Epoch/Engine.lean`, out of scope here). Layer 1
already flags the shape of this gap in C9 (T-C4 does not exhibit §3's
in-flight liberty).

**CE8 — the backing store is read-only at Layer 2.** `cap_dup`, install and
`dreplace.commit` are staged out (§Scope), so there is no authenticated
*write* path and no dirty-line write-back: eviction is silent, and the
cache is a clean read cache over an authenticated table. Consequently the
"dirty-line forwarding invariant" `EPOCH_SPEC.md` §SUPERSEDING DOCTRINE
point 3 mentions is not needed yet — and when the installer lands, it is
the *installer* that owes MAC generation, which is the natural place for it.

**CE9 — `cw = 8` (256 cache lines) is a fit decision, measured.** A 32-line
cache is below `yosys`'s block-RAM threshold, so `c_tag`/`c_p0`/`c_p1`
landed in flops with a 32:1 read mux. At 256 lines the payload banks are
block RAM. Together with CE10 this is a 14× LUT difference on the same
logic; the before/after numbers are in §FIT below.

**CE10 — one write port per shared bank, and the interlock that makes it
sound.** `c_tag` has two writers (walker install, drop/mint invalidate) and
`cell_flags` has two (walker fail-stop, drop/mint bump). Two syntactic
write sites become two `Compile` write *ports*, and a Xilinx block RAM has
two ports **total** — so `cell_flags` (three read sites + two writes) fell
out of block RAM entirely. `yosys`'s own words on the naive shape, for
`cell_flags` alone: *"created 1024 $dff cells ... read interface: 3 $dff
and 3069 $mux cells, write interface: 2048 write mux blocks"* — on an
engine with about 700 architectural flops. Together with CE9 the two
mistakes measured **9 523 LUTs / 3 982 FFs**; the shipped engine is
**671 LUTs / 442 FFs** (§FIT).

Fixed by giving each bank exactly one muxed write site (`ctagWrRule`,
`flagWrRule`) *plus* an interlock: `opRule` accepts a drop/mint only while
`w_st = W_IDLE`, and `chkRule` starts a fill only while `d_st = D_IDLE`, so
`D_DO` and `W_CHK` are mutually exclusive and the mux priority is a
don't-care rather than a policy. `Design.memPortTraceOkB` is the standing decidable
guard (`Compile.MemWriteWF`'s port condition), checked before every emit —
Loom-level since D38, having started life here as `Engine.memPortsOkB`
(`Loom/Hw/MemTarget.lean`; the engine keeps only the discharged obligation,
`Engine.design_memPortTraceOk`).

Residual, named: a drop/mint request that arrives while a fill is in flight
is **dropped**, not queued. The MMIO adapter's op word is fire-and-forget,
so software must poll (`fill_count`, or re-read the slot). A v2 wants a
one-deep request queue.

**CE11 — one check unit, and the check costs 4 cycles.** §3's engine has
one check unit *per referent volume* (Epoch E3); §2.2's capability check is
per-domain and has one client here, so there is one unit. It is
`K_IDLE` (accept, drive the addresses) → `K_RD` (the cell and cache banks'
registered read) → `K_LIN` (the lineage replica's read, whose **address is
the cached payload's lineage field** and therefore cannot issue a cycle
earlier) → `K_EV` (one compare, emit). It is still one compare against
on-chip state with no fabric transaction, which is what §2.2's checking
interface claims; the extra cycles are the price of block RAM (Epoch E4's
argument, one stage deeper because of the lineage indirection).

Steps 1–2 of §2.2 (occupancy, embedded epoch) are answered from the cell
banks alone, so a stale or dropped handle **never causes a DDR
transaction** — the ladder checks that as a counter assertion, not as
folklore.

**CE12 — the walker is a three-beat sequencer, not a multi-level walk and
not a Merkle tree.** Appendix F row 2's "page-walker-class sequencer" is
honoured as a sequencer over the HP-master handshake (`W_A0/D0 → A1/D1 →
A2/D2 → MAC → CHK`), with a flat, directly-indexed table at
`tbl_base + slot·32`. §Scope already stages the Merkle *tree* out ("v1
authenticates entries individually; the tree is a scaling optimization, not
a safety change"), and a multi-level table is the same kind of additive
change.

**CE13 — the composed SoC gives the engine its own HP master.** `HpArbiter`
has exactly two requester ports and both cores hold them, and
`Machines/Lnp64mini/*` may not be edited, so `lnp64mini_cap` instantiates a
second `axi_hp_master` (`cwhp_`) for the walker. The ZC702 has four HP
ports, so this is a wiring fact, not a compromise; `cwhp_start_wr` and
`cwhp_wdata` are tied off (CE8), and the master's write path constant-folds
away.

**CE14 — reset images stay all-zero except the two epoch banks.**
`cell_flags` encodes occupancy as `F_VACANT` (**empty**, not occupied) and
`c_tag`'s valid bit resets clear, so both reset to all zero — Epoch E13's
lesson (an all-zero image is the only one every configuration path
delivers) applied at design time rather than after a silicon surprise. The
non-zero images are `cell_epoch` and `lin_repl`, both epoch 1, both mapped
to block RAM whose `INIT` the flow does deliver.

**CE15 — `tbl_base` is an input port, not an MMIO register.** The table's
DDR base is an integration-time constant driven by the composition
(`CAP_TBL_BASE`), so no core can retarget the walker. It would in fact be
harmless if one could — every entry's tag binds its slot and its on-chip
epoch, so a table at a different address authenticates only if it holds the
*same current* entries — but "harmless because of the MAC" is a weaker
statement than "unreachable", and the doctrine prefers the latter.

## FIT (measured, `yosys 0.33 synth_xilinx`, XC7Z020: 53 200 LUTs, 106 400 FFs, 140 RAMB36)

| design | LUTs | % LUT | FFs | RAMB36 | RAMB18 |
|---|---|---|---|---|---|
| `epochengine` alone | 351 | 0.7 % | 204 | 0 | 3 |
| **`capwalk` alone** | **671** | **1.3 %** | **442** | **4** | **6** |
| `lnp64mini_dual` (baseline) | 29 032 | 54.6 % | 12 389 | 26 | 0 |
| `lnp64mini_epoch` (+ §3 engine) | 29 480 | 55.4 % | 12 805 | 26 | 3 |
| **`lnp64mini_cap` (+ §2.2 engine)** | **29 997** | **56.4 %** | **13 519** | **30** | **9** |

**Does it fit? Yes, and cheaply.** The capability engine, its second HP
master and its MMIO adapter cost **+517 LUTs (+1.8 % relative, +1.0
percentage point of the device), +714 FFs, +4 RAMB36 and +6 RAMB18** on top
of the dual+epoch SoC. Block RAM goes from 26 to ~34.5 RAMB36-equivalents,
about 25 % of the 140 available — the ZC702 has BRAM to spare and this
design spends it deliberately (CE9/CE10) to keep LUTs.

**What it would have cost done naively — the number worth remembering.**
The first build (32-line cache, two write ports on the two shared banks)
measured `capwalk` alone at **9 523 LUTs / 3 982 FFs**, i.e. **14× the LUTs
and 9× the flops** of the shipped engine, for the same logic. `yosys` put
`cell_flags` and `c_tag` in flip-flops with 1024:1 and 32:1 read muxes,
because a bank with more than two ports (three reads + two writes) has no
block RAM to go to, and a 32-deep bank is below the block-RAM threshold.
Added to the cores' 29 k that is 38 k LUTs, 72 % of the device, and it
would have been read as "the capability engine is expensive" rather than as
"two banks fell out of BRAM". D19 is a *shape* discipline about reads;
CE10 records that write-port count is the matching discipline for writes.
It is a Loom capability now, not a local guard: D38 made the write-port
budget a field of a declared `MemTarget` profile, so `Design.realizableOnB`
predicts that a bank over budget falls out of the macro — and, when such a
bank carries a reset image, `Design.emit` refuses it
(`Loom/Hw/MemTarget.lean`, `LOOM_GAPS.md` D38).

Reproduce with `scripts/capwalk_ladder.sh` plus

```console
yosys -p "read_verilog rtl/lnp64mini_cap.v; hierarchy -check -top lnp64mini_cap; \
          synth_xilinx -top lnp64mini_cap; stat"
```

(`lnp64mini_dual`'s baseline moved by ~115 LUTs from an earlier measurement
in this session because a concurrent workstream edited
`Machines/Lnp64mini/Core.lean`; all five rows above are from one batch, on
one tree, so the deltas are comparable.)

**Not measured here:** place-and-route timing. The MAC's mixing cone is
three XOR-shift stages of 32 bits inside one cycle (`W_MAC`), which is the
longest new combinational path in the engine; if it does not close at the
SoC clock, the fix is to spread `xsE` over two `W_MAC` sub-states, which
costs one cycle per MAC round and nothing else. Recorded so that a timing
failure is a known knob, not a surprise. **No board work was done in this
campaign.**

## Theorem priority for Layer 3 (scoping note, 2026-08-02)

Adversarial-memory safety is **not** the headline theorem for a real
processor, and Layer 3 should not be organised around it. It is
threat-model-specific: it matters when memory is genuinely outside the trust
boundary (confidential computing — SEV-SNP/TDX/CCA authenticate memory because
the hypervisor is untrusted; and *our* board, where DDR belongs to the PS and
is shared with A9s we do not control). On a part with an on-die memory
controller, DRAM is usually inside the boundary, and an attacker who can
rewrite it arbitrarily likely had a cheaper path. CHERI does not MAC its
capability tables.

Ranked by what actually carries the security claim:

1. **Mediation / no-bypass** — every access is checked; no path reaches memory
   or authority around the check. If this is false nothing else matters, and
   it is currently the LEAST explicit thing we have. Layer 3 should state it.
2. **The refinement itself** — the RTL implements the architecture. Wrong here
   and every security theorem is about a different machine.
3. **Revocation complete within a bound** — the capstone, and the claim nobody
   else can demonstrate on silicon.
4. **Isolation including timing** — no influence across domains except through
   named channels.
5. **Fail-stop containment** — a detected violation is contained.

T-C6/authentication is one clause among these, not the organising principle.

**Keep the authenticated fill regardless.** It is built, cheap at this scale,
and honest about its assumption (CE4). And the doctrine that produced it
earned its keep for a reason other than its threat model: requiring
zero-assumption safety forced the safety-critical state on-chip at the
checking interface, which is what made the *epoch* refinement come out
unconditional over adversarial cores and why prophecy variables (D25) proved
unnecessary — `b_acked` is architectural state, not a fact about the future.
The design discipline bought more than the theorem will.
