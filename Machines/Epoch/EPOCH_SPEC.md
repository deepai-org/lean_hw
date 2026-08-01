# Epoch engine: spec-to-silicon plan (LNP64 §3, Appendix F machine 1)

Normative source: `/home/ubuntu/lnp64/lnp64_isa.md` §3 "Epoch cells (the one
freshness primitive — Law 2)" and Appendix F ("mechanized protocol specs are
the normative behavioral definition"; each generation's RTL discharges a
*refinement obligation* against the frozen protocol). This is the first such
obligation attempted, for the machine every other engine is a client of.

Deliverable shape (three layers, one repo each where it belongs):
1. `Machines/Epoch/Protocol.lean` (lean_hw) — the mechanized §3 protocol as a
   `Loom.TSys`-shaped transition system + its safety theorems. This is the
   candidate NORMATIVE artifact; it is written to be copied/referenced from
   the lnp64 repo once proven (do not edit lnp64_isa.md in this campaign).
2. `Machines/Epoch/Engine.lean` — the Loom `Design` (hardware).
3. `Machines/Epoch/Refines.lean` — Simulation from Engine to Protocol.

## Scope decisions (v1 — record deviations, do not silently narrow)

IN: embedded + shared cells; `{epoch, referent_count, poison}`; saturation =
permanent death; bump policies **lazy** and **poison**; broadcast + ack over a
referent span of exactly the two cores (the minimum honest distributed
instance); failure precedence; the three lifecycle points (death /
no-stale-access / reuse) for the CPU-use case.

OUT (staged, named): `cancel` (needs the park/wake directory — Appendix F
machine 6), `quiesce` (needs DMA + fence recourse), replication/spanning-tree
reduction beyond 2 leaves (the bound is O(log span); with span=2 the tree is
one level — state this, don't pretend), RESTAMP/lineage repoint, the other six
referent kinds (§3's eight-row table) — v1 exercises capability-slot validity
and one shared lineage cell.

## Protocol model (Layer 1)

State (spec level, N cells, K = 2 referent volumes):
```
cell i : { epoch : Word W, rc : Nat, poison : Bool, dead : Bool }   -- dead = saturated
volume k, cell i : { repl_epoch : Word W }      -- the per-volume replica (§3 "replicated per referent-holding volume")
pending : Option { cell, target_epoch, acked : Fin K → Bool }        -- one bump in flight (v1)
```
Operations (spec transitions):
- `use k i e` → outcome ∈ {OK, BADREF, POISONED, STALE, DENIED} using the
  *volume-local replica* (class-0 check: local, tile-bounded, one compare).
  Failure precedence EXACTLY §3: structural → poison → freshness → rights.
- `bump i policy` → increments home epoch (saturating; at max ⇒ `dead`
  permanently), marks poison if policy=poison, starts the broadcast.
- `ack k` → volume k adopts the new replica epoch.
- `bumpReturn` → enabled only when all referent-span volumes have acked
  (THE return guarantee: "post-return success through an old remote replica is
  forbidden").

Safety theorems to prove (each maps to a §3 sentence):
- **T-E1 stale-fails-forever**: after `bumpReturn` for cell i, any `use` with
  the pre-bump epoch fails (STALE or POISONED) at every volume, forever.
- **T-E2 saturation is permanent death**: once `dead`, no `use` ever returns
  OK again; no bump revives (counter never wraps to a live value).
- **T-E3 poison permanence**: after a poison bump, even *current-epoch* uses
  fail POISONED (§3: "future references, not just stale ones"), forever.
- **T-E4 failure precedence**: the outcome function is exactly the specified
  priority order (a decidable statement over all inputs at the model's bounds).
- **T-E5 no-stale-access point**: no use that linearizes after `bumpReturn`
  observes the old epoch — this is T-E1's temporal half; state it over runs.
- **T-E6 monotonicity**: home epoch and each replica are non-decreasing.
- **T-E7 in-flight liberty**: a use concurrent with the bump MAY succeed
  (§3 explicitly allows it) — proved as a non-theorem: exhibit a run. This
  keeps us honest that the spec is not over-constrained.

Also: model-check the same statements at §16.4-style bounds with Loom's BMC/
k-induction (`Loom/Dp/Bmc.lean`, `KInduction.lean`) as an independent leg.

## Engine design (Layer 2)

Loom `Design` "epochengine", open (D15):
- Cell table: `mems` — `cell_epoch` (aw=CELLW, dw=39 per §3's capability-slot
  width; use 32 for v1 and record it), `cell_flags` (poison/dead bits).
  Per-volume replica table: `repl0_epoch`, `repl1_epoch` (2 volumes).
- Inputs (from cores/wrapper): `req_valid, req_core, req_op(check|bump),
  req_cell, req_epoch, req_policy`; outputs: `resp_valid, resp_code(2b),
  resp_busy`, plus `inval_valid/inval_cell/inval_epoch` per core and
  `ack_core0/ack_core1` inputs.
- FSM: IDLE → (CHECK: one-cycle local compare against the requesting core's
  replica, per the class-0 rule) | (BUMP: home increment/saturate/poison →
  BROADCAST → collect acks → RETURN). A cycle counter latches
  bump-issue→ack-complete for the demo's latency measurement.
- Fill/access split (Appendix F's frozen datapath residue): the CHECK path
  compares an epoch the core already holds against the local replica — no
  fabric transaction. Bumps are transaction-side.

## Core integration + demo (Layer 3/4)

Two ops in lnp64mini's decode via the GP-aperture pattern (MMIO to the engine,
NOT new opcodes — keeps the core's proved ladder intact; record this as a
deviation from "instruction" framing in §3): a check word and a bump word at
distinct MMIO addresses through the existing `l_is_gp`/`s_is_gp` path.

Demo (the goal's acceptance): under live NetBSD on core 0, a core-1 workload
holds a reference and loops `check`; core 0 issues `bump`; the engine's cycle
counter reports bump-return-to-fail-closed; core 1's next `check` returns
`-STALE`; a `poison` bump then fails closed forever across a soak.

Ladder as always: Protocol ≡ Engine (refinement, Layer 3) → FastEval/ISS ≡
iverilog → eqcheck the engine netlist → silicon numbers.

## Design decision: engine state and DDR (binding, 2026-08-01)

Question that will recur for every engine: can Loom prove things about an
engine whose state lives in DDR? Today, no — DDR sits behind the AXI master,
so it enters a Design as a D15 *input trace*; theorems quantify over all
traces and therefore say nothing about DDR contents. On-chip `mems` (D19/D20)
ARE in scope. The standing rules:

1. **Safety-critical state lives on-chip, at the checking interface.** This is
   not a Loom limitation dressed as a principle — it is Appendix F's
   validator-concentration doctrine ("safety proofs attach to checking
   interfaces; producing engines owe completeness and liveness only") plus
   §3's class-0 requirement that the epoch check be local and tile-bounded,
   with cell state resident near every referent. An engine that puts its
   safety invariant in far memory is nonconforming before it is unprovable.
2. **DDR holds re-validatable bulk only.** A DDR-backed table is a backing
   store behind an on-chip cache whose fill path re-validates. Proof shape:
   the cache is a faithful view GIVEN the fill contract; the fill contract is
   where the environment assumption sits, concentrated in one place.
3. **When DDR must be modelled, compose it — do not assume it.** Write the
   behavioral DDR+AXI slave as a Loom `Design` and `connect` it (D16) so the
   composed system is closed and its theorems unconditional; the residual
   obligation becomes "the PS DDR refines this model," a statement about an
   AXI slave. Preferred over a `DdrFaithful` trace predicate (the cheap
   option, CmdPulseTrace-shaped), which stays available for quick results.
   The iverilog testbenches already contain this behavioral slave, so the
   model should BECOME the testbench, not duplicate it.
4. **Corruption is an architected outcome, not a proof hole.** For freshness
   specifically, a stale DDR-resident value fails the epoch check by
   construction; what DDR still owes is integrity, and a detected violation
   has its §3/Appendix F disposition (poison, fail-stop, CORE_CHECK).

v1 consequence: the epoch cell table fits entirely on-chip on the XC7Z020
(~114 free RAMB36 after the dual core), so v1 needs no DDR-resident state.
The composable memory model (rule 3) is built alongside, because the NEXT
engine (capability table walk/fill, Appendix F machine 2) genuinely spills.

## SUPERSEDING DOCTRINE: external state is adversarial (binding, 2026-08-01)

The four rules above are the ROAD; this is the DESTINATION, and every
intermediate theorem must survive as a lemma of the final one. The reason
"engine keeps its table in DDR" is unprovable today is that theorems quantify
over all `m_rdata`/`m_done`. The move is NOT to condition that quantifier down
(a `DdrFaithful` predicate) nor to close it with one model — it is to build
engines for which the UNCONDITIONAL theorem is true. Then the very fact that
made DDR unprovable makes the result maximally strong: the D15 boundary stops
being a limitation on proofs and becomes the formal statement that the outside
world is untrusted.

The end state, four theorems:

1. **Zero-assumption safety — DDR as adversary.**
   `theorem engine_safe : ∀ ιs, SafetyInvariant (run engine ιs)`
   No side condition. Memory may return garbage, replay stale lines, or lie
   about completion; every value crossing back in is re-validated (MAC/tag for
   integrity, epoch for freshness — which §3 gives by construction) and every
   failure lands in fail-stop/poison/CORE_CHECK. Authenticated memory
   (Merkle/MAC over the spilled table, epoch-bound against cross-epoch replay)
   is the completion of §3's own observation that staleness already fails the
   check: extend it until EVERY memory misbehavior is harmless or detected.
2. **Rely-guarantee liveness — quantify over all compliant memories.**
   `theorem engine_live : ∀ env, env ⊨ Φ_axi → Liveness (run engine (env ⊗ …))`
   Liveness cannot be assumption-free (a memory that never answers denies
   service; no tag check fixes that). `Φ_axi` is the mechanized frozen
   AXI-subset spec used as a RELY, not a discharged obligation — strictly
   stronger than proving against one model. The behavioral slave is demoted to
   its proper role: a Lean-proved WITNESS that `Φ_axi` is satisfiable (so the
   rely is not vacuous), and the same artifact drives iverilog co-simulation so
   proof and testbench cannot drift.
3. **Abstraction — ISA-level theorems never mention DDR.**
   Engine specs are stated against an abstract machine whose table is one
   mathematical map. ONE refinement (abstraction = on-chip cache ∪
   authenticated backing store, with the dirty-line forwarding invariant)
   quarantines the whole memory hierarchy; everything above it (Appendix F
   validator theorems, class-0 locality) is proved against the abstract map and
   is PORTABLE — move the backing store to HBM, a second channel, or a network,
   and only that one proof changes.
4. **The residual axiom, guarded by a proof-derived artifact.**
   "The PS7 eventually responds" is a claim about someone else's silicon and
   will never be a Lean theorem. So generate a bus monitor FROM `Φ_axi`, as a
   Loom design through the same trusted pipeline, with
   `theorem monitor_sound : monitor flags trace ↔ ¬ (trace ⊨ Φ_axi)` (up to
   bounded history), routing violations to poison/CORE_CHECK. The deployment
   assumption becomes "PS7 satisfies Φ_axi OR we fail-stop" — protocol
   compliance converts into an architected detected violation. What stays
   axiomatic is one ledger line: EXTERNAL MEMORY EVENTUALLY RESPONDS. It gates
   liveness only, never safety.

Why this is the ideal and not merely the maximal option: the safety/liveness
asymmetry is fundamental and this design saturates both sides — safety with
zero environmental assumptions, liveness with exactly one, runtime-monitored.
It is self-hosting (cache, MAC engine, epoch check and bus monitor are all Loom
designs with their own proofs, emitted through the same checked pipeline: the
guardian of the one axiom is itself proof-carrying). And it composes outward:
`Φ_axi`-as-rely is a template for every future external dependency (second bus,
NoC, eventually the CDC boundary).

### Consequence bound NOW, for the v1 engine (boundary: cores, not DDR)

Same doctrine one boundary in. §3's return guarantee depends on acks being
truthful. If a CORE holds its own replica and asserts its ack, a lying core
breaks safety and T-E1..T-E6 must be conditioned on core cooperation. So:
**the ENGINE owns the per-volume replicas (one BRAM bank per volume) and the
ack is engine-internal; cores may only REQUEST checks and bumps, never write
freshness state.** Then the epoch safety theorems are unconditional over all
core behavior and all input traces — adversarial cores included. This is not a
new requirement: §3's safe-reuse corollary already says the reuse point is
"established by the engine, never asserted by software". Layer 2 (Engine.lean)
is bound to this shape; Layer 3's refinement must therefore deliver an
UNCONDITIONAL safety statement, and any conditionality is a defect to report,
not a scope decision to take.

### Proposed contribution back to the ISA doc (not applied here)

Appendix F's asymmetry — checkers owe safety, producing engines owe
completeness and liveness — is the same theorem as the safety/liveness
asymmetry above, at a different scale. Worth stating explicitly in Appendix F
so the validator-concentration doctrine and the external-state doctrine are
visibly one principle.

Ledger line: **DDR holds bits; the design holds truth. Safety assumes nothing
of the outside world; liveness assumes exactly one thing, and a proof-carrying
monitor watches even that.**

## Deviations (Layer 1, recorded against the plan above)

Every item below is a departure from, or a refinement of, this file's
"Protocol model (Layer 1)" section as mechanized in
`Machines/Epoch/Protocol.lean`. Nothing was silently narrowed.

**D1 — `Cell` carries an `occupied` bit.** The state shape above lists
`{epoch, rc, poison, dead}`. §3's failure-precedence paragraph also rules on
*empty* slots ("an empty slot is `-STALE` when its embedded epoch mismatches
and `-BADREF` only for a matching-epoch empty reference"), which is
unstatable without occupancy. `Cell.occupied` is additive and no v1
transition writes it (`step_occupied`).

**D2 — poison/death are home-cell facts; only the epoch is replicated.**
The state shape replicates exactly `repl_epoch` per volume, so `use` reads
the *freshness* value from `repl k i` (§3's class-0, tile-bounded compare)
and the *dispositions* from the home cell. Consequence, stated rather than
hidden: T-E3 (poison) is immediate everywhere, not ack-gated, which is
strictly stronger than §3 requires; the ack-gated content of §3's return
guarantee lives entirely in T-E1/T-E5, which are about the replicated
epoch. A v2 that replicates the poison bit must re-prove T-E3 as an
ack-gated theorem.

**D3 — saturated death is a freshness-class failure (`-STALE`).** §3 gives
death no error value of its own; it files saturation under "stale fails
forever". `useLocal` therefore returns `-STALE` for a dead cell, after
poison and before the epoch compare.

**D4 — structural and rights facts are request-level booleans.** `Req`
carries `wellFormed`, `classOk` and `rights` rather than deriving them from
a modelled capability table. v1 exercises capability-slot validity
abstractly (as scoped above); the precedence theorems T-E4 are therefore
about the *order* of the checks, which is what §3 freezes.

**D5 — slot reuse is not a v1 transition.** §3's "slot reuse installs a new
entry with no inherited poison" appears in the model only as the empty-slot
clause of the outcome function, not as a step. T-E3's "forever" is
consequently relative to the v1 op set. Re-install belongs with the *reuse
point*, which this scope note already stages out.

**D6 — two extra ops: `acquire` / `release`.** The op list above names
`use`/`bump`/`ack`/`bumpReturn`. Without a referent-count mutator the `rc`
field would be vestigial, so the model adds the two minimal ops. They are
carried through every invariant.

**D7 — `use` is an enabled stutter step.** §3's check is a pure read. It is
modelled as a state-preserving transition so that "a use concurrent with the
bump" (T-E7) is a genuine interleaving inside a run rather than an
extra-logical notion.

**D8 — "forever" is `Relation.ReflTransGen Step`.** T-E1/T-E2/T-E3/T-E5 are
stated over every state reachable from the state in question, rather than
over an explicit trace type. `Loom.TSys.Reachable` is used for the
init-relative invariant (`inv_invariant`).

**D9 — epoch width stays a parameter.** `epoch : BitVec W` with saturation
at `allOnes W`; every theorem is proved for all `W`, so the 39-bit
capability-slot cell and the 64-bit shared cell are both instances. The
exhaustive-`decide` restatement of the precedence order (`T_E4_exhaustive`)
is at `W = 2`, which is the "decidable statement over all inputs at the
model's bounds" this file asks for.

**D10 — the referent span is all `K` volumes.** The model does not carry a
tracked-subset span; `bumpReturn` waits for every volume. With `K = 2` this
is exactly the plan's "the bound is O(log span); with span=2 the tree is one
level" — stated, not pretended away.

**D11 — what the model-checking leg actually covers.**
`Machines/Epoch/Bmc.lean` is a *bit-level netlist* instance (`W = 3`,
`N = 2`, `K = 2`) checked with `Loom/Dp/Bmc.lean` + `Loom/Dp/KInduction.lean`
and kernel-re-checked LRAT certificates. Two honest limits:

1. `Loom.Dp.Cnf.blast` over-approximates `add`/`eq`/`ult` as *free*
   variables, so no epoch-arithmetic statement is checkable there. The
   properties checked are the Boolean-structural twins of the theorems —
   dead/poison stickiness, a dead cell's frozen counter, return-implies-all-
   acks, ack-implies-in-flight, and ok-implies-live — i.e. T-E2/T-E3/T-E4's
   and T-E5's netlist shadows. T-E1's replica-monotonicity and T-E6 are
   *not* reachable by this engine, and T-E7 is a liveness-flavoured
   existential that BMC does not address.
2. `bmc_sound`/`kinduction_sound` conclude about `Module.run … reset`, the
   *closed* run. The design is therefore self-driving (an LFSR generates the
   op/cell/volume/policy/epoch stream) so that run is a real interleaving.
   The k-induction *step* certificate (`kind_step_sound`) is nevertheless
   discharged over an unconstrained start state, so the property is proved
   1-inductive over the netlist's whole state space.

**D12 — the BMC depth actually reached is 2, not ~12.** The plan asks for
depth ~12. `Loom.Dp.Bmc.bmcCnf`'s offline construction (the `Var → Bool`
assignment threaded through `buildSteps`) blows up sharply with depth in
the *interpreter*: on this design, depth 0 → 0.5 s, depth 1 → 0.5 s,
depth 2 → 8 s, depth 3 → 3 m 48 s, depth 4 → no result in 15 min. The
bounded leg therefore
lands at depth 2 (`safeP_bmc2`, 4092 clauses / 1130 RUP steps). This costs
nothing in strength: `safeP_invariant` (1-induction, base + step) already
gives the property at *every* cycle, which subsumes any finite depth. The
blow-up is a toolchain observation worth its own issue, not a property of
the epoch model — the k-induction queries at the same design are 856 and
2436 clauses and build in seconds.

   Cost, recorded so nobody is surprised: a cold build of
   `Machines/Epoch/Bmc.lean` is ≈ 10 min, ≈ 9 of which is the kernel
   `decide` re-check of the depth-2 BMC certificate.

   The two legs are independent in the intended sense: the kernel proofs
   never mention the netlist, and the model checker never mentions
   `Protocol.St`. Layer 3 (`Refines.lean`) is what will join them.

## Deviations (Layer 2 — `Engine.lean`, `EpochSoc.lean`, recorded 2026-08-01)

Every item is a departure from, or a refinement of, this file's
§"Engine design (Layer 2)" / §"Core integration + demo" as built in
`Machines/Epoch/Engine.lean` + `Machines/Epoch/EpochSoc.lean`. Nothing was
silently narrowed. Layer-1 deviations keep their `D` numbers; Layer 2's
are `E`.

**E1 — epoch width 32, cell table 512 entries.** §"Engine design" says
"dw=39 per §3's capability-slot width; use 32 for v1 and record it" — 32 it
is. `Cfg` is a parameter, so the 39-bit and 64-bit instances are one line
away and every Layer-1 theorem already holds for all `W` (D9). A second
instance `epochengine_tiny` (`ew = 3`, 4 cells) ships alongside, because
saturation at `allOnes 32` is not reachable in a testbench and §3's
"saturation is permanent death" therefore has to be exercised at a width
where it *is* — see E7.

**E2 — there are no `ack_core0`/`ack_core1` INPUTS.** The Layer-2 port
sketch above predates this file's own §"SUPERSEDING DOCTRINE" and its
§"Consequence bound NOW". The doctrine wins: the engine owns the replica
banks and generates the acks itself, one referent volume per cycle, in
`B_ACK`. Cores drive only `req{k}_{valid,op,cell,epoch,policy,flags}` —
§3's `Req` and the op — and there is no path by which any core write
reaches a replica, the home epoch, or the poison/dead bits. Layer 3's
safety statement is therefore unconditional over all core behaviour, as
§"Consequence bound NOW" requires. `inval_valid`/`inval_cell`/
`inval_epoch` survive as *observability outputs* (the broadcast is
visible), not as a handshake.

**E3 — one check unit per volume, not one shared CHECK state.** The
sketch has a single FSM with a `CHECK` arm. Built as two independent
per-volume units plus one bump sequencer, because (i) §3's class-0 rule is
that the check is local and tile-bounded — a shared unit would serialize
two volumes' checks through one resource; and (ii) a check must not be
blocked by an in-flight bump, or §3's in-flight liberty (T-E7) would be
physically unrealizable. Unit `k` reads replica bank `k` and cannot name
any other bank.

**E4 — a check costs 3 cycles, not 1; there is no install/alloc op.**
The sketch says "CHECK: one-cycle local compare". With D19/D20
block-RAM-shaped memories the compare needs a read stage:
`C_IDLE` (accept, drive the address) → `C_RD` (the bank's registered read)
→ `C_DO` (compare, emit the outcome). It is still one compare against one
local replica with no fabric transaction, which is what §3's class-0
claim is about; the extra two cycles are the price of BRAM, and the LUTRAM
alternative is what stopped the dual core from fitting (D19). Relatedly,
v1 has **no core-visible install op**: the cell table resets to
epoch 1 / occupied / unpoisoned with both replicas in step, which is
exactly `Protocol.Init`, and is the only way freshness state is ever
established. An install op is where §3's *reuse point* lives, and this
file's §Scope already stages that out (Layer-1 D5).

**E5 — the response surface is wider than `resp_valid/resp_code(2b)/
resp_busy`.** `resp_code` is **3** bits, because `Protocol.Outcome` has
five constructors and the encoding is required to be identical to it
(`ok=0, badref=1, poisoned=2, stale=3, denied=4`). Busy is split into
`c{k}_busy` (per-volume check unit) and `bump_busy` (the one in-flight
bump), and the bump return is its own pulse `bump_done{k}` beside
`bump_cycles`, because the two paths are independent by E3. `rc`
(`referent_count`) and the `acquire`/`release` ops (Layer-1 D6) are **not
in the engine**: §"Engine design" lists only `cell_epoch`/`cell_flags`/
the replica banks, `rc` carries no safety obligation, and adding a
core-writable counter would be a new core-writable coordinate for no gain.

**E6 — the two cores share one MMIO base; what is "distinct" is the
word.** §"Core integration + demo" asks for "distinct addresses". Both
cores use `0x0A0E_0000` (one 4 KiB page carved out of the GP aperture's
existing `ea[31:20] == 0x0A0` scratch window), with distinct *words* for
cell / epoch / flags / fire-check / result / fire-bump / latency / ID.
A core's referent volume is **wired, not addressed**: core `k` reaches
request port `k` and check unit `k`. If the volume were selected by
address, an adversarial core could ask for a check against the other
volume's replica — exactly the class of thing E2's doctrine exists to
make impossible. Per-core address bases would be strictly weaker.

**E7 — what the FastEval selftest and the iverilog leg actually cover.**
`Machines.Epoch.Engine.selftest` runs the `Design` through the *verified*
fast evaluator (`fastRunOpen_agrees`, instantiated from
`Loom.Hw.FastEval.fastRunOpen_eq`), so there is no hand-written ISS to
drift (D18). Covered: check-hit; the four failure classes in §3's
precedence order (T-E4); bump → broadcast → per-volume ack (`b_acked`
0→1→3) → return, exactly one return pulse (T-E1/T-E5); poison permanence
including *current*-epoch references, 20 cycles later (T-E3); saturation
on `epochengine_tiny` — six bumps to `allOnes 3`, then `-STALE` at both
volumes and no bump revives it (T-E2); and a use concurrent with an
in-flight bump returning `ok`, then `-STALE` after the return (T-E7).
`fpga/zc702/tb_epochengine.v` replays the same two traces and prints the
same event lines, and the two outputs are byte-identical.
**Not** covered at Layer 2, by construction: anything quantified over all
runs — those are Layer 3's obligation, and the selftest is corroboration,
not proof.

**E8 — the `repl{k}` cross-port collision is architecturally free.**
Check unit `k` may read `repl{k}` in the same cycle the ack sequencer
writes it. D9 gives read-first semantics; Xilinx leaves a cross-port
same-address collision indeterminate. Every such cycle is inside an
in-flight bump (replica writes happen only in `B_ACK`, with `bump_busy`
high), and §3 explicitly permits a use concurrent with a bump to observe
either epoch (T-E7). After the return no replica write is outstanding, so
nothing observable after §3's linearization point is affected. This is the
D19 collision obligation discharged by *architecture* rather than by
timing luck — contrast `Machines/Lnp64mini/PORTING_SPEC.md` deviation 5,
which is still owed a silicon confirmation.

**E9 — `EpochSoc.lean` is additive; `DualSoc.lean` was not edited.**
`Machines/Epoch/EpochSoc.lean` reuses `DualSoc`'s five instances and its
`wire` function (falling through to it for everything it does not
override), so `rtl/lnp64mini.v`, `rtl/lnp64mini_soc.v` and
`rtl/lnp64mini_dual.v` re-emit **byte-identically** (md5 unchanged), and
all six existing iverilog system testbenches reproduce their recorded
numbers exactly: soc `loomcheck` 273 cycles; dual 372 / 12540 / 14933 /
2014 / 346 cycles, `res_kill` 39/1, `wake_out` 8/8, `shared[0x10000]=200`.

**E10 — the demo is the testbench, not the board.** §"Core integration +
demo" asks for the acceptance under live NetBSD on core 0. This pass
delivers the same *protocol* event on the same fabric in iverilog
(`fpga/zc702/tb_lnp64mini_epoch.v`, programs `epoch0.s`/`epoch1.s`): core 1
checks a live handle (`ok`), core 0 bumps through the GP aperture and its
latency read blocks until the bump returns, core 1 re-checks the SAME
handle and gets `-STALE`, and a poison bump then makes even the current
epoch fail `-POISONED`. Board and NetBSD are out of scope for this pass by
instruction. The measured bump latency is **5 cycles**
(`B_RD → B_UP → B_ACK×3 → B_RET`, i.e. issue → both volumes acked →
return), lazy and poison alike.

**E11 — FIT: LUT/BRAM measured, Fmax NOT measured.** `yosys 0.33`,
`synth_xilinx -flatten -nowidelut`, bare module (not the board wrapper):

| cell | `lnp64mini_dual` | `lnp64mini_epoch` | Δ |
|---|---|---|---|
| LUT2+3+4+5+6 | 27,409 | 28,210 | **+801 (+2.9 %)** |
| `CARRY4` | 1,049 | 1,061 | +12 |
| `FDRE`/`FDSE` | 12,389 | 12,805 | +416 |
| `RAMB36E1` | 26 | 26 | 0 |
| `RAMB18E1` | 0 | **3** | +3 |
| `RAM64M` (LUTRAM) | 48 | 72 | +24 |
| total cells | 51,262 | 53,065 | +1,803 |

`epochengine` alone: 327 LUTs, 204 FDRE, 12 CARRY4, **3 RAMB18E1**
(`cell_epoch`, `repl0`, `repl1` — 512×32 each, block RAM as D19 intends)
and 24 `RAM64M` (the 512×3 `cell_flags`, too narrow to be worth a BRAM).
The remaining +474 LUTs of the composed delta are the two `epochmmio`
adapters and the GP response muxing.

Post-route `Fmax` is **not reported**: it comes from `nextpnr-xilinx`
(openXC7) in `remote-fpga fpga/substrate0/oxc7/build_oxc7.sh`, which is
not installed on this host (`snap install openxc7` → "not found"), and
the board is out of scope by instruction. Reference points for whoever
runs it: the dual placed at 48 % `SLICE_LUTX` after D20, and the
single-core SoC ran at 35.11 MHz post-route. A +2.9 % LUT delta with the
three new banks landing in otherwise-idle RAMB18 sites is not expected to
move either materially, but that is a prediction, not a measurement, and
it is recorded as one.

**E12 — core 1 reaches the engine, and still cannot reach GEM0.**
`Machines/Lnp64mini/DUAL_SPEC.md` deviation D5 ties core 1's GP-aperture
responses to "instantly done, reads 0" (GEM0 belongs to core 0), which on
its own leaves core 1 with no MMIO at all — and the demo requires core 1 to
*hold* a reference and watch it go `-STALE`. Of the three ways out
(a separate non-GP decode window; lifting D5 for one address range; a
dedicated request port per core) this build takes the **third, plus a
sub-window of the GP aperture that is not GEM's**:

* the engine has one request port per referent volume
  (`req0_*` / `req1_*`), which is the doctrine's own abstraction — the
  engine already owns per-volume state, so a per-volume request port is
  the matching seam, and no address a core can name reaches the other
  volume's port (E6);
* each core gets its own `epochmmio` adapter, selected by
  `gp_addr_r[31:12] == 0x0A0E0` — inside the core's *existing*
  `ea[31:20] == 0x0A0` scratch window, and disjoint from GEM0's
  `0xE000_B000`, which lives in the other half of the decode
  (`ea[31:16] == 0xE000`). The core's decode is therefore **unchanged**,
  which is what keeps `lnp64mini.v` byte-identical (E9);
* D5's tie-off survives verbatim for everything else: core 1's
  `gp_done`/`gp_rdata` are `epSel1 ? mm1_* : (1, 0)`. A core-1 access to
  any non-engine GP address still completes instantly reading 0.

Structural proof in the emitted netlist: `c1_gp_rd`/`c1_gp_wr` fan out
**only** into the `mm1_` adapter cone; the AXI GP master's
`gpm_start_rd`/`gpm_start_wr`/`gpm_addr`/`gpm_wdata` are driven from
`c0_*` alone (and gated with `¬epSel0`). Behavioural proof in
`tb_lnp64mini_epoch.v`: core 1 probes `0xE000_B000` after its epoch work
and reads `0` without wedging (`c1.r11 = 0`, `C1 HALTED=1`).

### Guest-visible register map (Layer 2, as built)

Base **`0x0A0E_0000`**, identical for both cores; 32-bit accesses only
(`ST.W` / `LD.W`, opcodes 0x34 / 0x31 — the GP aperture traps other
widths). This differs from the provisional guest header
(`lnp64/toolchain/include/lnp64/epoch_mmio.h`, base `0xE010_0000`,
`ID/CELL/REF/CHECK/BUMP/STATUS/LAT/HOME`); `0xE010_0000` is **not**
decodable by this core at all (`l_is_gp` matches `ea[31:16] == 0xE000`,
not `0xE010`), so adopting it would require changing the core's decode and
forfeiting the byte-identical guarantee.

| off | write | read |
|-----|-------|------|
| `+0x00` `EP_CELL`   | cell index (9 bits) | cell index |
| `+0x04` `EP_REF`    | the presented reference epoch (§3's `ref.epoch`) | same |
| `+0x08` `EP_FLAGS`  | `{rights<<2, classOk<<1, wellFormed}`, resets to 7 | same |
| `+0x0C` `EP_CHECK`  | **fire a check** (data ignored) | `{chk_pend<<1, chk_busy}` |
| `+0x10` `EP_RESULT` | — | `valid<<8 \| Outcome`; **the load blocks** until the check answers, then clears `valid` |
| `+0x14` `EP_BUMP`   | **fire a bump**, `bit0` = poison policy | `{bmp_pend<<1, bump_busy}` |
| `+0x18` `EP_LAT`    | — | last bump's issue→all-acked→return latency in cycles; **the load blocks until the bump returns** (§3's linearization point) |
| `+0x1C` `EP_ID`     | — | `0xE90C0001` |

Outcome codes are `Protocol.Outcome`'s constructor order and match the
provisional header: `0 = OK, 1 = BADREF, 2 = POISONED, 3 = STALE,
4 = DENIED`.

Two intentional differences from the provisional map, beyond the base:

* **`EP_FLAGS` exists.** Layer-1 deviation D4 makes the structural and
  rights facts request-level booleans; without them §3's precedence
  (`-BADREF` / `-DENIED`) is unreachable from software. It resets to 7, so
  a guest that only ever does plain checks never has to write it.
* **There is no `HOME` register.** Exposing the home epoch would let
  software compute freshness itself, which is exactly what §3's safe-reuse
  corollary forbids ("established by the engine, never asserted by
  software"). `EP_RESULT` is the only architected answer to "is this
  reference fresh".

A blocking-read map means the usual sequence has **no polling**:

```
ST.W [base,  0], cell        ; stage the handle …
ST.W [base,  4], ref_epoch   ; … (both cores may do this concurrently)
ST.W [base,  8], 7
ST.W [base, 12], r0          ; fire CHECK
LD.W rd,  [base, 16]         ; blocks; rd = 0x100 | outcome

ST.W [base,  0], cell
ST.W [base, 20], policy      ; fire BUMP (0 = lazy, 1 = poison)
LD.W rd,  [base, 24]         ; blocks until the bump has RETURNED
```

`fpga/zc702/epoch0.s` (bumper) and `fpga/zc702/epoch1.s` (holder) are the
worked examples.

## Deviations (Layer 3 — `Refines.lean`, recorded 2026-08-01)

Layer 3 discharges this file's `Machines/Epoch/Refines.lean` obligation: the
Loom `Design` of Layer 2 refines the mechanized §3 protocol of Layer 1, and
§3's safety theorems are transported onto the hardware. Layer-1 deviations
keep their `D` numbers, Layer 2's their `E`; Layer 3's are `F`.

**F1 — the concrete system is the OPEN design, quantified over all input
valuations.** `Refines.sysOpen d` has `init σ = (σ = d.reset)` and
`step σ σ' = ∃ ι, d.cycleOpen ι σ = σ'`. The existential over the input
valuation is the mechanized form of §"Consequence bound NOW": the two request
ports are the cores' only reach into the engine, and the step relation admits
*every* value they could ever present, on every cycle. `abs_setInputs` then
proves that no input name is a coordinate the abstraction reads. **There is
no hypothesis about core behaviour anywhere in Layer 3** — the safety
statement is unconditional over all input traces, adversarial cores included,
as this file requires.

**F2 — the abstraction's `rc` is `0`, and every address is a cell.**
`abs σ` reads `cells` out of `cell_epoch`/`cell_flags` (poison/dead/occupied
= bits 0/1/2), `repl k` out of `repl{k}`, and `pending` out of the bump
sequencer. `Protocol.Cell.rc` is `0` at every cell because the engine has no
referent counter (E5) and `rc` appears in no invariant or safety theorem. The
cell count is `N = 2 ^ aw`: every address in the bank is a cell, so `use`'s
out-of-range `-BADREF` arm (Layer-1 D4) is unreachable at the design level —
range checking lives in the MMIO adapter, not the engine.

**F3 — `pending` is `some` exactly in `B_ACK`/`B_RET`, not "everything but
`B_IDLE`".** The natural reading of the sequencer would make any non-idle
state a bump in flight. That is not a refinement: in `B_RD`/`B_UP` the home
epoch has not yet been incremented, and `Protocol.stepEv (.bump …)` increments
the home *and* creates `pending` in one event. The abstract `bump` is
therefore the `B_UP → B_ACK` cycle, where the memory write, `b_target` and
the broadcast commit together; `B_IDLE → B_RD` (accepting a request) and
`B_RD → B_UP` (the D19 read stage) are stutters at `pending = none`. Anything
else would need a protocol step that moves the epoch without a bump.

**F4 — one design invariant, and it is about the sequencer, not the cores.**
The simulation is stated on `(sysOpen d).reachablePart` and needs
`Refines.DInv`, two facts:
(i) `b_st = B_UP → b_epoch_q = cell_epoch[b_a] ∧ b_flags_q = cell_flags[b_a]`
— the D19 read-stage discipline, without which the increment the engine
commits need not be `satInc` of the *current* home epoch; and
(ii) `b_st = B_RET → both ack bits set` — without which the return would not
be `bumpReturn`-enabled. Both are proved by `dinv_cycle`, which shows they
hold after **every** cycle from **every** state, so `DInv` is inductive with
reset as its only base case. Restricting to reachable states is not
conditionality: the delivered theorems are `(sysOpen d).Invariant`-shaped,
i.e. statements about every reachable state of the design.

**F5 — the one side condition is `2 ≤ ew`, a geometry fact.** At `ew = 1` the
reset epoch `1` *is* `allOnes`, so the reset image would not satisfy
`Protocol.Init` (`deadIffMax`) and the engine would boot dead. Both shipped
instances satisfy it (`cfg32.ew = 32`, `cfgTiny.ew = 3`); it is a constraint
on the parameterization, not an assumption about the environment.

**F6 — D25 (prophecy/history variables) was NOT needed; the entry is
closed.** `LOOM_GAPS.md` predicted that a commit point depending on "which
volume acks last" would defeat forward simulation. It does not, and the
reason is architectural rather than lucky: because the engine owns the
replicas and generates the acks itself (E2), the per-volume ack vector is
*architectural state* (`b_acked`), not a fact about the future, and the
"whole span has acked" precondition of the return is an inductive invariant
of the sequencer (F4-ii). A plain `StutterSimulation` suffices. Had the acks
come from cores — the design this file's doctrine forbids — the ack vector
would have been an environment observation and D25 would have bitten.

**F7 — what the transported theorems say, and what they do not.**
Delivered, each `∀` over reachable states, input traces and cycle counts:
`design_inv` (`Protocol.Inv`), `T_E1_design` / `T_E1_design_never_ok`,
`T_E2_design`, `T_E3_design`, `T_E6_design`, plus `chk_resp_0` / `chk_resp_1`
— the check unit's 3-bit `resp{k}_code` is exactly `Protocol.useLocal`
(§3's precedence: the design-level T-E4) applied to the latched request and
volume `k`'s replica, and to *no other volume's* (E6).
**Not proved, and stated rather than hidden**: that the values a check unit
latched still equal the memory contents at that address when it answers. That
is *false in general* during an in-flight bump — it is exactly E8's
cross-port collision, which §3 licenses as in-flight liberty (T-E7). Tying a
check's answer to a *specific* memory snapshot therefore needs a history
variable and belongs with a future v2 that also replicates the poison bit
(D2). The freshness state itself is fully covered: T-E1's "forever" is over
`Protocol.Run`, which `run_abs` proves is what running the fabric does.

**F8 — the cycle bound, and its relation to the measured 5 (D28).** Three
numbers, kept apart on purpose:
* **15 cycles — the transported bound.** `bump_returns_within_15_cycles` /
  `bump_bounded_response`: the spec bound `K + 1 = 3` steps
  (`Machines/Epoch/Bounded.lean`) through `StutterSimulation.
  boundedResponse_pullback` with stutter budget `b = 3` gives
  `3 * (3+1) + 3 = 15` **clock cycles**. This is the number that comes for
  free from the spec, and it is a *sound over-approximation*: the pullback
  charges `b+1` cycles for every protocol step whether the design spends them
  or not.
* **4 cycles — the exact bound.** `bump_returns_within_4_cycles`, by a direct
  ranking on the same cycle-accurate system: two acks (one volume per cycle),
  the move to `B_RET`, and the return. This is the number to hold silicon to.
* **5 cycles — Layer 2's measurement** (E10, `bump_cycles`). It is a
  *different interval*: the counter is zeroed when the request is accepted
  (`B_IDLE → B_RD`) and read at the return, so it spans `B_RD`, `B_UP` and
  the four cycles the proof bounds, minus one for the counter's start offset
  — issue at cycle 0, return at cycle 6, counter reads 5. The proved 4 covers
  the sub-interval from §3's `bump` event (the home increment and broadcast,
  `B_UP → B_ACK`) to §3's linearization point (the return), which is the
  interval the *protocol* bound is about. So: 4 is exact and proved, 15 is
  proved and loose, and the measured 5 is consistent with both — it is not
  the same quantity as either, and this paragraph exists so that nobody
  reports it as if it were.

**F9 — the theorems reach the emitted RTL.** Everything is stated about
`Design.cycleOpen`; `design_wf` / `tiny_wf` discharge `Compile.DesignWF` in
the kernel and `emitted_cycleOpen` instantiates the D-series emission theorem,
so one cycle of the emitted µVerilog module is one cycle of the `Design` these
theorems quantify over. Post-synthesis is D22's job (eqcheck), unchanged.

## Deviation E13 — the reset image the target flow will not deliver (recorded 2026-08-01, found on silicon)

**The defect.** On the ZC702, under live NetBSD, the guest's `epoch` command
reported

```
epoch engine present; reference(cell 0, epoch 1) -> -BADREF
```

for a *live* cell — the same reference that the iverilog cross-core testbench
answers `ok`. The ID register read back `0xE90C0001`, so the MMIO path, the
address decode and the whole register file were sound; only the freshness
answer was wrong.

**Root cause.** `cell_flags`' reset image was not on the fabric. Loom expresses
a `MemDecl`'s reset image as a Verilog `initial` block, which iverilog honours
exactly. On the openXC7 path (yosys → nextpnr-xilinx → fasm2frames →
xc7frames2bit) that image survives **only for memories yosys maps to block
RAM**. yosys 0.38 mapped the three 512×32 epoch banks to `RAMB18E1` and carried
their `INIT_xx` faithfully (each 32-bit word = 1), but mapped the 512×3
`cell_flags` bank to *distributed* LUT RAM (`RAM64M`) — and the distributed-RAM
mapping **silently discards a non-zero init**, emitting `INIT_A..INIT_D = 0`.
No warning is issued at any stage of the flow.

With `cell_flags = 0` the occupancy bit (`FLAG_OCC`, bit 2) was clear, so
`Protocol.useLocal` entered the empty-slot clause; and because the *replica*
bank **had** initialized correctly to epoch 1, the presented epoch 1 matched,
which is precisely §3's matching-epoch-empty case — `-BADREF`. The board's
choice of `-BADREF` over `-STALE` is itself the proof that the BRAM init
survived and the LUTRAM init did not.

**The evidence that settled it**, in three independent forms:

1. *Netlist.* In `oxc7/out/lnp64mini_epoch_top.json`,
   `u_dual.ep_cell_epoch`/`ep_repl0`/`ep_repl1` are `RAMB18E1` with
   `INIT_00 = …0000001…` per 32-bit word, while `u_dual.ep_cell_flags.0.*`
   are 24 `RAM64M` cells with `INIT_A = INIT_B = INIT_C = INIT_D = 0` —
   against a source image of `3'd4`.
2. *Simulation.* Zeroing **only** `ep_cell_flags`' `initial` block in the
   emitted RTL and re-running the unmodified cross-core testbench turns
   `EPOCH DEMO OK` into `EPOCH DEMO FAILED` with
   `c1.r9(live check) = 257`, i.e. `-BADREF` — the board's symptom, exactly,
   and with the other four checks degrading exactly as the fabric's did.
3. *Board.* `scripts/board/epoch_demo.tcl` reads core 1's independently held
   reference out of DDR and reports `-BADREF` from lap 1 — a second,
   separate path to the engine reaching the same wrong answer.

**The fix, and why this one.** The engine must not depend on a memory reset
image the target flow cannot deliver. Two structural options were on the table
— a reset sweep that writes the reset cell state after `rst` (lnp64mini's
zeroing-engine shape), or a core-visible install/provision op — and both were
rejected: a sweep makes `abs(reset)` no longer `Protocol.Init`, which
invalidates `init_ok`, `dinv_reset` and every top-level theorem stated over
`runOpen ιs n design.reset`; an install op is a Layer-1 change (it contradicts
E4) for state that v1 never varies.

The chosen fix is narrower and removes the dependence rather than working
around it: **occupancy is not stored.** v1 has no install/free op (E4), so no
rule ever writes `cell_flags` bit 2 — `bumpedFlags` ORs into the read value and
leaves it alone — which makes the bit a memory-resident *constant* whose only
source is the reset image. The check unit now sources §3's empty-slot clause
from the constant `1` instead of from `flags_q[2]`, `cell_flags`' reset image
becomes **all-zero**, and bit 2 is renamed `FLAG_RESERVED` and held for the v2
install/free op. An all-zero image is one every configuration path delivers,
LUTRAM included.

After the fix the only banks carrying a non-zero reset image are the three
epoch banks, which are exactly the banks the flow maps to block RAM and whose
`INIT` it demonstrably does deliver.

**Layer 3 is unchanged in substance.** `Refines.abs` was edited in one place —
`absCells.occupied := true` (and `chkCell.occupied := true`, its check-unit
twin) — so the abstraction still mirrors the hardware exactly and the
refinement stays an equality, not a weakening. `reset_mem_flags` now states
`= 0#3`. `outcome_eval` loses one of its seven `by_cases` splits (64 cases
instead of 128). `Protocol.Init` does not constrain `occupied`, so `init_ok`
is unaffected; `T_E1_design` / `T_E3_design` keep their `occupied = true`
hypotheses, now discharged by `rfl`. No theorem statement about the protocol
was weakened, no `sorry` and no new axiom was introduced, `lake build` and
`lake exe audit` are green, and `scripts/epoch_ladder.sh` passes end to end
(the iverilog engine ladder is still byte-identical to the FastEval oracle).
The one observable change is the flag word the demo prints after a poison
bump: `flags[5] = 5` becomes `flags[5] = 1`, occupancy no longer being stored.

**The standing guard: `scripts/check_mem_init.py`.** The real hazard here is
not the one bank; it is that the flow drops a reset image *without saying so*,
so no amount of proof about the `Design` can catch it. The guard re-derives
every memory's reset image from the emitted RTL and checks it against the yosys
netlist: a non-zero image must be mapped to BRAM **and** that primitive must
carry a non-zero `INIT_xx`; an all-zero image must be matched by all-zero
`INIT`s. Run against the *pre-fix* netlist it reproduces the defect from the
netlist alone, with no board and no simulation:

```
FAIL ep_cell_flags: reset image is NON-ZERO but yosys mapped it to distributed
     RAM (RAM64M, e.g. u_dual.ep_cell_flags.0.0); that path discards the init
     and the bank comes up all-zero on silicon
```

**A second finding, recorded and not fixed here.** The same guard shows that
`c0_tpc` and `c1_tpc` — lnp64mini's 32×64 trap-PC tables, reset image
`64'd4096` — are mapped to `RAM32M` and lose their init on this flow too. It
is latent rather than live: the guest installs its trap vectors before it takes
a trap, so NetBSD's four-trap boot never reads an uninitialized entry. It is
outside this campaign's scope, it is now visible to a script instead of to a
board, and it should be closed the same way — by giving the table an all-zero
reset image and biasing the vector, or by forcing the bank to block RAM.

## E13 acceptance — the demo on silicon (2026-08-01, verbatim)

Bitstream `lnp64mini_epoch_top.bit` rebuilt from the post-E13 RTL (openXC7,
50% SLICE_LUTX, `sysclk` fmax 25.89 MHz against the 12 MHz constraint);
`netbsd-fabric.service` restarted; `PASS 20260801-163134`, NetBSD serving
native GEM0 dual-core with BSCAN quiet. The guest image is **unchanged** —
E13 is a fabric-side fix only, and the guest's `LNP64_EPOCH_FLAGS` is the
*request* word (wf/class/rights), unrelated to `cell_flags`.

**1. A current reference reads `ok`** (telnet into the on-core shell) —
the check that returned `-BADREF` before the fix:

```
core$ epoch engine present; reference(cell 0, epoch 1) -> OK  (try: epoch bump | epoch poison | epoch check <e>)
```

**2. Core 1's independently held reference agrees** (`scripts/board/
epoch_demo.tcl`, reading the SMP gate out of DDR over BSCAN — the engine's
second volume, reached by a path that shares nothing with the shell's):

```
== epoch demo observer ==
BEFORE laps=4921 held_epoch=1 checks=4921 last=OK first_fail_lap=none
+5s    laps=4960 held_epoch=1 checks=4960 last=OK first_fail_lap=none
checks in 5s: 39
STATE: reference still current (no bump has returned yet)
EPOCH_DEMO_DONE
```

**3. `epoch bump` returns, and prints the measured issue→all-acked cycles.**
The old reference is stale the moment the bump returns:

```
core$ bump returned (all volumes acked) ack_cycles=5
core$ epoch engine present; reference(cell 0, epoch 1) -> -STALE  (try: epoch bump | epoch poison | epoch check <e>)
```

`ack_cycles=5` is E10/F8's measured interval, on silicon, equal to the number
Layer 2 measured in simulation — consistent with the proved exact bound of 4
for the sub-interval `B_UP → return` and with the transported bound of 15.

**4. Core 1's held reference goes `-STALE` and STAYS `-STALE`** across
samples — §3's return guarantee and T-E1, observed on the fabric. Note
`first_fail_lap=5016`: core 1 was re-presenting the same handle every lap and
flipped exactly once, at the lap the bump returned.

```
== epoch demo observer ==
BEFORE laps=5131 held_epoch=1 checks=5131 last=-STALE first_fail_lap=5016
+5s    laps=5172 held_epoch=1 checks=5172 last=-STALE first_fail_lap=5016
checks in 5s: 41
STATE: reference is -STALE since lap 5016
+10s   laps=5213 held_epoch=1 checks=5213 last=-STALE first_fail_lap=5016
HOLDS: still -STALE -- stale/poison fails forever
EPOCH_DEMO_DONE
```

**5. `epoch poison` fails closed permanently** — and, per §3's precedence,
*even for the current epoch*: after `poison` the home epoch is 3, and
presenting 3 still returns `-POISONED`, because poison is inspected before the
freshness compare (T-E3):

```
core$ poison bump returned (all volumes acked) ack_cycles=5
core$ check epoch=2 -> -POISONED
core$ check epoch=3 -> -POISONED
```

```
== epoch demo observer ==
BEFORE laps=5437 held_epoch=1 checks=5437 last=-POISONED first_fail_lap=5016
+5s    laps=5476 held_epoch=1 checks=5476 last=-POISONED first_fail_lap=5016
checks in 5s: 39
STATE: reference is -POISONED since lap 5016
+10s   laps=5516 held_epoch=1 checks=5516 last=-POISONED first_fail_lap=5016
HOLDS: still -POISONED -- stale/poison fails forever
EPOCH_DEMO_DONE
```

The guest was healthy throughout and after: `5 packets transmitted, 5
received, 0% packet loss` on GEM0, and `uname` over telnet still answers
`NetBSD lnp64mini3 (rump) on ZC702 PL fabric`.

Post-fix, `scripts/check_mem_init.py` against the rebuilt netlist reports
`ep_cell_flags: all-zero reset image, ['lutram'] with zero INIT` and
`check_mem_init: OK -- 14 memories checked, 2 acknowledged`.
