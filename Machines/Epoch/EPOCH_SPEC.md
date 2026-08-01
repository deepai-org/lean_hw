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
