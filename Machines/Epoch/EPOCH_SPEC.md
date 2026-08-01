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
