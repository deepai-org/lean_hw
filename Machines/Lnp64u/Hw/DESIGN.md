# LNP64-µ core in the EDSL (task 1.11) — design

**Named win (Rule 5):** the spec is already cycle-accurate (P7) — one spec
`step` is one cycle, retirement atomic. So the core is a **direct
implementation: 1 hardware cycle = 1 spec cycle**, and R-MC is a *plain*
`Simulation` (abs per field), not a stuttering one. The frozen µ parameters
(4 domains, 8 regs, 16 slots, 16 cells, 4 gates, 12-bit addresses) make full
structural unrolling synthesizable.

## State encoding (the `abs` contract)

One EDSL register per scalar spec field; `Fin`-indexed families become
register families with numbered names. `Option` is a valid bit + payload.
All names are `snake` with numeric indices, e.g. `d2_reg5`.

| spec field | registers | width |
|---|---|---|
| `(doms d).reg r` | `d{d}_reg{r}` | 32 |
| `.pc` | `d{d}_pc` | 12 |
| `.caps s` | `d{d}_cap{s}_v` 1, `d{d}_cap{s}_kind` packed 32 | see below |
| `.caps s |>.lineage` | `d{d}_cap{s}_lin_v` 1, `d{d}_cap{s}_lin` 4 |
| `.slotGen s` | `d{d}_gen{s}` | 8 |
| `.lineage l` | `d{d}_cell{l}_v` 1, `d{d}_cell{l}_par` 14 (dom 2 ∥ slot 4 ∥ gen 8) |
| `.regions r` | `d{d}_rgn{r}_v` 1, `d{d}_rgn{r}` packed (backing 14 ∥ base 12 ∥ len 13 ∥ perms 3) |
| `.run` | `d{d}_run` 2 (00 running, 01 halted, 10 blocked) + `d{d}_run_g` 2 |
| `.serving` | `d{d}_srv_v` 1, `d{d}_srv` 2 |
| `.cause` | `d{d}_cause` 32 |
| `.budget` | `d{d}_budget` 32 (Nat, bounded by quota ≤ period) |
| `.maxDonation` | `d{d}_maxdon` 32 (constant after reset) |
| `gates g` | `g{g}_callee` 2, `g{g}_entry` 12; act: `g{g}_act_v` 1, `g{g}_caller` 2, `g{g}_callerrd` 3, `g{g}_sreg{r}` 32 ×8, `g{g}_spc` 12, `g{g}_ssrv_v`+`g{g}_ssrv` (always 0/-, kept for abs fidelity), `g{g}_depth` 3, `g{g}_don` 32 |
| `mover` | `mov_v` 1 + packed job fields (src 14, dst 14, srcCur/dstCur 12, remaining 13, owner 2, statusAddr 12) |
| `inflight` | `if_v` 1, `if_dom` 2, `if_word` 32, `if_cl` 8 |
| `cycle` | `cycle` 32 |
| memory | EDSL `mem "mem"`: addrWidth 12, dataWidth 32 (single write port — the spec writes at most one word per cycle: store XOR mover-word XOR status; enforce mutual exclusion in the rule structure, required by the compiler's one-port fold) |

`kind` packing (32): bit 0 tag (0 = mem, 1 = gate); mem: base [12:1], len
[25:13], perms [28:26] (r,w,x); gate: gid [2:1].

**Memory-write exclusivity.** The spec can write TWO memory words in one
cycle: on a mover job's final data word (`remaining = 1 → 0`), `moverPhase`
writes the destination word *and* the completion status word. A retiring
`sw` plus a mover word in the same cycle is likewise two writes. The EDSL /
µVerilog memory has ONE write port, and the compiler's `memPort` fold merges
writes only across `ite` branches (a second executed write silently wins).
**Decision (Rule 2 — the consuming machine drives the toolchain feature):
Loom gains a verified second write port.** `MemDecl`/`MemDef` get a second
guarded port (`wr2`), `Module.cycle` commits port 1 then port 2 (port 2
wins on address collision — document it), the compiler assigns the core
phase's store to port 1 and the Mover phase's write(s) to port 2 via a
per-rule port annotation (or: `memPort` folds rules 1–2 into port 1 and
rules 3+ into port 2 — pick the cleanest), and the memory half of the
emission theorem extends to both folds. The Mover-phase dst+status
double-write within one rule still needs care: dst and status are distinct
addresses in the same cycle — so the Mover rule itself needs both ports
(dst on port 1 when the core phase didn't store — the spec's core-store and
mover-write can also collide!). Port budget: core store (1) + mover dst (1)
+ mover status (1) = up to THREE writes per cycle in the worst case
(sw retiring + final mover word). ⇒ implement `wrPorts : List Port`
(bounded write-port LIST, compiler emits one `always` write per port,
last-port-wins), with the fold-correctness lemma proved once over the list.
The spec's three writers are pairwise-distinct addresses in the colliding
cases? NOT guaranteed (a store can target the status address) — spec
semantics applies core store first, mover writes after (phase order), so
port order = phase order gives exactly spec behavior. Land `wrPorts` BEFORE
the mover circuit; the Acc8 design uses one port and its proofs must keep
working (list of one).

**Landed (task 1.11).** `wrPorts` + `Act.memWrite port` exist; the core
rule folds ALL its memory writers (`sw` stores and the sweeps' Mover-status
writes, mutually exclusive per retirement) into ONE syntactic port-0 write
at the dispatch level (`SysOps.retireMemFor` muxes), and the Mover rule
carries one syntactic port-1 write (data word) and one port-2 write
(status). `designTrace = [0, 1, 2]` therefore satisfies `MemWriteWF`'s
strictly-increasing-port condition *by construction* (checked at run time
in `Tests/Lnp64uCore.lean` together with register-name `Nodup` — the
emission theorems' preconditions).

**Cross-phase visibility (D9 vs the spec's phase composition).** The Mover
phase runs on the *post-core* state, but EDSL reads are pre-cycle; the
Mover rule therefore re-derives every post-core signal it consumes as
expressions over the pre-cycle state (`SysOps.moverAct`): the retiring
`move`'s new job, the sweeps' job-clear (`killedByCoreE`), capability
liveness (live-pre ∧ not-killed-this-cycle), post-core region registers
(map/unmap installs + sweeps) for the status-write authority, and the
same-cycle `sw`-store forwarded into the source-word read. Reachability
simplifications used by the sweeps (valid regions have live backings; live
Mover jobs hold live refs — every kill sweeps) are recorded in
`SysOps.lean`; the Phase-3 R-MC proof carries the matching invariant.

## Rules (ordered; later writes win = phase order)

1. `refill` — per domain: `if cycle % P_d == 0 && cycle != 0 then budget := Q_d`
   (P, Q from the manifest, baked as literals at design-generation time; the
   design is `def core (m : Manifest) : Design`).
2. `core` — the big one: if `if_v` then countdown/retire (decode `if_word`,
   dispatch the 25 exec circuits, all writes guarded by the retire
   condition), else schedule → fetch → decode → charge → latch in-flight.
3. `mover` — one word per the spec's moverPhase.
4. `tick` — `cycle := cycle + 1`.

Decode is structural on `if_word` bit fields (D1 layout: opcode [5:0], rd
[8:6], rs1 [11:9], rs2 [14:12], imm17 [31:15]).

`cap_revoke`'s marks fixpoint: the planned fully-unrolled 64× `markStep`
is NOT viable — `Expr` has no sharing, so composing iterations in one
combinational expression multiplies the tree by ~65 per iteration.
**Implemented instead (the design's own "optimization path", upgraded):
a pointer-doubling mark engine in hidden registers** (`rv_j/rv_v/rv_r`,
one node per machine slot; `abs` ignores them). `marks` equals the
reachability closure "parent chain of live-generation hops ending at the
revoked root", and pointer doubling (`R += V ∧ R[J]; V &= V[J]; J := J[J]`)
reaches all chains of length `≤ 2^k` after `k` rounds — 7 rounds suffice
for 64 nodes. The engine initializes on the first countdown cycle
(`if_cl = revokeCost`; cap tables and the issuer's registers are provably
stable while an instruction is in flight — only retirements mutate them)
and runs one round per remaining countdown cycle (22 ≥ 7); retirement
consumes the converged vector. Registers are the only sharing mechanism in
the EDSL — this is the pattern for any multi-stage combinational fixpoint.

## Verification ladder

- Lockstep: `Tests/Lnp64uCore.lean` runs `core m` vs the ISS, comparing
  `abs` per cycle (full state): the base-op manifest (256 cycles) and the
  system-op demo manifest (`Hw/Demo.lean`, 2000 cycles, every system op).
- Emission: `lake exe emit lnp64u` emits `rtl/lnp64u.v` + a generated
  ISS-golden testbench; `scripts/lockstep_lnp64u.sh` runs iverilog against
  the goldens and yosys for synthesis-cleanliness. **Standalone script —
  deliberately NOT in `scripts/ci.sh`** (the emitted core is large; see
  the script's timings).
- R-MC (Phase 3): `Simulation (machine m) (core m).toTSys` with `abs`;
  plain simulation by the 1:1 cycle design decision.
