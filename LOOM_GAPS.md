# The capability ledger: what building real machines taught Loom

**The method.** Loom's capabilities are discovered by need, not designed in
advance. Every campaign drives a real artifact onto real silicon; every point
where the toolchain forces a workaround becomes a numbered decision (D-series,
`Loom/Hw/DESIGN.md`) rather than a hack. This file is the standing ledger:
closed gaps as evidence the method works, and *predicted* gaps for the work in
flight so they are built deliberately instead of discovered mid-proof.

**The rule**: friction is a ledger entry. If a proof needs a side condition the
architecture does not require, or a design needs a shape the EDSL cannot say,
that is a Loom defect — record it here before working around it.

## Closed (each discovered by a campaign, not by design)

| D | Capability | Discovered by |
|---|---|---|
| D9 | last-write-wins rule semantics (= NBA) | the first core port |
| D12–D14 | decidable read-validity / emission / CSE-identifier checks | the release-certificate path |
| D15 | input ports as environment-owned coordinates | the substrate ports (a JTAG regfile is not a closed system) |
| D16 | compose: prefixed / par / connect | the all-Lean SoC |
| D17 | StutterSimulation + verified `retimeReg` | pipeline-aware refinement |
| D18 | verified fast evaluator (retires hand-written ISSes) | mini-scale proof/eval cost |
| D19/D20 | sync-read + thread-table memories (BRAM inference) | the dual core did not fit |
| D21 | CDC contract: verified toggle-sync + `CmdPulseTrace` | the wrapper boundary |
| D22 | post-synthesis equivalence checking (LRAT-certified) | the yosys-adequacy assumption |
| D23 | bounded response (`MustReach`), ranking rule, transport across `Simulation`/`StutterSimulation` | the epoch demo's acceptance criterion: bump-return within the ack bound |
| D25 | **closed as not needed** — plain `StutterSimulation` carried the engine refinement; see below | the epoch Layer-3 refinement |
| D31 | memories inside the post-synthesis equivalence check: reset images, write-port pins, both read shapes | D30 — the epoch engine's first silicon `-BADREF`, i.e. a bank whose reset image the flow dropped where the checker could not look |
| D32 | the eqcheck CNF encoder proved (side A: UNSAT ⟺ the two transition functions agree, normalization included) | D22 itself — the checker's verdict carried an "*if* the encoding is faithful" that no other link in the chain has |
| D28 | steps-to-cycles: a spec bound transported through a design with stutter budget `b` is a number of CLOCK CYCLES | the epoch Layer-3 refinement |

### D23, in detail (closed 2026-08-01)

**Shipped** — `Loom/Core/Bounded.lean` (capability) and
`Machines/Epoch/Bounded.lean` (the artifact that needed it):

* `MayReach Q n s` (`EF≤n`), `MustReachOrBlock Q n s` (`AF≤n`, deadlock
  tolerated) and `MustReach Q n s` (`AF≤n` **plus** an enabledness witness at
  every pre-response state). `BoundedResponse P Q K` = "from every reachable
  `P`-state, `MustReach Q K`". The all-paths reading is not left to the
  definition's shape: `MustReachOrBlock.on_path` proves that every explicit
  path of length `n` out of `s` contains a `Q`-state.
* The **enabledness decision, made explicit**: over a relation that may block,
  `AF≤K` is vacuously true at a stuck non-`Q` state, which is not a hardware
  bound. So `MustReach` carries the "can step" obligation, `MustReachOrBlock`
  does not, and every theorem that produces the former takes the concrete
  enabledness hypothesis as an argument rather than assuming totality.
* The **workhorse**: `TSys.Ranking Q Dom μ` (progress off `Q`, `Dom` closed,
  `μ` strictly decreasing) with `Ranking.mustReach : μ s ≤ n → MustReach Q n s`
  and `boundedResponse_of_ranking`.
* **Transport**: `Simulation.mustReachOrBlock_pullback` (no side conditions),
  `Simulation.mustReach_pullback` / `boundedResponse_pullback` (same bound `K`,
  given implementation enabledness), and
  `StutterSimulation.mustReach_pullback`: with a stutter rank `≤ b` that
  strictly decreases on every stuttering step, a spec bound `K` becomes an
  implementation bound `K*(b+1) + rank s`, hence `K*(b+1) + b`.
* **The artifact**: `Machines/Epoch/Bounded.lean` proves the epoch protocol's
  ack bound without touching the frozen `Protocol.lean` — under the ack-phase
  schedule `ackSys` (each step is a *fresh* ack or the return, and each step is
  a genuine `Protocol.Step`), `bumpReturn` is enabled within `K` steps and the
  bump has returned within `K + 1`, on all paths, with no deadlock. The
  fairness hypothesis is shown to be load-bearing rather than decorative:
  `unbounded_without_fairness` proves that in the *unrestricted* protocol a
  bound of any size implies the bump had already returned (`use` is an
  always-enabled self-loop).

**Not covered.** Unbounded liveness and fairness proper (`◇`, `□◇`, weak/strong
fairness) remain out of scope — there is no fairness algebra here, and a
property with no nameable `K` gets no support. The bound is over *steps of the
transition system*, not cycles: converting a proved `K` into a silicon number
requires a steps-per-cycle argument at the refinement that introduces the clock
(D23's "link to measured silicon cycles" is therefore deferred to the engine
refinement, which is where the cycle-accurate system exists). Nested/until
temporal formulae, past-time operators, and any automaton-based specification
language are absent; the response predicate is a plain state predicate.
Transport is forward-simulation-shaped, so a refinement needing prophecy (D25)
must be repaired there first — a bound cannot be pulled through a simulation
that does not exist.

## Predicted, for engine verification (the epoch campaign and beyond)

**D24 — rely-guarantee as first-class.** `CmdPulseTrace` (D21) is a hand-rolled
instance: a Prop on input traces that a design's theorems may assume. The
external-state doctrine (`Machines/Epoch/EPOCH_SPEC.md`) needs the general
theory: environment predicates, theorems quantified over all environments
satisfying `Φ`, satisfiability witnesses so a rely is provably non-vacuous, and
composition lemmas (rely of the whole from relies of the parts) that agree with
D16's `connect`.

**D25 — refinement toolkit beyond stutter. CLOSED 2026-08-01, as *not
needed*.** The prediction was that a hardware engine committing over several
cycles what the spec commits atomically would need prophecy or a
backward/history-indexed simulation, "when the commit point depends on the
future (which volume acks last)". It did not bite in `Machines/Epoch/
Refines.lean`, and the reason is worth recording because it is architectural,
not accidental: the engine **owns** the replicas and generates the acks itself
(EPOCH_SPEC deviation E2), so the ack vector is architectural state
(`b_acked`), not an observation of the environment's future, and
"the whole referent span has acked" — the enabling condition of §3's return —
is an ordinary inductive invariant of the sequencer. A plain
`StutterSimulation` (D17) plus one two-clause design invariant discharged the
whole obligation. Had the acks been *inputs*, as the pre-doctrine port sketch
had them, the ack vector would have been an environment observation and this
entry would have been paid in full. The doctrine that made the safety theorem
unconditional is the same one that made the refinement elementary.

Re-open if a future engine's commit point genuinely depends on an input the
design does not latch: the shape needed is still auxiliary/prophecy variables
with `invariant_pullback` ergonomics.

**D26 — spec-to-design synthesis with soundness.** The proof-derived bus
monitor (`monitor_sound : monitor flags trace ↔ ¬ trace ⊨ Φ`) is a new
capability class: compile a temporal spec into a Loom `Design` and prove the
compilation correct. Distinct from D22 (which checks a design against text);
this checks the *world* against a spec, in hardware.

**D27 — checking-interface abstractions.** Authenticated backing store
(MAC/Merkle, epoch-bound anti-replay) so DDR-resident engine state carries
zero-assumption safety. The cryptography need not live in Loom; the reusable
piece is the *shape*: a validated view over untrusted bulk, with one refinement
quarantining the hierarchy (EPOCH_SPEC.md theorem 3).

## How to use this file

A campaign closes an entry by shipping the capability AND the artifact that
needed it — never the capability alone. An entry that survives two campaigns
without being needed is deleted: Loom grows by demand, and unused generality is
a cost, not an asset.

## D28 — steps-to-cycles: a proved bound and a measured number must be one quantity

**CLOSED 2026-08-01** by `Machines/Epoch/Refines.lean` — see the end of this
entry for what was shipped. Discovered closing D23 (2026-08-01). Bounded response is stated in
*transition-system steps*; the goal's acceptance is in *fabric cycles*. Those
are only the same quantity once a refinement fixes the steps-per-cycle
correspondence — which is exactly what the Engine→Protocol refinement (Layer 3)
introduces, via the stutter budget `b` that `StutterSimulation.boundedResponse_pullback`
already takes. So the entry is small but load-bearing: state, in one place, that
the spec bound `K` transported through a design with budget `b` is the number of
CLOCK CYCLES a silicon measurement may be compared against, and make the epoch
demo cite that theorem when it prints its latency. Without it, "proved bound"
and "measured cycles" are two numbers that merely look alike — which is exactly
the sloppiness this project exists to refuse.

**Shipped.** `Refines.bump_returns_within_15_cycles` and
`Refines.bump_bounded_response` are the spec bound `K + 1 = 3` steps
(`Machines/Epoch/Bounded.lean`) transported through the engine refinement with
stutter budget `b = 3`, i.e. `3 * (3+1) + 3 = 15` **clock cycles** of the
emitted RTL, over all input traces, with no stall. Because the generic
pullback charges `b+1` cycles per protocol step, the transported number is a
sound over-approximation; the exact one is proved beside it by a direct
ranking on the same cycle-accurate system —
`Refines.bump_returns_within_4_cycles` (`K = 2` acks, the move to `B_RET`, the
return). Layer 2's measured `bump_cycles = 5` is a *different interval*
(request acceptance → return, less the counter's start offset) and
`EPOCH_SPEC.md` deviation F8 spells out exactly how the three numbers line up,
so that a proved bound and a measured number are never quietly conflated.

## Deliberately out of scope (do not propose these as gaps)

Recorded 2026-08-01 so the boundary is not re-litigated. Loom's semantics (D9)
is single-clock synchronous: one implicit clock, reads pre-cycle, writes commit
at cycle end. µVerilog then excludes latches, tri-states, combinational loops,
async set/reset, multiple drivers, and every inference-sensitive construct —
per the charter's rule that *where the standard leaves latitude, the subset
excludes the construct*. The value proposition is that all serious tools agree
on the emitted text; async and multi-clock are exactly where they stop agreeing.

* **Asynchronous / self-timed logic** (C-elements, bundled-data, handshake
  pipelines): NOT a future entry. Its correctness arguments are about
  delay-insensitivity, hazards and isochronic forks — a different formalism
  (STG/Petri-net class) and a different backend. A sibling tool if ever, never
  a subset extension.
* **Multiple clock domains inside one `Design`**: still excluded as a
  *semantics change* — making `Design` multi-domain turns the step function
  into an interleaving model and invalidates D9, the emission theorem,
  FastEval and eqcheck at once. But multi-domain SUPPORT is now planned as
  **D29 (below)**, by composition rather than by changing the core.
* **Hard blocks** (PLL/MMCM, SerDes, DDR PHY, XADC) and **bidirectional IO**:
  wrapper only, by the three-doors doctrine.
* **Timing constructs** (multicycle/false paths, clock gating as a construct):
  outside the semantics by design — timing closure is a per-target vendor-side
  activity and the theorems are stated conditional on a clock constraint.

**Where this project would actually hit the multi-clock wall**: bringing the
GEM MAC itself into Loom means owning the 125 MHz RGMII domain. Every crossing
so far (JTAG DRCK, PS FCLK, the 200 MHz board clock) has stayed in the wrapper
under D21, which is why the question has not yet been forced.

## D29 — multi-clock, by composition (PLANNED, 2026-08-01)

Decision: support multiple clock domains *without touching D9*. Single-clock
`Design`s stay the unit of semantics, compilation, emission and equivalence
checking; domains meet through proved components, not through a new step model.

Pieces:
1. **A domain-composition operator** pairing designs with a *declared* clock
   relationship (ratio or "unrelated"), emitting one module per domain plus a
   wrapper instantiation; eqcheck runs per domain, unchanged.
2. **A verified CDC component library**, generalizing D21's toggle synchronizer:
   pulse-sync, 2FF level-sync, four-phase handshake, and a gray-pointer async
   FIFO — each with an adversarial-resolution soundness theorem (the D21 shape:
   quantify over every way a metastable flop may resolve) and an explicit rely
   on the clock relationship.
3. **Trace-level relies (D24 shape)** so a slow-domain design's theorems compose
   with a fast-domain one's: what one domain guarantees is what the other may
   assume, with the CDC component's theorem as the bridge.
4. **Bounds across domains (D23/D28)**: a K-step bound in one domain becomes a
   cycle bound in the other only through the declared ratio — state it once,
   there, rather than per design.

Driving artifact (the rule: ship the capability WITH the artifact that needs
it): the **GEM MAC's 125 MHz RGMII domain** — bringing the MAC itself into Loom
is the first thing that genuinely cannot stay in the wrapper. It also unlocks
GALS-shaped machines at LNP64 scale, where §16.7 volumes with per-volume clocks
and a spanning-tree ack reduction are exactly a multi-domain composition.

Explicitly NOT part of D29: asynchronous logic. Its correctness rests on local
delay assumptions (isochronic forks, bounded delays) that are strictly harder to
discharge than the synchronous alternative, which collapses all timing
correctness into ONE checkable predicate (the clock constraint, verified by STA,
with theorems stated conditional on it). For a proof-carrying stack that is the
reason the chain closes. The real-world niches for true async — near-threshold
power, DPA-resistant dual-rail, ring-oscillator TRNGs — are not this project's,
and on FPGA fabric async is actively counterproductive (no delay control, no
C-element primitive, tools fight it). The genuinely useful part of "async" is
the GALS boundary, and D29 delivers exactly that.

## ASIC portability: what the FPGA gives for free (design rules, 2026-08-01)

The charter targets "any FPGA vendor and the ASIC flow" from one module. The
boundary does not move on an ASIC — the untrusted wrapper simply holds
different occupants (POR, reset synchronizer, PLL, ICG cells, pads, memory
macros instead of IBUFDS/BUFG/BSCANE2/PS7). What DOES change is that several
things the FPGA supplied invisibly become explicit. Design rules, to apply now:

1. **Never rely on memory initial contents.** SRAM has none; bitstream BRAM
   INIT is an FPGA affordance and may not even survive an open synthesis flow
   (suspected root cause of the epoch engine's first silicon `-BADREF`). A
   design whose reset state lives in `initial` contents is not portable. Put
   reset state in an explicit reset sequence (a sweep, like lnp64mini's
   zeroing engine) or a ROM, and keep the `Init` predicate the proofs use
   true by construction either way.
2. **Reset is a protocol, not a wire.** ASICs need async-assert /
   sync-deassert reset synchronizers (FPGA GSR hid this). That primitive is
   inherently async and is OURS — it gets the D21 treatment: a theorem that
   release is synchronous, proved over adversarial metastability resolution,
   in the shape of `toggleSync_sound`.
3. **MTBF becomes quantitative.** D21 states the single-flop resolution
   assumption qualitatively. On ASIC it acquires a number (library flop
   parameters × clock rates × transition rate), and CDC paths acquire
   `set_false_path`/`set_max_delay` constraints discharged by STA.
4. **Clock generation and gating are instantiated, not designed.** PLL/DLL are
   foundry IP; ICG cells contain a latch and are therefore outside µVerilog by
   construction — synthesis inserts them, LEC verifies them, they sit below the
   boundary. A declared clock RATIO from the PLL is a D29 rely.
5. **Async FIFOs arrive with GALS.** The moment D29 goes to silicon, gray-
   pointer async FIFOs join the verified CDC component library (rule 2's shape).

None of these needs asynchronous *logic* in the sense D29's note rejects: every
item is either foundry/library IP we instantiate, or a small standard structure
whose protocol we prove over adversarial resolution. The FPGA's hard blocks and
the ASIC's library cells occupy the same slot in the trust story.

## D30 — memory reset images must be verified into the netlist (CLOSED 2026-08-01)

Discovered by the epoch engine's first silicon run, and the sharpest
tool-boundary finding so far. Loom emits a `MemDecl`'s reset image as a Verilog
`initial` block. On the openXC7 path that image survives **only for banks yosys
maps to block RAM**: the three 512×32 epoch banks became `RAMB18E1` with
faithful `INIT_xx`, while the 512×3 `cell_flags` bank became distributed LUT
RAM (`RAM64M`), **whose mapping silently discards a non-zero init** — no
warning, at any stage. The design was correct, the proofs were correct, the
simulation was correct, and the fabric still disagreed.

Diagnosis by symptom is the part worth remembering: with flags zeroed the
occupancy bit was clear, so a check took §3's empty-slot clause; the *replica*
bank had initialized correctly, so the presented epoch matched, giving the
matching-epoch-empty case — `-BADREF`. The board answering `-BADREF` rather
than `-STALE` was itself the evidence that BRAM init survived and LUTRAM init
did not.

Closed by `scripts/check_mem_init.py`: re-derive every memory's reset image
from the emitted RTL and check it against the yosys netlist, per bank. It
reproduces the defect on the pre-fix netlist with no board and no simulation,
and it immediately found a second, latent instance (lnp64mini's `c0_tpc`/
`c1_tpc` trap-PC tables, reset `64'd4096`, losing their init the same way —
harmless only because the guest installs vectors before it traps). Acknowledged
losses are printed as `ACK` lines rather than suppressed.

Design consequence, now a standing rule (see also the ASIC section, rule 1):
**a design must not depend on a memory reset image the target flow cannot
deliver.** The epoch engine took occupancy out of memory entirely rather than
adding a reset sweep (which would have broken `abs(reset) = Protocol.Init` and
every theorem stated over `runOpen`-from-reset) — the fix that kept Layer 3 an
equality instead of a weakening.

## D33 — equivalence against the POST-PLACE-AND-ROUTE netlist (planned)

`eqcheck` covers `emitted module ≡ post-synthesis netlist`. The span
`synthesis → placement/routing → FASM → frames → bitstream` is unchecked, and
D30 is the standing proof that "the tool surely preserved it" is not a safe
assumption anywhere in that span.

**Feasibility is better than it looks: the artifact already exists.**
`build_oxc7.sh` runs nextpnr-xilinx with `--write $O.routed.json`, so every
bitstream we have ever built already has its post-P&R netlist saved, in the
same JSON family `Loom/Netlist/Json.lean` parses.

**Decomposition (do it this way, not as one miter):**

    module ≡ synth-netlist          -- eqcheck today (D22, hardened by D31/D32)
    synth-netlist ≡ routed-netlist  -- D33: netlist-to-netlist
    ⟹ module ≡ routed-netlist       -- by transitivity

Netlist-to-netlist is the easier half: both sides are the same kind of object,
so cone construction is shared and only *matching* differs. A single
module-vs-routed miter would force the naming problem and the semantic gap to
be solved at once.

**What it catches**: packing (LUT/FF merging into SLICEs, carry chains),
constant propagation during packing, routing that connects the wrong things.

**The two risks, to be de-risked on a small design first:**
1. *Cell coverage after packing* — nextpnr emits BEL-level primitives
   (packed SLICE contents, `LUT6_2`, site pins) that `Cells.lean` does not
   model. Work, not doubt.
2. *Name matching* — synthesis already reorders and renames bits (`wreduce`,
   Deviation 1); P&R is worse. May require structural/functional
   correspondence instead of a netname bijection. Settle this on `s0blinky`
   before committing to the SoC.

**Below the routed netlist: corroborate, do not prove (decided 2026-08-01).**
`routed → FASM → frames → .bit` is deliberately NOT a verification target.
The reason is epistemic, not effort: the prjxray database is a reverse
-engineering of undocumented configuration bits, not a specification, so
checking `fasm2frames` against it would prove *consistency with an inference*
— the only link in the chain whose ceiling is not a proof or a checked
certificate, sitting exactly where over-claiming is easiest. It also does not
transfer: the ASIC path's analogue of D33 is LEC against the post-layout
netlist (same shape, same machinery), and there is no bitstream in it at all.
And it is the wrong end of the risk curve — synthesis is where *meaning*
changes (D30 lived there), P&R still has semantic content (packing), while
FASM/bitgen is mechanical transcription whose failures are usually
catastrophic rather than silent.

The right instrument for this layer is the one that already found D30:
**run the real bitstream on the real part and compare against the model.**
So the effort that might have gone to a bitstream checker belongs in the
generated conformance suite + hardware-in-the-loop CI (per-opcode, emulator ≡
ISS ≡ iverilog ≡ silicon, on every change), which corroborates bitgen,
placement AND timing marginality on the actual artifact without pretending
any of it is proved. The charter's optional "verified down-to-the-bitstream
module" stays optional; if it is ever built it is a flagship-target
curiosity, not a link this stack's claims rest on.

Equivalence is never timing, at any level: the clock constraint stays
discharged by STA, by design.

## D31 — memories inside the equivalence checker (CLOSED 2026-08-01)

**Discovered by D30**, which is to say by the epoch engine's first silicon
run. D22's checker had a hole exactly where the tool lied: array storage,
port wiring and configuration images were "carried by cell identity", i.e.
trusted, and the one class of defect that had actually reached silicon lived
inside it. The stop-gap was `scripts/check_mem_init.py`, a guard *outside*
the certified path — a certificate plus untrusted glue.

Closed by `Loom/Netlist/Mem.lean` and the memory legs of `Tools/EqCheck.lean`.
Per bank, now checked and LRAT-certified where a solver is involved:

* **reset images** — the primitives' `INIT*` parameters decoded per address
  and per bit and compared against `MemDef.init`, *plus* the separate
  deliverability rule that a non-zero image on distributed LUT RAM is a
  failure even when the netlist's `INIT` is faithful, because the
  configuration path does not carry it. That second rule is D30;
* **storage and write ports** — write clock, enable (against
  `en ∧ ¬rst ∧ bank-select`, with the depth-group index *proved* rather than
  assumed), address and per-lane data, all against the primitives' own pins,
  through a model of how `memory_libmap` splits an array by width and depth;
* **read paths** — each netlist read port matched to a printed read site by
  proving the address cones equal, then the async (LUT RAM) versus D19
  synchronous (block RAM, one cycle, `DOx_REG` clear, `READ_FIRST`) shape
  checked against what the design declares, including that the primitive's
  data pins *are* the module's read value — which is what ties the read ports
  to the cells the write ports write.

**Evidence it bites.** `Tests/fixtures/eqcheck/epochengine_prefix.{v,json.gz}`
is the pre-`b510caf` engine plus its netlist; `scripts/eqcheck_memfixture.sh`
requires eqcheck to reject it, naming `cell_flags`, with exactly one signal
differing — D30 reproduced from the netlist alone, no board and no
simulation. The post-fix engine passes the same 124 signals.

**Two findings it made on the way.** (1) `lnp64mini_soc`'s `tpc` loses its
`64'd4096` image the same way — already recorded in `EPOCH_SPEC.md` E13, and
now found independently from the certified path. (2) yosys 0.33 wires
`RAMB36E1` `SDP`-72 `DIPBDIP` to `DIPADIP`'s nets, so `dmem` bits 44/53/62
are never written while `DOPBDOP` reads them: a self-inconsistent netlist,
and a synthesizer defect rather than an emission one (the board's bitstream
is built with 0.38, which does not have it). Both are carried as `--ack`
lines, printed in full on every run.

`check_mem_init.py` is now redundant and is deliberately **kept** as an
independent second implementation — two readers of the same netlist
disagreeing is itself a signal. See `Loom/Netlist/EQCHECK_SPEC.md` §Memories.

## D32 — the equivalence checker's encoder, proved (CLOSED 2026-08-01, in part)

**Discovered by D22 itself.** Every other link in the emission chain is a
theorem; the strongest link — the per-build netlist check — ended in a
conditional the tool printed on every run: "*if* the encoding is faithful,
netlist ≡ module". The encoder is a small pure function, so the conditional
was a gap of effort, not of principle.

Closed for the µVerilog side of the miter by `Loom/Netlist/Encode.lean` (the
gate layer) and `Loom/Netlist/MiterProof.lean` (the blaster, the DIMACS
normalization, and the miter):

    encode_sound : CNF.Unsat (toDimacs s.clauses).cnf ↔
                     ∀ f, (assumptions hold at f) → e.eval (stOf f) = valB f

`sigMiter` is the shape every miter has, and both `coneMiter` and `regMiter`
are instances of it (the register miter's `rst ? init : next` is now written
as a µVerilog `mux` and blasted by the one blaster, emitting the same
clauses). Both directions — the forward one is what makes an UNSAT verdict mean
something, the backward one is what makes the countermodel the tool prints a
real disagreement. `toDimacs`' clause normalization (repeated literals and
tautologies dropped, forced on us by cadical's parser) is *inside* that
statement: `toDimacs_unsat_iff`.

**What is NOT proved, stated by the tool on every run.**

* Side A operators `shl`, `shr`, `slt` — the barrel shifter and the signed
  comparator. Left on the unverified path rather than weakening the theorem;
  `encVerified` selects the proved fragment and `eqcheck` prints which
  operators each design actually uses (`s13soak`: `shl`; `lnp64mini_soc`:
  `shl slt shr`; the other four designs: none).
* Side B — the netlist cone walk `Netlist.evalSig`/`evalBits` and the cell
  library under it. It enters `encode_sound` as the hypothesis
  `EncA 0 w actB valB`, so the remaining gap is one named obligation rather
  than an unstated assumption.

Reopen (or rather, continue) on: (a) `shl`/`shr`/`slt`; (b) side B, which
needs a reference semantics for the netlist and a memo-table invariant for
the traversal.

## Predicted, from building the engine roster (recorded 2026-08-01)

Two engines (Epoch §3, CapWalk §2.2) are enough to see the duplication; six
more are planned, so these are due now rather than later.

**D34 — a protocol-machine library.** Both engines hand-rolled the same
skeleton: state structure, `Ev` inductive, `stepEv : St → Ev → Option St`,
`Step := ∃ e, stepEv s e = some s'`, the `TSys` instance, a multi-field `Inv`
structure with its `inv_inductive`/`inv_invariant` pair, and
`Run := Relation.ReflTransGen Step`. None of that is engine-specific. A
`ProtocolSpec` abstraction (state, event alphabet, partial step, invariant
bundle) with generic derivations — `toTSys`, reachability, `Run`, the
inductive-invariant lemma, and the "disabled events stutter" glue — would make
the next engine start at its actual content. Validate it by *expressing* both
existing engines through it without editing the frozen files.

**D35 — refinement by cases.** `Machines/Epoch/Refines.lean` is ~1450 lines for
one engine, and its spine is generic: an abstraction function, then a commuting
square discharged by exhaustive case analysis over the design's FSM state ×
control flags, with a design invariant carrying the sequencer's staging. That
wants a combinator (or tactic) parameterised by the state encoding, so each
engine writes its abstraction and its cases and nothing else.

**D36 — the outcome/priority pattern.** T-E4 (2^10 views) and T-C2 (2048 views)
both prove "this total outcome function is exactly this priority order" against
an independently-written spec function, by kernel `decide` at a small width,
plus per-clause lemmas at arbitrary width. Same proof, twice, by hand. Make it
one combinator: given a priority list of (guard, outcome), derive both the
exhaustive check and the per-clause ordering lemmas.

**D37 — prevention, not just detection, for non-deliverable reset images.**
D30 is now caught by eqcheck (and by `check_mem_init.py`), but Loom still
permits a design whose correctness depends on a memory reset image the target
flow cannot deliver. The EDSL knows the memory's shape and the intended
mapping; well-formedness could refuse a non-zero image on a bank that will map
to distributed RAM, turning a downstream catch into a compile-time error.
Detection is a guard; prevention is a property.
