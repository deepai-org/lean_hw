# PLATONIC — making Loom the ideal version of itself

Companion to [CHARTER.md](CHARTER.md) (what and why) and [PLAN.md](PLAN.md)
(the implementation ledger). This document is the *capability roadmap*: the
gap between Loom as built and Loom as it should be, decided 2026-08-03.

**The organizing sentence.** The design, its spec, its proofs, its
simulator, its tests, and its silicon evidence are **one Lean value viewed
six ways**. Everything Loom does well is an instance of that sentence;
every wart is a place where two of the views are maintained by hand and
corroborated instead of derived and proved. Each workstream below removes
one hand-maintained view or deepens a capability no other tool
(Chisel, Clash, Bluespec, Kôika) can offer at all.

**Standing constraints, inherited from the charter:**

- The TCB does not grow for convenience. Metaprogram output is ordinary
  `Design` data; notation elaborates to existing constructors; nothing
  below adds an axiom or an `implemented_by` twin without a TRUST.md entry.
- The three-axiom closure (`propext`, `Classical.choice`, `Quot.sound`)
  remains the release bar.
- Claims land as theorems or as explicitly-named assumptions — never as
  prose implying a theorem (the D9-vs-ORAAT drift in `Loom/Hw/DESIGN.md`
  is the cautionary example; fixing it is W0 below).
- Every "easy" claim gets a falsification protocol
  (`Machines/Tutorial/DEFECTS.md` pattern): acceptance criteria below are
  executable or checkable, not vibes.
- **Loom is toolchain- and hardware-agnostic.** openXC7/ZC702 appears in
  acceptance criteria below only because it is the test substrate
  currently on the bench — it is *available equipment, not a dependency*.
  Anything target-specific (memory-cell models, timing weights, flow
  scripts) lives behind an explicit target interface, following the
  `Loom/Hw/MemTarget.lean` precedent, with the concrete target as one
  instance. Swapping the board or the synthesis flow must never touch
  `Loom/` — only the target instance and `fpga/`.

---

## W0 — Honesty pass (small, do first)

The external review (2026-08-03) found `Loom/Hw/DESIGN.md`'s header still
describing the original Kôika aspiration — ORAAT semantics, rule aborts, a
scheduling-correctness theorem — none of which D9's implemented semantics
has. Anyone reading the header and then `Act.run` concludes the project
claims something it doesn't.

**Deliverables.**
1. Rewrite the DESIGN.md preamble to match D9 as built: rules are an
   ordered list; all reads pre-cycle; last-write-wins; no aborts, no
   scheduler. ORAAT moves to an explicit "not implemented; see W2" note.
2. Sweep other docs for the same drift (`grep -i oraat\|abort\|schedul`).

**Acceptance.** A cold reader of DESIGN.md §Semantics and `Act.run` finds
no daylight. **Size:** hours.

---## W1 — A design language worthy of the prover

*Kills the stringly-typed layer and the mirror boilerplate — the two
findings every reviewer (internal and external) converges on.*

Today a register exists in up to five places (RegDecl, `Expr` shorthand,
ISS struct field, `issRegs` comparator, `toEnv`), bound by string name and
restated width. Write typos are caught only on the proof path
(`designWFCheck`); read typos and wrong-width reads are **silent** —
a fresh coordinate reading `0#w` forever. `DesignWF` constrains writes
only; the repo already discovered the read-side hole from the other
direction (`designReadsValidB`, NEXTSTEPS task #9 finding 2).

**The comparator is the undercounted view, and it's the one that bites.**
The lockstep comparator (`cmpStates`/`issRegs`) is a hand-maintained list
of what "EDSL ≡ ISS" *means*, and state absent from it is not compared at
all. This hit twice in one campaign: EXT-2's `tdom` and EXT-7's five TLB
memories were both missing from `cmpStates`, so the lockstep line was
green for free — "the legs agree" actually meant "the legs agree on the
subset someone remembered to list." That is strictly worse than a typo'd
read, which at least reads zero; an incomplete comparator **actively
certifies nothing while looking like evidence**. Consequence for this
workstream and W5: comparator membership for every declared register and
memory is a *generated obligation* — new state is compared by
construction, and any exclusion must be explicit, named, and justified in
the generated artifact. "Green lockstep" must be impossible to obtain by
omission.

**Deliverables.**
1. **Emit-time gates** (immediate, independent of the rest):
   `Design.emit` additionally runs `designWFCheck` and a read-validity
   check (reuse the `designReadsValidB` machinery). Both silent failure
   modes become emit-time errors on the corroborate-only path, zero proof
   cost. (Same class as the D16/D19/D39 gates already in `EmitIO.lean` —
   "an obligation a caller can skip is not an obligation".)
2. **Typed handles**: `structure Reg (w : Nat)` carrying the name, with
   `.rd : Expr w`, `.set : Expr w → Act`; `Mem aw dw` likewise. Width
   stated once, at declaration.
3. **Single-declaration registers** via metaprogram: one
   `loom_register pc : 64 := TEXT_BASE` (syntax TBD) generates the
   `RegDecl`, the handle, and registers the name for W5's derived views.
   `Fin`-indexed arrays declared once (`loom_register_array tpc : 32 × 64`),
   generating the builders that today are copy-pasted six times
   (`tpcDynWrite` et al. become one generic `dynWrite`).
4. **Notation layer** (`act!` or equivalent): `:=`-assignment,
   `if/then/else`, `;` sequencing; infix `+`, `===`, `&&&`, `!` on `Expr`.
   Elaborates to existing constructors — the pretty form and the
   constructor form are the same term, so nothing downstream changes.
5. **Op mnemonics** for Lnp64mini (`OP_CLONE := 0x59` …) — FSM states got
   names; opcodes deserve the same.

**Acceptance.**
- A deliberately typo'd read and a typo'd write in a scratch design both
  fail at `Design.emit` with the name in the error.
- `Machines/Lnp64mini/Core.lean` ported to the new layer with the emitted
  `rtl/lnp64mini.v` **byte-identical** before/after (the refactor gate) —
  or, where a deliberate semantic gate intervenes, an **expected diff,
  enumerated and justified** line by line. Precedent: D39a (mandatory
  outputs) deliberately breaks byte-identity for any design that narrows
  its exports, so byte-identity alone can no longer be the universal
  gate; the enumerated-diff form is the fallback, never a blanket waiver.
- ISS lockstep green with the comparator-completeness obligation
  discharged (no state absent-by-omission), and the file measurably
  smaller (~⅓ target).
- Tutorial updated; a `DEFECTS.md`-protocol run of the new syntax.

**Dependencies:** none. **Size:** the biggest ergonomic win per week of
anything on this list; gate (1) is a day, the rest ~2–3 weeks.

**Precedent confirming the W1.1 bet (2026-08-03):** moving D19 and
instance-name disjointness into `Design.emit` and making outputs
mandatory (D39a) immediately surfaced two real defects — `tlb_vld`
passing a loop index as a `memWrite` port number, and the TLB memories
absent from the comparator. "An obligation a caller can skip is not an
obligation" keeps paying on contact.

---

## W2 — Proof effort sub-linear in design size

*The real differentiator. Today an invariant proof `simp`s the whole
cycle, so proof cost grows with the design — the R-MC campaign's
100–400 s/site pathologies are the symptom, and nobody will prove
theorems about an 825-register core by whole-cycle simp twice.*

**Deliverables.**
1. **Frame lemmas from footprints.** `Loom/Hw/Footprint.lean` already
   computes write sets. Prove, once and generically:
   a rule whose write footprint is disjoint from an invariant's support
   preserves it (`frame_rule`); a cycle preserves an invariant if every
   rule does under the accumulated-write discipline (`invariant_by_rules`).
   An invariant over k registers then needs real proof text only for the
   rules that touch those k names — for `OneHot` on Lnp64mini that is
   ~3 rules out of 28.
2. **Support inference**: a decidable support-extractor for the common
   invariant shapes (predicates over named reg reads), so the frame side
   conditions discharge by `decide`, not by hand.
3. **`cycle_simp`** (tutorial defect #3, still open in the library): the
   shipped simp set / tactic that unfolds `Design.cycle` over a literal
   rule list, so the tutorial's "put your own definitions in the simp
   set" recipe becomes optional rather than load-bearing.
4. **Stretch — ORAAT as a reasoning layer** (this is where W0's honest
   "not implemented" note gets discharged for real): a schedule type with
   one-rule-at-a-time semantics and a **verified flattening** to the D9
   rule list. Rule atomicity as a proof device, compiled away — what
   Bluespec promises and never proves. Research-grade; do not block
   1–3 on it.

**Acceptance.**
- An invariant on Lnp64mini (e.g. `err`-style accounting or a scheduler
  one-hot) proved via `invariant_by_rules` + frames in minutes of
  wall-clock and a page of text — *on the real 28-rule core*, not a toy.
- Re-prove `SatCounter`/`PingPong` invariants with the new route; tutorial
  gains a "scaling up" section.
- Measured before/after proof-time numbers recorded (RELEASE_COST.md
  discipline).

**Dependencies:** none hard; W1's handles make supports nicer to state.
**Size:** items 1–3 a focused 2–4 week campaign; item 4 open-ended.

---

## W3 — The verified-transformation library

*Write the design clearly, optimize it provably. `retimeReg` (D17) is the
seed; the endgame is that the shipped netlist differs from the legible
design only by a chain of once-proved transforms.*

**Deliverables, in value order.**
1. **Promote and prove the balanced-tree builders.** `priTree`,
   `actPriTree`, `orTree`, `reduceTree` move from `Machines/Lnp64mini/`
   into `Loom/Hw/`, each with its eval-equality lemma
   (`priTree_eval : (priTree xs d).eval σ = (xs.foldr mux-chain d).eval σ`,
   etc.). Their correctness claims are currently comments — in this
   repo's own currency, the one place semantics is hand-reassociated for
   timing is exactly the place that deserves a theorem. Lnp64mini then
   imports them; behavior is unchanged by construction.
2. **`retimeReg` generalizations**: retime a feedforward path (cut a
   combinational cone at a named boundary, insert a stage, lagged
   `StutterSimulation`); `retimeᵏ` with the lemma parametric in k — pick
   pipeline depth, theorems survive with zero new proof text.
3. **Fan-out/duplication transform** (duplicate a hot register with a
   proved coherence invariant) — the next timing lever the 13.4 MHz
   ceiling will ask for.
4. **Transform-chain composition**: `Simulation`/`StutterSimulation`
   composition lemmas so a chain of transforms yields one end-to-end
   refinement, and `invariant_pullback` transports the ledger across the
   whole chain in one application.

**Acceptance.**
- Zero semantic claims about builders living in comments (grep gate).
- A demo: a deliberately deep Lnp64mini cone retimed by transform, ledger
  property transported, emitted, and the fmax delta measured on whatever
  flow/board is on the bench (currently openXC7/ZC702) — the
  "provably-safe optimization" story end to end, recorded like the
  silicon evidence README. The transform and its theorem are
  target-independent; only the measurement is not.

**Dependencies:** W2.4 not required; uses existing TSys machinery + D17.
**Size:** item 1 ~a week; 2–4 incremental, each lands standalone.

---

## W4 — Translation validation of synthesis — ✅ DONE (residuals only)

D22 (`scripts/eqcheck.sh`, `Loom/Netlist/`) checks the yosys-mapped
netlist against the µVerilog module signal-by-signal, every UNSAT
LRAT-certified and re-checked by the verified `Loom.Dp.Cert.checkLrat`;
D31 brought memories inside the miter (reset images, write ports, both
read shapes — the D30 LUTRAM-init lie is caught from the certified path);
D32 proved the encoder (`encode_sound`), removing the checker's last "if".
`TRUST.md` records exactly what this does and does not make true.

**Residuals (keep on the books, none blocking):**
1. Shrink and individually justify any remaining per-design exclusion
   lists (D31 acceptance clause — verify it's fully discharged for the
   SoC and dual-SoC netlists, not just the singles).
2. Fold eqcheck into the standing release/nightly gates for every shipped
   `.v`, so a new design cannot ship un-validated by omission.
3. Keep `check_mem_init.py` as the stated independent cross-check.
4. The netlist cell models are per-target by nature (unknown cell = hard
   error, as today); when a second synthesis flow arrives, its cell
   library becomes a second instance behind the same interface — the
   miter/encoder/LRAT core is flow-independent already.

**Acceptance for closure:** eqcheck green in the nightly gate over the
complete shipped-RTL list, exclusions enumerated with reasons, zero.

---

## W5 — Generate the ISS from the Design (decided: generate, not prove-apart)

*Removes the last big hand-maintained view: the ~600-line cycle-accurate
mirror whose agreement with the Design is only as strong as lockstep
coverage. Decision 2026-08-03: derive it from the `Design` value rather
than keep a hand mirror with an equality proof.*

**Approach.** A metaprogram consumes the `Design` (post-W1, the single
declarations) and emits a specialized `step : St' → In' → St'` over a
generated struct-of-BitVecs — i.e. it partially evaluates `Act.run` on
the concrete rule list at elaboration time. Correctness is by
construction: the generated `step` is *defeq* (or provably equal by
`rfl`/generated `simp` proof) to `Design.cycleOpen`, and that equality is
stated as a generated theorem — so the fast path is covered by a theorem
the way `implemented_by` twins are audited today, but per-design and
kernel-checked, not whitelisted.

Speed is the design driver, and the bar is known: interpreter-mode
lockstep costs ~25 min and blows the stack on big designs
(`Machines/Lnp64mini/Emit.lean` header); the compiled hand-ISS runs the
MMU selftest in 45 s. The generated stepper must be within ~2× of the
hand ISS compiled, or it hasn't earned deletion of the mirror.

**Deliverables.**
1. `loom_derive_iss design` elaborator: struct, `step`, `toEnv`/input
   adapter, and the lockstep comparator (subsumes `issRegs`). The
   comparator is **complete by construction**: it covers every declared
   register and memory of the `Design`, and any exclusion is an explicit
   argument that shows up in the generated code with its justification
   (the EXT-2/EXT-7 `cmpStates` omissions are the motivating defects —
   see W1's motivation).
2. The generated `step ≡ cycleOpen` theorem, per design, in the audit.
3. Migrate Lnp64mini: hand ISS retired to a cross-check or deleted;
   Harness/selftests target the generated stepper.
4. Benchmark note in RELEASE_COST.md style.

**Acceptance.**
- `lake exe minitest selftest` (and the preempt/dom/mmu family) green on
  the generated stepper, ≤2× hand-ISS wall time, zero hand-written mirror
  lines left for Lnp64mini.
- `#print axioms` on the generated equality theorem: the three axioms.

**Dependencies:** W1 (single declarations are the input). **Size:** the
hardest metaprogramming on this list; ~3–5 weeks; prototype on
`S13Soak`/`PingPong` first.

---

## W6 — A semantics for timing and area

*"Routes at 13.4 MHz max" and the 25 MHz divided clock were empirical
surprises. Make "will it fit and make timing" a `#eval`, then a theorem.
No verified-HDL project has this.*

**Scope honesty, learned from the EXT campaign:** the campaign's actual
losses were **not depth**. EXT-4's first version cost 8,073 LUTs and
wouldn't route; narrowing the comparator 4× recovered 6,800 LUTs and
0.22 MHz — the failure class was *duplication and congestion*, not path
length. A depth-only model would pass its retrodiction test while
missing the class of failure that actually stopped work. So W6 has two
axes from the start: a **depth model** (path length) and an **area
model** (node count / duplication), with congestion-driven Fmax loss
explicitly stated as *predicted only via the area proxy* — that residual
scope limit is written where the model is defined, not discovered later.

**Deliverables.**
1. **Static depth model**: `Expr.depth : Expr w → Nat` (unit-delay or
   per-op weights), `Design.criticalPath` reporting the deepest
   register-to-register cone with its path — a `#eval`/CLI report
   (`lake exe minitest timing`-style) usable during design.
2. **Static area model**: per-op node/LUT-weight estimate over the
   compiled DAG (post-CSE, so sharing is counted once) plus a
   *duplication report* — the top-N subterms instantiated more than once
   and their multiplicity. This is the model that would have flagged
   EXT-4's 8,073-LUT comparator before the router did.
3. **Proved bounds for the library**: `priTree_depth ≤ …·log₂ n + …`,
   `reduceTree_depth`, retime's depth-split lemma — and area counterparts
   (`priTree_size`) — so the W3 transforms get *quantified* payoffs, not
   just semantic safety.
4. **Calibration, honestly labeled and target-parametric**: per-op
   depth and area weights are a `TimingTarget` value (the `MemTarget`
   pattern), fitted against whatever flow's reports are available —
   currently openXC7 on the ZC702 — with fit quality recorded in the
   evidence README style. **Calibrate against post-routing numbers
   only**: the campaign measured post-placement Fmax ~5 MHz pessimistic
   against post-routing (28.25→33.96, 27.27→31.74 MHz), so a model
   fitted to placement reports would be systematically wrong. The models
   and their lemmas (items 1–3) are target-independent; only the weight
   instance is fitted. Both models are *predictors with stated error
   bars*, not claims about physics — say so where they're defined (the
   CONCRETE_SSA_BOUNDARY.md discipline, applied to timing and area).
   This is also the workstream most tempted to leak board-specific
   assumptions into `Loom/` — hold the target-interface line hardest
   here.

**Acceptance (both retrodictions required — one per failure class).**
- *Depth:* the target-independent depth report, run on pre-fix Lnp64mini,
  ranks first the exact cone the current bench measured at 13.4 MHz
  (the number is the bench's, the cone is the model's).
- *Area:* the duplication report, run on EXT-4's first version, ranks
  first the comparator whose 4× narrowing recovered 6,800 LUTs.
- W3's retime demo shows predicted vs measured fmax delta on the
  available flow.

**Dependencies:** none for 1–3; W3 makes 3 worth having. **Size:** 1–2
are days each; 3 ~a week; 4 ongoing calibration.

---

## Sequencing

```
now:        W0 ─ W1.1 (emit gates) ─ W3.1 (builders proved)   [days each]
next:       W1.2–5 (language layer)         [unlocks W5; improves W2]
campaign 1: W2.1–3 (frames + cycle_simp)    [the scaling story]
campaign 2: W5 (derived ISS)                [after W1; baseline in hand]
opportunistic: W3.2–4, W6                   [as designs demand]
research:   W2.4 (verified ORAAT layer)     [paper-grade; never blocks]
closure:    W4 residuals into nightly gates
```

Rationale: W0/W1.1 are honesty and safety, done first on principle —
and the bet is already confirmed (see W1's precedent note). **W3.1 sits
beside them, not in "parallel/opportunistic"**: the tree builders are
load-bearing in every structure the EXT campaign built (the tdom funnel,
the ready bitmap, the wake bank, the regfile funnel), which makes them
simultaneously the largest semantics-in-a-comment surface and the
hottest path in the shipped design — the worst place in the repo for an
unproved claim to live. W1 compounds into everything (every future port,
W5's input, W2's statements). W2 is the thesis — "proof effort
sub-linear in design size" is the sentence that makes Loom a category
rather than a better Chisel. W5 deletes the largest remaining
hand-mirror (its ≤2× bar has its baseline as of 2026-08-03: the compiled
runner landed, 45 s compiled vs ~25 min interpreted are current
numbers). W6 is the hardware community's credibility multiplier. W2.4 is
the only research-risk item and nothing depends on it.

**The claim, when this document is done:** a legible single-source design;
theorems whose cost scales with the property, not the core; provably-safe
optimization; a kernel-checked chain from the design value through
compile, print, and synthesis to the netlist; a derived-and-proved fast
simulator; and a timing model with stated error bars — one Lean value,
six views, none maintained by hand.
