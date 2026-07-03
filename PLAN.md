# Loom + LNP64-µ Implementation Plan

Companion to [readme.md](readme.md) (the program charter). The charter says *what* and *why*; this
document says *where the code goes, in what order, and how we know where we are*. It is the living
progress ledger: the checklists in §8 are updated as work lands, and the theorem table in §7 is
kept in sync with `lake exe audit` (the tool that makes the table honest).

**What is being built (scope, restated).** The deliverable is **Loom**: a machine-generic Lean 4
toolchain for modeling, verifying, and fabricating processors — spec DSL and projections, proof
infrastructure, decision procedures, hardware EDSL and verified compiler, verified Verilog
emission, documentation engine, independent checker. Loom is generic over the machine being
modeled: it must serve a 64-bit design, an 8-bit 6502, or an exotic architecture as readily as its
first use case. **LNP64-µ is that first use case** — a small capability machine whose theorems
(T1–T9) we actually care about proving, and whose obligations drive every Loom feature (Rule 2).
A second, deliberately tiny machine, **Acc8**, exists to keep the toolchain/machine separation
structural: every generic Loom layer is exercised by two machines, and Acc8 — being small — reaches
each layer first, as the pathfinder.

**How to use this document.** To find where to work next: read §8 top-to-bottom and take the first
unchecked box in the current phase whose dependencies (listed with each task) are checked. To check
overall health: run `lake exe audit` and compare against §7.

---

## 1. Foundation principles (decisions that shape everything below)

**P0 — Toolchain and machine are separate artifacts.** `Loom/` never imports `Machines/`
(enforced by the import linter). A Loom construct is *generic*: parameterized over machine
signatures, never mentioning domains, capabilities, or any LNP64-µ noun. Machine-specific
theory, state, and theorems live under `Machines/<name>/`. The Acc8 machine is the standing
proof of genericity: any Loom feature only one machine can use is machine code in disguise and
gets moved.

**P1 — Structure first, syntax second.** The spec "DSL" is a plain Lean structure,
`Loom.Isa.InstrDecl`, holding encoding, semantics payload, cost label, and prose as ordinary
fields. Instructions are first written as plain terms of this structure; the macro front-end
comes later as *sugar that produces the same terms*. Every projection — decoder, assembler, ISS
glue, conformance suite, book — consumes `Array InstrDecl`, never syntax trees. Genericity note:
`InstrDecl` is parameterized by an encoding signature (instruction width, opcode field) and by
*opaque* semantics/cost payload types supplied per machine — Loom handles syntax, encoding,
prose, and projections; operational semantics stays machine-side. Variable-length encodings
(6502-style) are a planned framework extension that lands only with a consuming machine (Rule 2
applied to the toolchain).

**P2 — One transition-system spine.** A single `TSys` abstraction (`Loom/Core/Ts.lean`, below
every layer) is the type through which any spec machine, the L3 hardware semantics, the µVerilog
semantics, and every L2 engine speak to each other. Refinement (`Simulation`,
`StutterSimulation`), invariance, BMC, k-induction, PDR, and the emission theorem are all stated
against `TSys`.

**P3 — Two levels of state, one map between them.** Theorems want `Prop`-level states; engines
want bit-level states (`BitSys`: `BitVec` state, decidable init/step). Each machine provides both
plus a proved correspondence (`Machines/<m>/BitLevel.lean`); engine results transport across it.

**P4 — Theorem statements are a separate, stable artifact.** `Machines/Lnp64u/Theorems/`
contains exactly the T1–T9 statements (plus refinement and emission instances), one file each,
importing definitions but containing no infrastructure. Statements land early with `sorry`;
proofs replace sorries without the statements moving.

**P5 — The audit tool is part of the foundation.** `lake exe audit` walks every declaration in
the theorem ledgers and reports per theorem: *stated / proved / clean* (clean = `#print axioms`
shows nothing beyond `Classical.choice`, `propext`, `Quot.sound`, and — only where declared — the
µVerilog-semantics axiom). It also enforces Rule 1 (`native_decide` ban on the trusted path),
the sorry policy, and the import DAG of §6. CI fails if the ledger in §7 disagrees with reality.

**P6 — The L5 checker is a separate package.** `checker/` is its own Lake package with zero
imports from Loom or Machines, consuming only Lean kernel export files.

**P7 — Deterministic, cycle-accurate spec (LNP64-µ).** The frozen machine admits a fully
deterministic step function given the reset manifest; one spec step is one cycle; an instruction
occupies the core for its WCET-class cost and retires atomically (the snapshot rule — retirement
is the linearization point, mapping onto L3's atomic rules). ISS = spec by evaluation.

**P8 — Dependency policy.** Mathlib is an accepted dependency (pinned to the toolchain tag).
Rationale: it is generic mathematics, and its proofs are checked by the same kernel as ours, so
it adds nothing to the TCB and nothing to the axiom whitelist. The charter's Rule 4 boundary is
unchanged: *domain* code (provers-for-hardware, spec languages, HDL frameworks, doc systems) is
never imported; generic *algorithmic* libraries (SAT solvers etc.) run untrusted behind
kernel-checked certificates.

---

## 2. Codebase conventions

- **Namespaces:** toolchain under `Loom`; machines under `Machines.<Name>` (e.g.
  `Machines.Lnp64u`, `Machines.Acc8`). Module path = namespace path.
- **File size:** target ≤ 400 lines; split along concept boundaries.
- **One concept per file**, named after the concept.
- **`sorry` policy:** allowed only under `Machines/*/Theorems/` and `Wip/` subdirectories; audit
  inventories them; a `sorry` anywhere else fails CI.
- **No `axiom` anywhere** except the single µVerilog-semantics axiom in
  `Loom/Emit/MicroVerilog/Axiom.lean`. Audit enforces.
- **Docstrings are the book's raw material** — publishable text from day one.
- **Theorem names follow the ladder** — `Machines.Lnp64u.Theorems.T3.no_access_after_revoke`.
- **Design docs:** each Loom layer and each machine has a `DESIGN.md` recording Rule-5's "named
  win" and key decisions. Machine-level design decisions (e.g. LNP64-µ's lineage-cell placement,
  generation saturation) are recorded in the module docstrings where they bind.

---

## 3. Repository layout

```
lean_hw/
├── readme.md                  # program charter
├── PLAN.md                    # this file: architecture + progress ledger
├── lean-toolchain             # pinned: leanprover/lean4:v4.28.0
├── lakefile.lean              # libs: Loom, Machines, Tools; exes; require mathlib @ v4.28.0
├── Loom.lean / Machines.lean  # root import files
│
├── Loom/                      # ═══ THE TOOLCHAIN — machine-generic, never imports Machines ═══
│   ├── Core/
│   │   ├── Word.lean          #   word abbrevs, BitVec field extract/insert kit
│   │   ├── Fun.lean           #   pointwise function update (table states)
│   │   ├── Ts.lean            #   TSys, BitSys, Simulation, StutterSimulation (P2 spine)
│   │   └── Trace.lean         #   lockstep trace event format (shared ISS/RTL/HW)
│   ├── Isa/                   # L0 framework — generic instruction-declaration machinery
│   │   ├── Sig.lean           #   encoding signature: instr width, opcode field, operand fields
│   │   ├── Instr.lean         #   InstrDecl (P1): encoding + opaque sem/cost payloads + prose
│   │   ├── Decode.lean        #   generic decode/encode projections + totality/round-trip kit
│   │   ├── Conformance.lean   #   generic vector generation
│   │   └── Dsl/               #   macro front-end elaborating to InstrDecl (late, P1)
│   ├── Dp/                    # L2 — decision procedures (generic over TSys/BitSys)
│   │   ├── Cert/Lrat.lean     #   verified LRAT checker, kernel-reducible (trusted path)
│   │   ├── Cnf.lean, Solver.lean, Bmc.lean, KInduction.lean, Pdr.lean
│   │   ├── SimDiagram.lean    #   simulation-diagram tactic
│   │   └── Dbsp.lean          #   reflective DBSP normalizer
│   ├── Hw/                    # L3 — hardware EDSL + verified compiler (generic)
│   │   ├── Action.lean, Rule.lean, Semantics.lean
│   │   ├── Netlist.lean, NetlistSem.lean, Compile.lean
│   │   └── View.lean          #   View q typed construct (DBSP obligation in constructor)
│   ├── Emit/                  # L4 — the boundary layer (generic: netlist in, µVerilog out)
│   │   ├── MicroVerilog/      #   Ast, Semantics, Print, Parse, RoundTrip, Axiom (THE axiom)
│   │   └── Emitter.lean
│   ├── Book/                  # L6 — documentation engine (generic over InstrDecl + ledgers)
│   │   ├── Model.lean, Extract.lean, Render/Html.lean, Render/Print.lean
│   └── Logic/                 # L1 generic parts only: BI-algebra core, step-indexing
│       ├── Sep/Bi.lean, StepIndex.lean
│
├── Machines/                  # ═══ THE MACHINES ═══
│   ├── Acc8/                  # the pathfinder: 8-bit accumulator machine, ~8 ops
│   │   ├── Spec.lean          #   state, ISA as InstrDecl terms, step, TSys instance
│   │   ├── Iss.lean, BitLevel.lean, Core.lean (L3 EDSL core, Phase 2)
│   │   └── Theorems/A1.lean   #   decode totality, asm round-trip (T1-analog); later A-EV
│   └── Lnp64u/                # the driving use case
│       ├── Types.lean         #   frozen µ parameters, ids, Errno, Fault, WcetClass   [DONE]
│       ├── Cap.lean           #   handle bit-shape, entries, lineage, regions        [DONE]
│       ├── State.lean         #   full machine state incl. gates, Mover, in-flight   [DONE]
│       ├── Manifest.lean      #   reset-ROM manifest, initial state, well-formedness
│       ├── SpecM.lean         #   semantics monad: total, faults-as-values
│       ├── Isa/Base.lean      #   ~15 base ops as InstrDecl terms
│       ├── Isa/System.lean    #   11 system ops
│       ├── Isa.lean           #   isa : Array InstrDecl — the single source
│       ├── Step.lean          #   cycle step: scheduler ∘ core retire ∘ Mover word; TSys
│       ├── BitLevel.lean, Iss.lean
│       ├── Logic/Invariant/   #   Phase-1 invariants; Sep/Resource.lean shares T9 terms
│       ├── Hw/                #   multicycle core, pipeline, Mover in the L3 EDSL
│       └── Theorems/          #   T1..T9, Refinement, Emission, Ledger.lean
│
├── Tools/                     # thin mains: Audit, Iss, Asm, Emit, BookGen
├── Tests/                     # golden tests
├── checker/                   # L5 — separate Lake package, zero Loom/Machines imports [Ph 4]
├── rtl/                       # emitted Verilog (build output, gitignored)
├── fpga/                      # per-target vendor projects + lockstep harness [Ph 2]
└── scripts/                   # CI glue, import-DAG lint
```

---

## 4. The spine: key signatures

`Loom/Core/Ts.lean` (built): `TSys` (relational step), `Inductive`/`Invariant` + induction
principle, `TSys.ofFun` for deterministic machines, `Simulation` (abstraction function,
commuting squares, invariant pullback, composition), `StutterSimulation` (multicycle refinement),
`BitSys` + `toTSys`.

`Loom/Isa/Instr.lean` (next): generic instruction declarations —

```lean
structure Sig where            -- per-machine encoding signature
  wordBits : Nat               -- instruction word width (Acc8: 16, LNP64-µ: 32)
  opcodeLo opcodeBits : Nat    -- where the opcode field lives
  fields : List FieldSpec      -- named operand fields (positions/widths)

structure InstrDecl (sig : Sig) (Sem Cost : Type) where
  mnemonic : String
  opcode   : BitVec sig.opcodeBits
  operands : List sig.FieldRef -- which fields this op reads
  sem      : Sem               -- opaque to Loom; the machine's Step consumes it
  cost     : Cost              -- opaque cost label (LNP64-µ: WcetClass)
  prose    : ProseBlock        -- the book paragraph, structured not stringly
```

Loom provides generically: `decode`/`encode` over a `Sig`, decidable totality/determinism/
round-trip obligations (the T1 kit), conformance-vector generation, and the book extractor.
The machine provides: state, the semantics payload and its interpreter, and the glue theorem
instances.

---

## 5. Layer notes

**Loom.Isa + machines' L0.** Order: generic `Sig`/`InstrDecl`/`Decode` → **Acc8 complete ISA +
A1 theorems** (the framework's first user, kept deliberately trivial) → LNP64-µ base ops → T1 →
system ops → full T1 → macro DSL last, with elaborated `isa` defeq to the structure-level one as
its regression oracle.

**L1 µLog.** Generic BI-algebra core and step-indexing live in `Loom/Logic/`; everything that
mentions µ's resources (memory ranges, cap slots, lineage cells, budget time) lives in
`Machines/Lnp64u/Logic/`, with `Sep/Resource.lean` sharing T9's conserved-quantity definitions.
Phase 1 mainline is plain invariants; the logical relation is Phase 3 and gates nothing.

**L2 Dp.** Engines search, certificates convince. `Cert/Lrat` first (trusted piece,
kernel-reduction benchmark = go/no-go data point), then Cnf/Solver/Bmc, then KInduction, then
Pdr. All generic over `BitSys`.

**L3 Hw.** Typed deeply enough that `View q` can demand its DBSP derivative proof as a
constructor argument. Semantics before compiler; compiler before any core. **Acc8's core is the
EDSL's first user and the first design through the compiler**; LNP64-µ's multicycle core follows.

**L4 Emit.** µVerilog AST finalized early (its austerity is a negotiation with the outside
world). **Acc8 is the first design emitted and the first on FPGA** — it debugs the boundary and
the vendor flows at 1/20th the size before LNP64-µ arrives. `Axiom.lean` contains the single
`axiom`; audit whitelists it for emission-dependent theorems only.

**L5 checker/.** Phase 4; only the package boundary exists from the start (P6).

**L6 Book.** Skeletal early: generic extractor walks any machine's `isa`; Acc8's two-page book
is the smoke test; LNP64-µ's book is the product.

**L7 fpga/.** Phase 2. Lockstep harness consumes `Loom/Core/Trace.lean`, frozen in Phase 0.

---

## 6. Import DAG (enforced by `scripts/check-imports.sh` + audit)

```
Loom.Core ← Loom.{Isa, Dp, Hw, Logic}      Loom.Hw ← Loom.Emit      (all machine-free)
Loom.*    ← Machines.Acc8, Machines.Lnp64u  (machines use the toolchain, never vice versa)
Machines.<m>.Theorems imports that machine + Loom; nothing imports Theorems except Ledger/Book
Loom.Book imports Loom.Isa only; machine book builds pass their isa/ledger as arguments
Tools imports anything; nothing imports Tools
checker/ imports NOTHING from this package (separate Lake package)
Mathlib may be imported anywhere except checker/
```

Additional rules: `Loom.Hw` never imports `Loom.Isa` (hardware designs are not tied to the
spec framework; refinement lives machine-side, which sees both); the µVerilog axiom is imported
only by emission theorem files.

---

## 7. Theorem ledger

Status: `—` not stated · `S` stated (sorry) · `P` proved (sorry'd deps) · `✓` proved clean.

**Acc8 (pathfinder):**

| Thm | Statement (short) | Phase | Status |
|-----|-------------------|-------|--------|
| A1 | decode total/det; asm∘disasm = id | 0 | ✓ |
| A-R | Acc8 EDSL core ⊑ Acc8 spec | 2 | — |
| A-EV | Acc8 netlist ≃ emitted µVerilog | 2 | — |

**LNP64-µ:**

| Thm | Statement (short) | Form | Phase | Status |
|-----|-------------------|------|-------|--------|
| T1 | decode total/det; asm∘disasm = id; ABI bound; null-handle | direct | 0 | — |
| T2 | authority confinement (invariant form) | invariant | 1 | — |
| T2′ | authority confinement (adversarial log-rel) | log-rel | 3 | — |
| T3 | temporal safety, spec level | invariant | 1 | — |
| T3′ | temporal safety as RTL cycle bound K | cycle bound | 3 | — |
| T4 | integrity / frame (4 channels + scrub equalities) | invariant | 1 | — |
| T4′ | frame, adversarial form | log-rel | 3 | — |
| T5 | noninterference (2-safety, path-free pairs) | 2-safety | 1 | — |
| T6 | totality / no-hostage | invariant + bound | 1 | — |
| T7 | Σ Q/P ≤ 1 ⟹ budget delivery; WCET lemmas | conditional | 1/3 | — |
| T8 | ownership transfer; W^X; status-word safety | invariant | 1 | — |
| T9 | conservation of slots/lineage/budget | invariant | 1 | — |
| R-MC | multicycle core ⊑ spec | StutterSimulation | 3 | — |
| R-PL | pipeline ⊑ spec (Burch-Dill) | Simulation | 3 | — |
| C-HW | EDSL→netlist compiler correct | TSys equality | 2 | — |
| E-V | netlist ≃ emitted µVerilog text | TSys eq + axiom | 2 | — |

---

## 8. Phases and work order

Take the first unchecked box whose deps are checked. `[m]` marks machine-side work, `[t]`
toolchain work.

### Phase 0 — Bootstrap
*Gate: generic Isa framework proven by two machines; T1 + A1 discharged; both ISSes boot with
the lockstep trace format; skeletal book; L3 semantics designed; µLog design doc; µVerilog
subset + semantics drafted.*

- [x] **0.1** [t] Scaffold: lakefile (Loom/Machines/Tools libs, exes), toolchain pin, Mathlib
      pinned at v4.28.0, module tree, .gitignore. *(CI + import-linter stub → 0.12)*
- [x] **0.2** [t] `Loom/Core/Word.lean` + `Fun.lean` — word types, field kit, table update.
- [x] **0.3** [t] `Loom/Core/Ts.lean` — the spine (§4).
- [x] **0.4** [m] `Machines/Lnp64u/Types.lean`, `Cap.lean` — frozen parameters, handle shape,
      lineage cells, regions.
- [x] **0.5a** [m] `Machines/Lnp64u/State.lean` — full machine state (gates, Mover, in-flight).
- [ ] **0.5b** [m] `Machines/Lnp64u/Manifest.lean` — manifest, initial state, well-formedness.
      *(deps: 0.5a)*
- [ ] **0.6** [m] `Machines/Lnp64u/SpecM.lean` — semantics monad, total, faults-as-values.
      *(deps: 0.5a)*
- [x] **0.7** [t] `Loom/Isa/Sig.lean` + `Instr.lean` + `Decode.lean` — generic declarations,
      decode/encode, T1 obligation kit. *(deps: 0.2)*
- [x] **0.8** [m] **Acc8 complete**: `Machines/Acc8/Spec.lean` (state, ISA as `InstrDecl`
      terms, step, `TSys`), `Iss.lean`; `Theorems/A1.lean` **discharged**. The framework's
      first user. *(deps: 0.7)*
- [ ] **0.9** [m] `Machines/Lnp64u/Isa/Base.lean` (~15 base ops) over the generic framework;
      Lnp64u decode/encode instances. *(deps: 0.6, 0.7)*
- [ ] **0.10** [t] `Loom/Dp/Cert/Lrat.lean` — verified LRAT checker + kernel-reduction
      benchmark (go/no-go). *(deps: 0.2)*
- [ ] **0.11** [m] **T1 (base ops) stated + discharged**; `Theorems/Ledger.lean` exists.
      *(deps: 0.9, 0.10)*
- [ ] **0.12** [t] `Tools/Audit.lean` + `scripts/check-imports.sh` — ledger walk, sorry/axiom/
      `native_decide` policing, import DAG (incl. P0), wired into CI. *(deps: 0.11)*
- [ ] **0.13** [m] `Isa/System.lean` — the 11 system ops. *(deps: 0.9)*
- [ ] **0.14** [m] `Step.lean` — cycle step: refill → core issue/retire → Mover word; `TSys`.
      *(deps: 0.13, 0.5b)*
- [ ] **0.15** [t+m] `Loom/Core/Trace.lean` frozen; `Iss.lean` + `Tools/Iss.lean` — **first
      light: both machines boot under `lake exe iss`**. *(deps: 0.14, 0.8)*
- [ ] **0.16** [m] T1 extended to the full opcode set. *(deps: 0.13, 0.11)*
- [ ] **0.17** [t] `Loom/Isa/Dsl/` — macro front-end; defeq regression on both machines'
      `isa`. *(deps: 0.16)*
- [ ] **0.18** [t] `Loom/Book/` skeleton — generic extractor + HTML; Acc8 book as smoke test,
      Lnp64u opcode table + instruction pages. *(deps: 0.15)*
- [ ] **0.19** [t] Design docs: `Loom/Hw/DESIGN.md`, `Machines/Lnp64u/Logic/DESIGN.md`,
      `Loom/Emit/MicroVerilog/` Ast + Semantics drafted. *(deps: 0.3; parallel)*

### Phase 1 — Spec-level security (LNP64-µ) + engine bring-up (Loom)
*Gate: T2–T9 in invariant form; k-induction + BMC online; conformance suites generating; the
multicycle core in the EDSL lockstep against the ISS.*

- [ ] **1.1** [m] `BitLevel.lean` for both machines (Acc8 first) + correspondences (P3).
- [ ] **1.2** [t] `Dp/Cnf, Solver, Bmc` — first certificate-checked BMC result (on Acc8, then
      Lnp64u).
- [ ] **1.3** [m] T9 conservation (seeds `Logic/Sep/Resource.lean`).
- [ ] **1.4** [m] T2 invariant form. **1.5** [m] T8, T4. **1.6** [t+m] `Dp/KInduction`; T3 +
      revoke-bound lemmas. **1.7** [m] T6; T5 as 2-safety product. **1.8** [m] T7 + WCET
      lemma skeletons.
- [ ] **1.9** [t+m] Conformance generation (generic) + both machines' suites self-checked.
- [ ] **1.10** [t] `Hw/Action|Rule|Semantics` — EDSL + atomic semantics as TSys.
- [ ] **1.11** [m] Acc8 core in the EDSL, lockstep vs Acc8 ISS; then Lnp64u multicycle core,
      lockstep vs ISS on the conformance suite.
- [ ] **1.12** [t] `Dp/Pdr.lean` as scaling demands.

### Phase 2 — Silicon path
*Gate: compiler verified; emission theorem + round-trip done; Acc8 then LNP64-µ multicycle on
two vendors' FPGAs, chain kernel-checked to the Verilog.*

- [ ] **2.1** [t] `Hw/Netlist(+Sem)`; **2.2** [t] `Hw/Compile` verified (C-HW).
- [ ] **2.3** [t] µVerilog Print/Parse/RoundTrip; **2.4** [t] Emitter + Axiom + emission
      theorem (E-V, instantiated as A-EV first); **2.5** [t] `lake exe emit` / `rtl` target.
- [ ] **2.6** [t] `fpga/` lockstep harness over `Loom.Core.Trace`.
- [ ] **2.7** Acc8 on FPGA (both vendors) — boundary/pathfinder; **2.8** Lnp64u multicycle on
      vendor A + B; **2.9** T7 WCET corroboration per target.

### Phase 3 — Refinement, pipeline, logic upgrade
- [ ] **3.1** [t] `Dp/SimDiagram` tactic (A-R as its first client); **3.2** [m] R-MC.
- [ ] **3.3** [t] `Hw/View` + `Dp/Dbsp`; **3.4** [m] pipeline + R-PL.
- [ ] **3.5** [m] T3′ concrete K at RTL; T6/T7 cycle-bound forms per target.
- [ ] **3.6** [t+m] `Loom/Logic` Sep core + StepIndex; Lnp64u LogRel; **3.7** [m] T2′/T4′.

### Phase 4 — Capstone
- [ ] **4.1** [m] Revoke demo on FPGA, K on a logic analyzer. **4.2** [t] `checker/`
      re-verifying T2/T3′/E-V exports. **4.3** [m] LNP64-µ book v1.0. **4.4** ASIC dry run
      (untrusted LEC). **4.5** Program review; next machines (64-bit LNP, 6502, exotic
      targets) scoped as new `Machines/` entries with zero toolchain rework as the success
      criterion.

---

## 9. Open decisions

| # | Decision | Resolve by | Current lean |
|---|----------|-----------|--------------|
| D1 | LNP64-µ encoding layout | 0.9 | 32-bit word; opcode [5:0], rd [8:6], rs1 [11:9], rs2 [14:12], imm17 [31:15]; packed-word operands for cap ops |
| D2 | LRAT via kernel reduction fast enough? | 0.10 | If slow: smaller per-obligation certificates; Rule 1 non-negotiable |
| D3 | Simulation function vs relation for Burch-Dill | 3.1 | Both already on the spine (`Simulation`, `StutterSimulation`); add relation variant only if flushing demands it |
| D4 | SAT solver + protocol | 1.2 | cadical, DIMACS in / LRAT out, subprocess, untrusted |
| D5 | Memory representation | done | Function at Prop level (built); packed arrays at bit level; P3 bridges |
| D6 | Book render targets | 0.18 HTML; print by 4.3 | HTML first; in-house print pass, scoped ruthlessly |
| D7 | Variable-length / exotic encodings in Loom.Isa | with the machine that needs them | Fixed-width `Sig` now; extension lands only with a consuming machine (e.g. 6502) |

---

## 10. Definition of "clean" (the standing self-check)

1. `lake build` succeeds warning-clean.
2. `lake exe audit` matches §7 exactly.
3. No `sorry` outside `Machines/*/Theorems/` + `Wip/`; no `axiom` outside
   `Loom/Emit/MicroVerilog/Axiom.lean`; no `native_decide` reachable from any ledger.
4. The import DAG of §6 holds — in particular `Loom` imports nothing from `Machines`.
5. Every merged component names the obligation it discharges (Rule 2), in its `DESIGN.md`.
6. `lake exe iss` boots both machines' golden images; traces match checked-in goldens
   (from 0.15 onward).
