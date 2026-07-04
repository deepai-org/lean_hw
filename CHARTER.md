# Loom: a verified-processor toolchain in Lean — and LNP64-µ, its first machine

**A program plan for a from-scratch, vertically integrated Lean stack — spec, logic, decision procedures, hardware compiler, documentation engine, independent checker, all in-house — whose emission boundary is verified Verilog, portable across FPGA vendors and to silicon.**

**Scope: the toolchain is the product; LNP64-µ is its first use case.** The stack described below — the spec DSL and its projections, the proof stratum, the decision procedures, the hardware EDSL and verified compiler, the µVerilog emission layer, the documentation engine, the independent checker — is built **machine-generic**, under the name **Loom**, and is expected to outlive and outgrow any one processor. LNP64-µ is the first machine modeled with it: a good small one, with theorems (T1–T9) we actually care about proving, whose obligations drive every toolchain feature (Rule 2). Later machines — a 64-bit LNP, an 8-bit 6502, exotic or experimental architectures — are intended to be new entries under `Machines/` with zero toolchain rework. To keep that separation structural rather than aspirational, the repository carries a second, deliberately tiny machine (**Acc8**, an 8-bit accumulator machine) through every toolchain layer: every generic construct is exercised by at least two machines, the toolchain never imports a machine, and Acc8 — being small — reaches each layer first as the pathfinder. Where the text below speaks of the layers L0–L7, read them as Loom's layers; where it speaks of the machine, read LNP64-µ, the driving instance.

Doctrine: **papers in, domain code never.** Published metatheory (Kôika's atomic-rule semantics, Cerise's logical-relation technique, DBSP's incremental algebra, IC3/PDR, Burch-Dill) is used freely as literature, and every line of *domain-specific* code in the artifact and its tools — the spec DSL, the logic, the hardware compiler, the emission layer, the checkers, the book pipeline — is written in-house in Lean 4. Standard, generic computer-science algorithms (SAT solving, arithmetic decision procedures, and kin) may be brought in as libraries, always as **untrusted components**: their outputs enter the trusted path only as certificates checked by the Lean kernel, so a wrong answer from a library is a build failure, never a wrong theorem.

---

## 1. Objective and capstone artifact

One Lean package in which: `#eval` boots LNP64-µ (the compiled spec is the instruction-set simulator); theorems T1–T9 are checked by the Lean kernel; the prose ISA book is emitted by our own documentation engine as a projection of the instruction declarations; the conformance suite falls out of the same declarations; and `lake build rtl` emits a Verilog module accompanied by a kernel-checked theorem that the module — under the formalized semantics of the emitted subset — denotes exactly the circuit the refinement proof is about. That module is then carried by any vendor flow to any FPGA, and by a standard ASIC flow to silicon, with the trust statement ending, explicitly and by design, at the Verilog.

The headline demo: LNP64-µ on FPGA, adversarial four-domain workload plus the Mover, `cap_revoke` retires, and no agent writes under the revoked authority within a machine-checked bound K — kernel-checked from the ISA specification to the Verilog, corroborated on hardware through lockstep co-simulation and the generated conformance suite.

The strategic rationale: every drift bug caught by hand in the spec-hardening rounds was two projections of one fact maintained separately. This stack is the design in which separate maintenance is structurally impossible — spec, chip, proof, and book as projections of one set of terms, produced and checked by tools that are themselves part of the same artifact.

## 2. The machine

LNP64-µ exactly as frozen: one in-order 32-bit core (multicycle FSM first, then a 2-stage pipeline), 8 GPRs with `r0`=0, no caches, MMU, speculation, interrupts, or FP, aligned word-only loads and stores; one Mover as a second master, one word per cycle, re-checking source and destination capability generations every word; four static single-threaded domains from a reset-ROM manifest carrying budgets, priorities, initial cap tables, and gate configs; physical static memory with four region registers per domain as cached authority, swept by revoke; two capability classes (Memory, Gate) with the full-LNP64 handle bit-shape at tiny instantiated widths (16 slots per domain, 8-bit generations with retirement, per-domain lineage quotas); no upcalls — every fault is domain-fatal with a precise cause register; one blocking construct, the serialized gate, chain depth ≤ 4, one capability per call and per return; completion via caller-owned status words, the 4-word `move` descriptor being the only argblock in the ISA. Roughly 25 opcodes: ~14 base ops plus 11 system ops (`cap_dup`, `cap_drop`, `cap_revoke` in its strongest single class, `mem_grant`, `map`, `unmap`, `gate_call`, `gate_return`, `move`, `yield`, `halt`).

Two disciplines attach to the machine. First, **µ is a morphism of the full architecture, not a mascot**: handle layout, `-errno` convention, snapshot rule, holder-field deadlock check, donation semantics, and revoke-returns-after-ack keep their exact full-LNP64 shape, so every later phase extends an invariant rather than rewriting one. Second, the machine's austerity is load-bearing twice: it sized the proofs, and it sizes the in-house tools — a ~25-opcode, few-thousand-LUT, cache-free design is what makes a from-scratch model checker, documentation engine, and emission layer finishable rather than fantasy.

## 3. The vertical stack

Seven layers, each existing to discharge obligations for the layer above.

### L0 — Spec DSL and projections
The metaprogrammed instruction-declaration DSL: one declaration per instruction carrying encoding fields, operational semantics, error contract, WCET class, and prose paragraph as components of a single term. Projections: the compiled ISS (native code, with a lockstep trace format shared by RTL simulation and hardware), the flat opcode table, the assembler/disassembler pair, the conformance suite, and the source hooks for L6's book. Interchange formats do not exist in this stack; the assurance role such exports would play moves to L5.

### L1 — The proof stratum: µLog
A bespoke capability logic built for this machine rather than a framework port. Two components. First, a small in-house separation-logic core: a BI algebra over the machine's resources — memory ranges, cap slots, lineage cells, budget time, which are exactly T9's conserved quantities, so the logic's resource algebra and the conservation theorem share definitions — with a later modality and step-indexing. Second, the adversarial-code theorem done directly: a step-indexed logical relation defined straight over the µ spec — the Cerise *technique* from the papers, none of the Cerise or Iris code — giving T2/T4 in their strongest form ("unknown code holding these capabilities cannot exceed them," quantified over all programs, with the Löb-style circularity capability machines require because code holds capabilities to code). Honest budget: this is the single hardest in-house component and it must be earned rather than declared; the Iris and Cerise papers are a complete blueprint even though their code is off-limits. The scaffolding comes first and gates nothing: bare state-machine invariants with product constructions, near `decide`-range at 4 domains × 16 slots, so T2–T9 land early in invariant form and upgrade to logical-relation form when µLog matures.

### L2 — Decision procedures: certifying engines over library solvers
The automation that makes ten thousand obligations tractable, structured in two tiers. The **domain tier is in-house**: bounded model checking, k-induction, and an IC3/PDR engine over L3's transition systems; the simulation-diagram tactic (abstraction function in, commuting squares out — the core tool for both the multicycle refinement and the pipeline's flushing proof); a reflective DBSP normalizer for the view lemmas. The **generic tier is libraries**: these engines call standard SAT and arithmetic solvers as untrusted backends, and every discharge returns to the kernel as a checked certificate (LRAT for propositional cores, and analogous certificate formats elsewhere), so no solver — library or in-house — ever joins the TCB, and solver upgrades are performance decisions with no trust consequences. This track also owns the CI proof-farm and should plan for the machine-assisted proof-engineering curve — premise selection, proof repair against CI, tactic search — which is concentrating in the Lean ecosystem and compounds across thousands of routine refinement obligations.

### L3 — Hardware EDSL and verified compiler
The Kôika successor: rule-based atomic semantics with the one-rule-at-a-time model and its scheduling-correctness story taken from the published metatheory and implemented fresh; verified compilation to a netlist IR of registers, LUT-expressible combinational logic, and memories. The distinguishing construct: **maintained views as a typed construct** — `View q` circuits whose constructors demand the DBSP derivative proof, with incrementality-of-composition discharged once as library theorems — so the readiness OR-tree, the region-sweep aggregation, and the Mover's generation re-check machinery are correct-by-construction instances whose data structures *are* the T2/T3/T9 induction hypotheses, the same terms in the same file. Engine snapshot points map onto atomic rules as linearization points.

### L4 — Verified Verilog emission (the boundary layer)
The stack's lower boundary, designed for portability across FPGA vendors and to silicon, with nothing at the boundary trusted as code. Three pieces.

**µVerilog, a formalized subset.** Define, in Lean, a deliberately minimal synthesizable Verilog subset — flat structural modules, `assign` continuous assignments, single-clock `always_ff` registers, explicit memory arrays; no inference-sensitive constructs, no latches, no tool-dependent idioms — and give it an operational semantics as synchronous transition systems. The subset is chosen for the property that every serious tool, FPGA or ASIC, agrees on its meaning; where the standard leaves latitude, the subset excludes the construct.

**A verified emitter.** The theorem: for every netlist-IR design, the emitted µVerilog module's transition system, under the formalized semantics, equals the IR's. The printer itself — AST to text — is covered by a verified round-trip against an in-house parser (`parse(print(m)) = m`), so the text file, not just the tree, is inside the theorem. Nothing in emission is trusted code; the trust reduces to one **stated axiom: downstream tools implement the standard Verilog semantics on the µVerilog subset** — the assumption every trusted-pretty-printer design makes silently, here minimized by the subset's austerity and stated in the capstone theorem's fine print.

**Portability consequences.** Timing closure is a per-target, vendor-side activity: the WCET and cycle-bound theorems (T3/T6/T7) are stated conditional on a clock constraint, and each target discharges that condition with its own untrusted STA, corroborated on hardware by the lockstep harness and the generated conformance suite. Optional per-target assurance add-ons, funded on demand and never dependencies: for open flows whose post-synthesis netlists can be re-read, an in-house equivalence back-check against the IR; for ASIC, standard LEC in the same untrusted-corroboration slot; and, for one open FPGA family, a verified down-to-the-bitstream module if a future phase wants that depth for a flagship target.

### L5 — Independent assurance: the second checker
The monoculture hedge, built in-house: a small, from-scratch, deliberately different-in-style independent checker for Lean's kernel export format, used to re-verify the crown-jewel exports (T2, T3, the emission theorem) on every release. One program, two checkers, zero borrowed domain code. Lean-kernel soundness risk is additionally bounded by the kernel's small size and the program's certificate-heavy, kernel-reducible proof style.

### L6 — Documentation engine
A projection-native book pipeline: a Lean metaprogram that walks the instruction declarations and theorem statements and typesets the ISA book (HTML and print), with every table, enum count, encoding diagram, and quoted bound generated from the same terms the kernel checked — the document-drift failure mode made unrepresentable. Scoped ruthlessly: it exists to serve exactly one book, not to compete with general documentation systems.

### L7 — Integration and demo
Multi-target from the start, which the Verilog boundary makes cheap: bring-up on at least two vendors' parts to prove the portability claim isn't theoretical; the lockstep harness driving ISS, L3 simulation, and hardware from one trace format; on-hardware corroboration of the T7 WCET lemmas and the T3/T6 cycle bounds per target; the revoke demo instrumented so K is observable on a logic analyzer next to the theorem it instantiates.

## 4. The theorem ladder

T1–T9, instantiated at µ scale, distributed across the layers above.

**T1 — Encoding and convention soundness.** Decode totality and determinism over all instruction words, assemble∘disassemble identity, the per-op return-ABI bound, null-handle unconstructibility from generation ≥ 1. Nearly free at definition time: the DSL emits these obligations per declaration and certificate-checked bitblasting discharges them in the kernel.

**T2 — Authority confinement.** Authority of every reachable state lies within the closure of the manifest under dup-narrow, grant-subrange, gate-transfer, drop, revoke. Proved parametrically; the tiny instantiation cross-checked by the L2 engines; upgraded to the full adversarial logical-relation form when µLog lands.

**T3 — Temporal safety, machine-wide.** The crown jewel: after `cap_revoke` retires, no agent — core via any region register, Mover mid-transfer — accesses under any descendant; generation-retirement no-resurrection; stated at RTL level as a concrete cycle bound. The demo is this theorem made visible.

**T4 — Integrity / frame theorem.** Exactly four influence channels at µ scale (granted memory, gate reply, Mover writes into granted destinations, the status word), plus the scrub equalities: activation entry registers ∈ {args, sp, zeros}; caller resumption = saved file plus `rd` := reply.

**T5 — Noninterference.** Architectural noninterference between manifest-disjoint domain pairs (donation deliberately couples timing along authority paths, so the theorem quantifies over pairs with no path), as 2-safety via the L2 engines; no speculation and no caches leave the microarchitectural leakage contract almost without residue.

**T6 — Totality and no-hostage.** Closed outcome set {retire, `-errno`, domain-halt}; the caller resumes within f(max_donation, depth ≤ 4, one Mover word + sweep-ack), quantified over all callees including adversarial ones — the statement only a proof can make.

**T7 — Real time.** Σ Q/P ≤ 1 at reset ⟹ per-period budget delivery; the gate blocking bound with inheritance; 25 WCET lemmas, finite by construction, stated conditional on the clock constraint and validated against hardware cycle counts per target.

**T8 — Whole-machine memory safety as ownership transfer.** Grant–revoke–regrant: the prior holder and its Mover traffic never touch the range after the new holder receives it; machine-wide W^X; status-word safety.

**T9 — Conservation.** Cap slots, lineage cells, budget time exactly accounted; drop and revoke restore precisely what was held. The per-domain lineage quota is already the first proof-forced design decision — a global pool is a cross-domain exhaustion channel violating T5/T9 jointly — and the program should expect and welcome more of these.

## 5. Trusted computing base

At steady state: **the Lean kernel, and the µVerilog-semantics axiom** (downstream tools implement standard Verilog semantics on the emitted subset). Two items. No trusted printer (the emission theorem replaced it), no importers, no solvers — library or otherwise — no synthesis or PnR tools; and the L5 checker independently re-verifies the kernel's own judgments. The residual assumptions below the boundary are corroborated per target, never proven, and never load-bearing for any theorem.

## 6. Governance rules

**Rule 1 — no `native_decide` on the trusted path.** Kernel reduction and kernel-checked certificates only; the Lean compiler serves the ISS and the tools, never the theorems.

**Rule 2 — no infrastructure merges without discharging a numbered µ theorem.** Seven in-house layers is seven attractive nuisances, and the known failure mode of hardware-in-a-prover efforts is drifting into infrastructure because infrastructure is more fun than refinement squares. Every DSL feature, tactic, EDSL construct, boundary-layer capability, and doc-engine feature lands attached to a T1–T9 or emission-chain obligation it discharges.

**Rule 3 — µ is a morphism, not a mascot.** No µ-local simplification may break shape-compatibility with full LNP64.

**Rule 4 — papers in, domain code never; generic algorithms as untrusted libraries.** External metatheory is read and cited. Domain-specific external code — provers, hardware frameworks, spec languages, doc systems — is neither vendored, ported line-by-line, nor linked. Generic algorithmic libraries (SAT, arithmetic decision procedures, and similar textbook machinery) are permitted, always untrusted, always behind kernel-checked certificates. **Mathlib is an accepted dependency**: it is generic mathematics, and its proofs are checked by the same Lean kernel as ours, so it adds nothing to the TCB and needs no certificate discipline — the untrusted-library rule applies to *computational* engines, not to kernel-checked lemma libraries.

**Rule 5 — every rebuild names its win.** Each in-house component states, in its design doc, the dimension on which it beats what it replaces — smaller TCB, exact fit to the DSL, kernel-checked certificates, one fewer language — and the claim is reviewed at phase gates. Vertical integration stays a doctrine, not a reflex.

**Rule 6 — nothing above the boundary depends on anything below it.** No theorem, proof, or generator may assume any property of any vendor tool beyond the µVerilog-semantics axiom; per-target facts (achieved clock, resource fit) enter only as discharge of stated conditions.

## 7. Phases and gates

Ordered by dependency, each phase gated on a demonstrated first-light artifact rather than a date.

**Phase 0 — Bootstrap.** Gate: spec DSL v0 with T1 discharged for the full opcode set via certificate-checked bitblasting; the ISS booting with the lockstep trace format; the L6 doc engine emitting a skeletal book; L3 semantics designed from the Kôika papers; the µLog design doc; the µVerilog subset and its semantics drafted.

**Phase 1 — Spec-level security.** Gate: T2–T9 proved over the spec in invariant form; the in-house k-induction and BMC engines online and discharging the T3/T6 bound lemmas; the conformance suite generating; the multicycle core written in the L3 EDSL and running in compiled simulation against the ISS.

**Phase 2 — Silicon path.** Gate: L3 compiler verified; L4 emission theorem and print/parse round-trip done; **first light on FPGA — the multicycle core on two different vendors' parts, the chain kernel-checked to the Verilog**.

**Phase 3 — Refinement, pipeline, logic upgrade.** Gate: the multicycle refinement proof (near-definitional commuting diagram); the 2-stage pipeline via Burch-Dill flushing through the simulation-diagram tactic; T3/T6/T7 as conditional cycle-bound theorems discharged per target; µLog's logical relation landed and T2/T4 upgraded to full adversarial quantification.

**Phase 4 — Capstone.** Gate: the end-to-end revoke demo on FPGA with kernel-checked K to the Verilog boundary; the book shipping from L6; the L5 checker re-verifying the crown jewels; an ASIC-flow dry run (untrusted LEC corroboration) as the silicon-readiness gate; program review for the ladder beyond µ.

## 8. Risks

**µLog is genuinely hard.** Step-indexed separation logics are subtle; this is the one place "we can do better" must be earned. Mitigations: the invariant-form mainline means nothing gates on it; scope it to one machine; staff it with someone who knows the Iris literature cold; the papers are a complete blueprint even with their code off-limits.

**The downstream-toolchain gap.** The honest cost of the Verilog boundary: synthesis, PnR, and bitstream or mask generation are corroborated, not proven. Mitigations, layered: the µVerilog subset's austerity leaves tools nothing inference-sensitive to disagree on; hardware lockstep and the generated conformance suite are continuous falsification per target; optional per-target back-checks (open-flow netlist equivalence, ASIC LEC, the bitstream module) are funded-on-demand assurance; and the boundary axiom is stated in the theorem rather than implied. A vendor miscompilation manifests as a lockstep divergence, localized below the boundary by construction.

**Tool-building drift.** Rules 2 and 5 with hard phase gates; Phase 2's two-vendor first light is placed to force L4 and L7 through to done rather than polished.

**Monoculture.** One language, one team, one kernel. Mitigations: L5's independent checker (different code, different style, same judgments); the certificate-heavy, kernel-reducible proof style; and published kernel exports so any third party can re-verify with tools we didn't write.

**Subset expressiveness.** µVerilog's austerity could pinch at later rungs (memory-inference styles, clock-domain idioms for multicore). Mitigation: the subset grows only by formalized construct, each addition carrying its semantics and its emission-theorem extension — Rule 2 applied to the boundary itself — with the subset owned by one person so it doesn't grow by committee.

## 9. The ladder beyond µ

Each µ cut names the phase that restores it, one obligation class at a time: MMU, page tables, and TLB → the real DVM broadcast-ack proof (the region-sweep proof is its induction hypothesis); a second core → TSO, coherence, and `fence.sc`'s global order; upcalls and the continuation stack → precise delivery and the editable-payload/engine-frame trust boundary; dynamic domains, CLONE, and exec → COW and atomic exec commit (where the temporal-bug class returns exactly when the phase does); send/recv and waitsets → transactional commit order and pin disciplines; multiple revoke classes → the lazy/forced/quiesce visibility lattice; service dispatch and RESTAMP → the stamp-cell indirection proofs. Because µ is a morphism of the full machine, each rung extends invariants and abstraction functions built here rather than replacing them — and because the Verilog boundary is vendor-neutral, the ladder can end in silicon: every rung up to and including tape-out rides the same emitted artifact and the same two-item trust statement, on infrastructure the program owns outright.

---

**Summary.** A stack with no borrowed domain code and a two-item TCB — the Lean kernel plus one public-standard axiom about a deliberately austere Verilog subset — in which spec, chip, proofs, book, conformance suite, and the tools that produce and check them are projections and instruments of one Lean artifact. Generic algorithms arrive as untrusted libraries behind kernel-checked certificates; everything that defines this machine is written here. The capstone theorem reaches from the ISA declaration to the emitted Verilog, the same module targets every FPGA vendor and the ASIC flow, and the demo makes the crown jewel visible: no agent writes after revoke, within K cycles, kernel-checked, on hardware in front of you.
