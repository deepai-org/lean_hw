# Loom capability and assurance gaps

This is the current gap ledger. A gap is recorded when a real machine, proof,
release, or hardware campaign needs a capability the generic toolchain does
not yet provide. Completed implementation history lives in Git; active work is
ordered in [`NEXTSTEPS.md`](NEXTSTEPS.md).

## Current capability map

| Decision | Current capability | Main implementation |
|---|---|---|
| D9 | Single-clock, pre-cycle reads, ordered last-write-wins actions | `Loom/Hw/Semantics.lean` |
| D12–D14 | Read validity, emission well-formedness, and concrete-SSA identifier/CSE checks | `Loom/Hw/ReadsOk.lean`, `Loom/Release/` |
| D15 | Explicit environment-owned input ports | `Loom/Hw/Syntax.lean`, `Semantics.lean` |
| D16 | Rename, prefix, parallel composition, and connection | `Loom/Hw/Rename.lean`, `Compose.lean` |
| D17 | Stuttering simulation and a verified retiming seed | `Loom/Core/Ts.lean`, `Loom/Hw/Retime.lean` |
| D18 | Verified fast evaluator | `Loom/Hw/FastEval.lean` |
| D19 | Declared synchronous-read memory shape | `Loom/Hw/SyncRead.lean` |
| D21 | Adversarial-resolution toggle/2FF/XOR CDC contract | `Loom/Hw/CdcContract.lean` |
| D22 | Post-synthesis module/netlist equivalence workflow | `Loom/Netlist/`, `Tools/EqCheck.lean` |
| D23 | Bounded response, ranking, and simulation transport | `Loom/Core/Bounded.lean` |
| D28 | Step-to-cycle bounds through stuttering refinement | `Machines/Epoch/Refines.lean` |
| D30–D31 | Memory images, write ports, and read shapes in netlist checking | `Loom/Netlist/Mem.lean` |
| D32 | Proved CNF encoder for the declared module-expression fragment | `Loom/Netlist/Encode.lean`, `MiterProof.lean` |
| D34 | Reusable partial-event protocol machines and invariant/run lemmas | `Loom/Protocol/Machine.lean` |
| D36 | Priority orders as data with generated ordering lemmas | `Loom/Protocol/Priority.lean` |
| D37 | Emit-time refusal of undeliverable nonzero memory images | `Loom/Hw/MemInitOk.lean` |
| D38 | Memory realizability against declared target profiles | `Loom/Hw/MemTarget.lean` |
| D39 | Mandatory declared register outputs and non-export theorems | `Loom/Hw/Outputs.lean` |

## Open gaps

### D24 — first-class rely/guarantee contracts

Open designs currently express environment assumptions with design-specific
trace predicates. Loom needs a generic contract layer with:

- predicates over input traces or environment steps;
- satisfiability/non-vacuity witnesses;
- guarantee-to-rely composition compatible with `Design.connect`; and
- transport of invariants and bounded response under those contracts.

The driving cases are CDC command traces, memory/bus backpressure, and
multi-component protocol engines.

### D26 — proved monitor synthesis

The desired capability is to compile a safety/response specification into a
Loom monitor design and prove the monitor flags exactly the violating traces.
This is distinct from artifact equivalence: it turns a specification into
hardware that checks an environment.

### D27 — authenticated views of untrusted external state

Protocol engines need a reusable abstraction for bulk state stored outside the
trusted design: a checked cache or authenticated view over untrusted DDR,
possibly using MAC/Merkle and anti-replay data supplied by a separate crypto
component. Loom's reusable contribution is the refinement boundary and
checking interface, not a bespoke cryptographic primitive.

### D29 — multiple clocks by composition

`Design` remains single-clock. Multi-clock support should compose separately
compiled domains through proved CDC components and declared clock
relationships rather than change D9 semantics.

Required pieces:

- domain composition that emits one verified single-clock module per domain;
- a CDC library beyond the current toggle synchronizer (level, pulse,
  handshake, and eventually asynchronous FIFO protocols);
- rely/guarantee composition across domains; and
- conversion of bounds through declared clock ratios.

Asynchronous/self-timed logic is not part of this gap. It requires a different
semantic and physical formalism.

### D33 — synthesized-to-routed netlist equivalence

The current checker compares emitted modules with post-synthesis netlists.
OpenXC7 also produces a routed JSON netlist, so the next useful boundary is:

```text
emitted module ≡ synthesized netlist ≡ routed netlist
```

The work is target-specific cell coverage and robust correspondence after
packing/renaming. Start with a small design. FASM/frame/bitstream generation
remains a corroborated physical-flow boundary because the available device
database is not a vendor specification.

### D35 — refinement-by-cases support

Engine refinements repeat a common structure: abstraction, a small design
invariant for staged state, and exhaustive FSM/control cases for the commuting
square. A generic combinator or tactic should let each engine supply its
encoding, invariant, abstraction, and meaningful cases without restating the
simulation scaffolding.

### D32 continuation — complete the equivalence proof surface

The module-side encoder proof currently covers:

```text
lit reg and or xor not add sub eq ult mux slice zext sext
```

Still open:

- `shl`, `shr`, and `slt` on the module side;
- a proved reference semantics for the netlist cone/cell side;
- a proof that the executed memoized bit-blaster matches its reference
  definition; and
- reduction of per-design exclusions and acknowledged memory defects.

Until then, every run must report its fragment, exclusions, and assumptions.

### Single-source design and comparison coverage

Names, widths, state adapters, and lockstep comparison membership are still
duplicated in larger designs. Typed handles, declaration notation, and
generated complete comparators are required so a new state element cannot be
silently absent from evidence.

### Proof scaling

Many user-level invariant proofs still simplify a complete cycle. Generic
footprint frames, support inference, and stable cycle tactics are needed so
proof cost scales with the property's dependency cone.

### Target cost models

**Partly closed (2026-08-07, W6 first increment).** `Loom/Hw/Cost.lean`
supplies the abstract implementation-cost vector — `stateBits`, `bitOps`,
`macroBits`, `softBits`, `maxFanout` — computed from the `Design` with no
target knowledge, ordered componentwise (`Cost.le`, reflexive/transitive,
monotone under `+`). That order is what a verified transformation is meant
to be proved against: *this pass does not make the cost vector worse* needs
no calibration and cannot be invalidated by a tool release.
`Loom/Hw/CostTarget.lean` maps the vector to one target's resources and to
a closure-risk estimate, keeping **capacity** ("does it fit") and
**closure** ("will the tools close it") as separate claims, every number
carrying provenance/tool version/design family, fitted by
`scripts/fit_cost.py` from measured output (`scripts/cost_rows.json`).
`lake exe costreport` prints it.

**Second increment (2026-08-07):** `Loom/Hw/CostTransform.lean` proves the
claim *about actual transformations* — renaming is cost-neutral
(`prefixed_cost`), `par` is additive (`par_cost_le`, so `Cost.add_le_add`'s
premise is discharged by a real combinator), and the balanced tree builders
are never more area than the linear chain and on a non-empty list are one
operator cheaper (`reduceTree_treeCost_lt_foldr`). It also proves two things
FALSE, which is the more useful half:

- **`priTree` is not area-neutral** (`priTree_cost_gt`), but the margin is
  `n-1` bits, not a guard cone. See the third increment below: the original
  reading of this theorem was wrong.
- **`par` is not `≤` on `maxFanout`** when the parts alias register names
  (`par_maxFanout_gt`) — precisely what `parOkB` refuses, so the theorem takes
  read-disjointness as an explicit hypothesis.

**Third increment (2026-08-07): the cost was a tree cost applied to a DAG,
and it got a sign wrong.** `Loom/Emit/MicroVerilog/Print.lean` gives each
*structurally distinct* node exactly one wire (pointer memo + a
`(width, rendered RHS)` hash-cons table), so a duplicated subexpression is
one wire in the emitted Verilog. `Expr.cost` billed it twice. `bitOps` now
counts distinct hash-consed nodes (`Expr.hc` interns into an `ENode` table
transcribed from the emitter's key; per-rule scope, summed over rules so
`par_bitOps` stays an exact sum). Scale of the old error on the shipping
core: `lnp64mini` `bitOps` is **73 861** hash-consed against **2 162 469**
tree — a 29× over-count. The old tree recursion survives as
`Expr.treeCost`/`Act.treeCost` with `Expr.cost_le_treeCost` proved, and
every tree-builder theorem was renamed onto it rather than deleted.

- **The `priPair` "guard cone" explanation was wrong.** `priPair` emits
  `(.or gl gr, .mux gl vl vr)`, so the left guard appears twice in the
  *term* — but it is one wire, and under the hash-consed cost it costs
  nothing extra. What is actually left is that the balanced form emits
  `n-1` extra width-1 `or` nodes the linear chain never builds, so it is
  dearer by `n-1` bits and by nothing else, **however expensive the guards
  are**. `priTree_cost_gt` still holds (16 < 17 on two atomic guards);
  `sel_cost_dag`/`sel_cost_tree` pin the shift on a 4-way select with a real
  shared guard cone (`+3` new, `+36` old).
- **The sign check, honestly.** A 32-way select with guard
  `(ir[31:26] == i) & ~stall`: under `treeCost` the balanced form is
  **+720 (+17 %)**; under the new cost it is **+31 (+0.7 %)**, i.e. exactly
  `n-1`. So the model no longer calls the balanced priority select
  materially worse — the measured +154 679 bitOps penalty on `s_ex_body`
  (which was itself larger than the whole core's true node weight) collapses
  to a tie. **It does not predict the balanced form cheaper.** The measured
  357-LUT win comes from yosys's own mux-cone optimisation, not from node
  count, and that is precisely `Cost.lean`'s stated honesty boundary: the
  model predicts risk, not P&R outcomes. Treating `priTree` vs `priChain` as
  an area lead was reading synthesis results out of a model that never
  claimed to have them.
- **Renaming now needs injectivity.** `Expr.cost_mapSignals` /
  `Act.cost_mapSignals` are *false* for a merging renaming (merged names
  merge nodes and the cost legitimately drops); `prefixed_cost` is unaffected
  because `prefix_injective` discharges it.
- **`reduceTree_cost_le_foldr` is false under the DAG cost**
  (`reduceTree_cost_not_le_foldr`): a leaf can structurally *be* the chain's
  own suffix, and then the chain's combines are free while the tree still
  builds its own. The `treeCost` version and `cost_le_treeCost` keep it as an
  upper bound; on non-aliasing leaves the tree is still strictly cheaper
  (`orTree_cost_lt_example`).

Still open here:

- per-transform theorems for the rest of the library (`retimeReg`, `connect`,
  the fusion passes);
- **the `familyOf`-invariance hypothesis** that `macroBits`/`softBits` carry:
  true, but a statement about `designTrace`/`syncReadOkB` and proved nowhere;
- target-independent critical-path and DAG-size reports (the cost vector
  is area-shaped; timing is not modelled at all);
- a fit with more designs than weights — the xc7z020 fit is
  **underdetermined** (three weights, two designs, ~1 % residual) and its
  provenance says so;
- **the honest limit found on day one**: the vector does *not* separate
  the lnp64mini design that routed from the one that did not — they differ
  by ~1 % in cells and both land at 52-53 %. At that margin the
  discriminator is congestion, not capacity, so this is a risk signal, not
  a verdict, and `maxFanout` is the dimension most likely to need real
  congestion modelling behind it.

## Current limits of completed capabilities

### Bounded response

`MustReach` includes enabledness so deadlock cannot satisfy a bound vacuously.
Ranking rules and simulation/stuttering transport are available. General
fairness logics, unbounded liveness, nested temporal formulae, and past-time
operators are not.

### Memory targets

Target profiles predict a realization; they do not control synthesis. Only the
XC7 profile has direct tool/silicon validation in this repository. ECP5 and
ASIC profiles contain conservative or explicitly provisional parameters.
Netlist checks remain necessary because actual mapping and initialization
delivery are downstream facts.

Current profile results are produced by:

```console
lake exe memtargets
```

The report, not copied prose, is authoritative for a particular revision.

### Declared observability

`Design.outputs` controls module ports and the compiler/printer theorems prove
an unselected register is not exported. It does not make a value physically
secret: synthesis may constant-fold it, and FPGA configuration/readback can
reveal reset constants or internal state.

### Protocol and priority libraries

The protocol library supplies transition/run/invariant scaffolding; each
engine still proves its event-specific facts. The priority library derives
first-match ordering lemmas from a clause list but does not automatically
derive an independently written outcome function.

### Post-synthesis equivalence

Equivalence is not timing, reset realization, P&R correctness, or bitstream
verification. A reported UNSAT result is meaningful only within the run's
operator, cell, signal, memory, and acknowledgement coverage.

## Deliberately outside Loom's core semantics

- asynchronous or self-timed circuit semantics;
- multiple clock domains inside a single `Design`;
- PLLs, SERDES, DDR PHYs, analog blocks, and bidirectional pads;
- electrical reset, metastability physics, timing constraints, and clock
  gating as semantic constructs; and
- verified place-and-route, configuration generation, or silicon physics.

These enter through target wrappers, contracts, external validation, and
dated hardware evidence. They should not be reintroduced as implicit EDSL
features.

## Adding or closing an entry

Add a gap before introducing a machine-specific workaround. Close it only
when both the generic capability and at least one real consuming artifact are
present, tested, and documented. If repeated campaigns do not need a proposed
abstraction, remove it rather than carrying unused framework complexity.
