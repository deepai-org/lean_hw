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

`MemTarget` checks a limited realizability predicate; it is not an area,
timing, banking, power, or placement model. Loom still lacks:

- target-independent critical-path and DAG-size reports;
- target profiles with calibrated operator weights and error bars;
- duplication/congestion indicators; and
- proved cost bounds for transformation-library components.

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
