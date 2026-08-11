# Changelog

All notable user-visible changes will be recorded here. This project follows
[Semantic Versioning](https://semver.org/) once the first release is tagged.

## Unreleased

### Added

- **Single-source LNP64mini execution and portable board automation:** the
  hand-maintained `MiniIss` cycle mirror, state adapter, mirror-only theorem,
  and emulator-step differential have been removed. Gate, fault, sentinel,
  capability, trace, MMU, and RTL-expectation paths now consume the certified
  Design-derived simulator. ZC702 scripts resolve board roots, tool paths,
  state, artifacts, and the `lnp64` checkout through shared shell/Tcl
  configuration rather than developer-specific home paths.

- **Technology-neutral datapath multiplication and concatenation:** the typed
  expression language now carries same-width modular multiplication through
  reference semantics, proved compilation, optimized and shared-DAG
  evaluation, analysis and transformation passes, concrete SSA certificates,
  and the µVerilog parser/printer. Emission uses plain `*`, leaving DSP or gate
  inference to downstream tools. `Expr.concat` / `++#` provides typed high/low
  concatenation by lowering to the existing proved primitive algebra.
  `Expr.umulWide` and `Expr.smulWide` similarly provide complete unsigned and
  two's-complement products without adding parallel compiler or certificate
  cases. Cost reporting recognizes extension wiring and charges the meaningful
  operand widths rather than the widened result width squared.
  LNP64mini now expresses ordinary low-half `MUL` with the generic operator,
  while deliberately retaining its iterative shift-add engine for the
  high-half `MULH`/`MULHU` operations; its canonical high/low assembly sites
  use the typed concatenation constructor. The direct operator is accepted on
  the current dual-core NetBSD board workload through the reproducible
  stock-openXC7 `-nodsp` path; DSP inference remains a separate target-flow
  optimization rather than a Loom semantic requirement.
- **Generic runner, diagnostics, coverage, and artifact identity:**
  `Loom.Runner` now owns differential step control, bounded and immediately
  flushed events, closed coverage failures, and structured PASS/FAIL/SKIP
  results. Acc8 and LNP64mini use the same facility; Acc8's bespoke runner and
  LNP64mini's legacy comparison/parallel evaluator surfaces were removed.
  `Loom.Artifact` adds exact-byte observation identity and change-only writes,
  while shared shell helpers and SHA-256 manifests provide named command,
  freshness, and external-artifact failures.
- **First proved synthesized-cell paths:** the equivalence checker's complete
  LUT1–LUT6 `evalCell` path—INIT parsing, pin assembly, Shannon expansion, and
  named output—is proved against direct truth-table indexing. Its complete
  legal CARRY4 `evalCell` path, including carry-input selection, staged gates,
  pin assembly, and named outputs, is proved against a direct Boolean
  recurrence. INV, MUXF7/MUXF8, constants, and every accepted buffer family
  are proved too, covering the complete supported combinational `evalCell`
  library. Focused executable proof instantiations include the illegal CARRY4
  hard-error path. FDRE/FDSE/FDCE/FDPE next-state paths are proved through
  parameter validation and legal control handling, with focused rejection
  tests for unsupported inversion parameters and driven asynchronous controls.
  Memo-only state updates are proved CNF-neutral and the executed `evalBits`
  traversal is proved compositional. The `MemoSound` cache invariant has
  proved empty, lookup, insertion, and clause/allocation-framing rules.
  Executed per-port and named-cell-output memo routing is proved CNF-neutral
  and invariant-preserving. A proof-carrying `RefBit` reference records both
  Boolean meaning and literal tied constants, and `RefMemoSound` preserves
  both through empty caches, insertion, framing, memo hits, and executed
  output routing. JSON constants and seed leaves are connected too. The
  executed declared-input traversal is now factored and proved to compose
  per-bit cone encodings into the named pin table without changing evaluation
  order; named lookup is proved to commute with bit denotation. Recursive
  input evaluation plus cell dispatch is now one helper with a generic encoder
  composition theorem, instantiated for buffers, INV, MUXF7/MUXF8, VCC, and
  GND. A uniform LUT bridge substitutes the routed Boolean pins into the
  direct truth table for all six existing arity theorems, with an executable
  LUT1 fixture. A structural variant preserves literal tied constants and
  instantiates both legal CARRY4 input forms, with executable fixtures.
  The exact clock-rejection branch and factored memo-miss driver tail are now
  proved too: recursive input traversal preserves the structural memo, output
  memoization extends it, and the final lookup returns the requested reference
  bit. The complete structural fuel induction now covers every `evalSig`
  branch from explicit seed-agreement and output-reference obligations, with a
  driven VCC fixture. Generic operational frame proofs discharge cell memo
  preservation for all combinational dispatch branches. Uniform discharge of
  the output-reference obligation and the matching CNF recursion remain. Added
  a run-local bidirectional encoder contract that proves constants, seeds,
  sound memo hits, signal-array traversal, declared-input traversal, and the
  bridge into existing cell-family `Enc` theorems without requiring global
  correctness from arbitrary memo tables. The matching full-control-flow
  theorem composes a run-local cell action through output memoization and final
  lookup, with a recursive driven-VCC fixture.
- **Complete non-memory expression encoding proof:** the equivalence checker's
  signed-less-than network and optimized variable barrel shifter have
  kernel-checked semantic proofs, including zero width and large shifts that
  yield zero. Recursive coverage, verdict reporting, and executable proof
  regressions now cover every expression operator accepted by the blaster;
  direct memory reads remain a deliberate cut.
- **Exact evaluator-DAG reports:** `DagEval.stats` reports expression-tree
  occurrences, unique/eliminated DAG nodes, multiply consumed nodes, maximum
  dependency depth, and maximum logical use count. `lake exe costreport` now
  prints these target-independent facts beside the calibrated estimate. The
  LNP64mini core currently reports 458,223 occurrences, 3,373 unique nodes,
  1,063 shared nodes, depth 25, and maximum use count 460; none is presented as
  physical fan-out or timing evidence.
- **Certified DAG simulation:** `DagEval` hash-conses generated expression
  trees, then independently certifies the node dependencies, expression and
  action correspondence, and state layout before exposing executable cycle
  operations. Its theorems compose with `FastEval` through
  `VerifiedSimulator`. LNP64mini lockstep and the build-time ALU matrix now use
  this path. `lake exe lnpsimbench` measures 10,000 cycles at about 0.33 s
  versus 0.18 s for the hand ISS (about 1.8×, inside the 2× replacement
  threshold), with 3,373 unique DAG nodes. The benchmark retains the older
  tree evaluator as a performance baseline and reports preparation separately
  (currently below one millisecond). The complete DAG API now includes run and
  reset-to-run theorems; S13Soak, Epoch, and CapWalk acceptance paths also use
  one fail-closed certified DAG per invocation.
- **Generated external debug maps:** `DebugTap`/`DebugMap` provide a named,
  explicitly unverified escape hatch for ephemeral board probes. One map entry
  generates child output connections, wrapper wires, optional first-event
  capture, two-flop DRCK sampling, core selection, and BSCAN read decoding.
  LNP64mini's trace/loud-latch indices 47–53 now come from one six-tap list;
  its dual wrapper contains only permanent generated-include sites. A
  source-level certificate checks typed outputs and address uniqueness, while
  `lake exe debugmap --check` rejects stale output or ports absent from the
  emitted dual RTL. Raw expressions, CDC, and board observations remain outside
  the release theorem by construction and report. Register-only typed EDSL
  expressions now derive and deduplicate their child dependencies; LNP64mini
  uses a sticky `running ∧ halted` predicate at index 54 as the real integration
  test. Memory-read expressions fail closed until a debug-only internal-memory
  export exists. Sticky taps may also generate persistent per-core halt
  requests; the LNP64mini board routes core 1 through its existing S_F0-safe
  hold path, with behavioral HDL coverage for trigger, persistence, isolation,
  and reset.
- **Verified fan-out duplication:** `duplicateFanout` adds a fresh register
  replica, redirects a selected set of consumer rules, and mirrors every
  producer write. `FanoutCoherent` is proved invariant from reset;
  `duplicateFanout_simulation` gives a reachable-state refinement and
  `duplicateFanout_invariant_pullback` transports source invariants. The typed
  `duplicateFanoutReg` entry point avoids repeating the source width, while
  `duplicateFanoutOkB_sound` turns the executable uniqueness/freshness guard
  into the exact proof witness consumed by the simulation. Positive
  shape/coherence/refinement regressions and collision/ambiguity negative
  controls cover the pass without changing LNP64mini's design or RTL.
  A standalone emitted demo corroborates visible-state agreement and replica
  coherence with Icarus, and reports generic Yosys measurements. Yosys 0.33
  merges the equivalent registers (421 cells and 149 flops in both forms),
  while a checked `keep` profile retains them and lowers measured maximum
  cell-input pin loads from 15 to 9/8 at 482 cells and 172 flops. The report
  explicitly separates the proved structural transform, synthesis tradeoff,
  and still-open post-place timing measurement.
- **Composable refinement chains:** `StutterSimulation` now has identity,
  strict/stuttering mixed composition, and general stuttering composition,
  so timing-insensitive verified transforms can be chained before invariant
  transport. A two-pass `retimeReg` regression composes both proof forms and
  transports source invariants directly to the twice-transformed design.
  `RetimeCut`/`retimePlan` package an ordered set of selected cuts as one pass;
  legality follows every intermediate design and `retimePlan_stutter` returns
  the complete composed refinement and state abstraction.
- **Typed signal handles:** the opt-in notation layer provides `Reg w`,
  `RegArray w n`, and `Mem aw dw`. A memory name, address width, and data width
  are declared once and reused by its declaration, reads, and writes while
  elaborating to the unchanged core EDSL. The immutable `Declarations`
  builder also derives register, memory, input, export, synchronous-read, and
  initialization-policy fields before lowering to an unchanged `Design`. The
  saturating-counter tutorial is migrated with a definitional equality
  regression against its previous core design. Acc8 is the first
  memory-bearing migration; its existing ISS lockstep, refinement, compiler,
  and text-round-trip checks remain unchanged. S13Soak is the first generated
  family migration: its `pend` and `age` registers use `RegArray`, with
  full-depth ISS agreement and byte-identical RTL. S0Blinky and the open
  S0Bscan first-light design now derive registers, memories, inputs, and
  exports from typed handles; frozen interface equalities, S0Bscan lockstep,
  and byte-identical emitted RTL guard the migration. S1Counters derives its
  scalar/generated-family interface from `Declarations`; RetimeDemo derives
  its source and selected cut from typed handles. LNP64mini now derives every
  scalar register, generated register family, memory operation and policy, and
  input from typed handles. Its independently frozen 403-entry migration
  report, scalar-lowering theorem, and fresh-emission gate guard the change.
  The typed migration changed the emitted LNP64mini text, so it is not claimed
  as byte-identical to the pre-migration local artifact.
- **Property-directed cycles:** register and memory projections can discard
  every rule outside their computed write support. Real LNP64mini regressions
  reduce `cur_dom` and `rf` from 21 rules to their single writer funnels; the
  `cycle_support` tactic performs the projection without unfolding unrelated
  logic. Multi-coordinate properties compute one ordered union of writer rules
  with a preservation theorem for every member projection. Typed-handle
  projection lemmas provide a stable simplification surface; the tutorial and
  a two-observation LNP64mini property exercise the result.
  Mixed register/memory `PropertyFootprint` values now produce one executable
  reduced cycle, with a theorem that the full transition agrees on the entire
  footprint and an invariant combinator consuming reset plus reduced-step
  preservation. The tutorial's real `SatOk` invariant and an LNP64mini
  register/RF footprint exercise the complete path.
  Canonical footprint projection now constructs supported properties without
  a manual dependency proof, and declaration validation reports unknown names
  and wrong widths before they can silently produce empty supports.
  Expression-shaped properties now derive their footprints from
  `Expr.readSites`; their support proof, reduced writer cone, and invariant
  combinator require no separately maintained coordinate list.
  `ExprProperty` composes differently typed expression predicates with
  propositional `and`, `or`, and `not`, deriving a combined register/memory
  footprint and support theorem structurally. Tutorial and LNP64mini
  regressions cover a real invariant and a mixed register/memory cone.
  `truth`/`all` now support generated conjunctions; a twelve-input LNP64mini
  closed-design invariant reduces all 21 rules away. A negative regression
  also proves that `running ∧ halted` requires a host-protocol assumption:
  command 13 start-only can produce it after a halt.
  Intra-rule `Act.projectRegs` removes unrelated writes with a selected-
  coordinate equivalence theorem. Explicit `InputAssumption` transition
  systems and an open property-cycle invariant combinator keep host contracts
  visible; the twelve-input LNP64mini property exercises the complete open
  path, and its command contract rejects the counterexample.
  The proved `PairSafety` abstract interpreter closes the remaining projected
  FSM cases, yielding a full-design invariant that excludes simultaneous
  `running`/`halted` exactly when the command contract holds, while retaining
  the unconditional counterexample as a negative control. Both are exported
  from `Machines.Lnp64mini.RunHaltInvariant`; regressions consume that module
  rather than owning a second proof.
  `Machines.Lnp64mini.LifecycleInvariant` extends the property to
  `running`/`halted`/`zeroing`, reduces the 21-rule core to its three actual
  writer rules, and names the additional reset-while-stopped obligation
  required by pre-cycle D9 rule evaluation.
  `Act.projectMems` and `Act.projectFootprint` now project retained actions on
  memory or mixed footprints. `propertyProjectedCycle` composes rule and
  intra-rule reduction with closed/open agreement and invariant combinators.
  An LNP64mini `in_gate`/`tpc` regression reduces `tarr_funnel` from three
  register plus eight memory writes to one of each without changing RTL.
- **Declared memory targets** (Loom D38): `MemTarget` records macro/soft
  memory names, write-port limits, size thresholds, and image-delivery
  behavior. `Design.realizableOnB` checks a design against `xc7`, `ecp5`, or
  `asicSram`; emission enforces the default XC7 profile. XC7 is the exercised
  repository target, while ECP5 and generic ASIC SRAM retain explicit
  provisional/TODO assumptions. `lake exe memtargets` prints the table.
- **Declared observability** (Loom D39): every `Design` has a mandatory
  `outputs : List String` selecting the registers exported as `o_<name>`
  ports. An unknown selection is a hard error at `Design.emit`. The compiler
  and printed-artifact theorems show that an unselected name is not exported.
  This lets the capability engine keep its MAC-key registers off the module
  interface.
- Unbounded, sorry-free LNP64-µ ISS↔EDSL refinement (`RMC.square`,
  `abs_run`, `refines`, and `invariant_transport`) across all 25 opcodes.
- Bounded `cap_revoke` pointer-doubling convergence and synchronized
  retirement proof.
- Machine-enforced executable trust inventory for unsafe helpers,
  `implemented_by`, `partial`, and `extern` declarations.
- External downstream-package smoke test importing `Loom` and `Machines`.

### Changed

- **Typed single-source migration completed:** LNP64mini proof projections now
  derive from checked property footprints, and Epoch/CapWalk memory-policy
  gates and reports enumerate each composed `Design`'s declarations. The
  superseded migration-report, manual-comparator coverage layer, and frozen
  pre-migration declaration snapshots have been removed; the generic typed
  lowering regression remains the compatibility check for the stable core
  EDSL.
- Trust and status documents now distinguish the proved ISS↔EDSL chain from
  executable compiler/printer replacements and the physical µVerilog/SoC
  boundary.

## 0.1.0-dev

Initial development line; no stable release has been tagged.
