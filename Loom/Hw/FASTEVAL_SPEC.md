# Verified fast evaluator

`Loom/Hw/FastEval.lean` and `Loom/Hw/DagEval.lean` accelerate repeated
execution of a well-formed `Design` while retaining a theorem that connects
the executable state to the ordinary hardware semantics.

## Representation

Elaboration resolves names to indices and lowers the design into compact
arrays:

- fixed-width values are masked `Nat` values;
- registers and inputs occupy indexed slots;
- memories use flat storage with per-memory metadata; and
- expressions first become width-erased trees with resolved references; and
- `DagEval` hash-conses those trees into a topologically ordered expression
  DAG, so a shared expression is evaluated once per cycle.

Elaboration is a total Lean function. `fastWFB` is the decidable precondition
for the correspondence theorem; executable entry points reject designs that
do not satisfy it.

The hash-consing builder is not trusted. `DagEval.prepare?` independently
checks node dependencies, every expression root, every action, and the flat
slot count. Only a `DagEval.Verified` value carrying that certificate exposes
the fast DAG cycle operations; malformed lowerings fail closed.

## Correctness

The development supplies abstraction functions between fast and ordinary
states and proves agreement for elaboration, reset, individual cycles, and
runs. Open-design results include the supplied input trace. Machine
`selftest`s use these results rather than treating the evaluator as a second
specification.

`DagEval.VerifiedSimulator` composes two proofs: the checked DAG cycle equals
the `FastEval` tree cycle, and the tree cycle agrees with `Design.cycleOpen`.
Its public closed/open cycle and run operations, including reset-to-run
corollaries, therefore retain the same design-level semantic contract. The
certificate and semantic theorems add no project axiom or `unsafe` execution
boundary.

`Notation.lean` and `Trees.lean` provide typed construction helpers and
balanced expression builders. They improve authoring and generated circuit
shape but do not change the semantic contract.

## Role and boundary

FastEval is the high-throughput executable model used for long traces and
cross-checks. It does not validate emitted Verilog, synthesis, board wrappers,
or external device behavior. Those are separate rungs in the verification
ladder. Performance numbers depend heavily on the design and host, so the
repository treats them as measurements rather than API guarantees.

On the repository's current host, `lake exe lnpsimbench` measures 10,000
LNP64mini cycles at about 0.33 seconds for the 3,373-node certified DAG and
0.18 seconds for the hand ISS (about 1.8×). The older tree evaluator remains
in the benchmark as a regression baseline; LNP64mini lockstep and its
build-time opcode matrix execute through the certified DAG.
S13Soak's long acceptance run and the Epoch and CapWalk acceptance ladders use
the same fail-closed preparation boundary.

`DagEval.stats` exposes exact graph structure independently of execution:
tree occurrences, unique and eliminated nodes, shared-node count, maximum
dependency depth, and maximum logical uses. `lake exe costreport` prints these
as target-independent facts beside the separately calibrated cost estimate.
