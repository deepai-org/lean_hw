# Verified fast evaluator

`Loom/Hw/FastEval.lean` accelerates repeated execution of a well-formed
`Design` while retaining a theorem that connects the fast state to the
ordinary hardware semantics.

## Representation

Elaboration resolves names to indices and lowers the design into compact
arrays:

- fixed-width values are masked `Nat` values;
- registers and inputs occupy indexed slots;
- memories use flat storage with per-memory metadata; and
- expressions become width-erased trees with resolved references.

Elaboration is a total Lean function. `fastWFB` is the decidable precondition
for the correspondence theorem; executable entry points reject designs that
do not satisfy it.

## Correctness

The development supplies abstraction functions between fast and ordinary
states and proves agreement for elaboration, reset, individual cycles, and
runs. Open-design results include the supplied input trace. Machine
`selftest`s use these results rather than treating the evaluator as a second
specification.

`Notation.lean` and `Trees.lean` provide typed construction helpers and
balanced expression builders. They improve authoring and generated circuit
shape but do not change the semantic contract.

## Role and boundary

FastEval is the high-throughput executable model used for long traces and
cross-checks. It does not validate emitted Verilog, synthesis, board wrappers,
or external device behavior. Those are separate rungs in the verification
ladder. Performance numbers depend heavily on the design and host, so the
repository treats them as measurements rather than API guarantees.
