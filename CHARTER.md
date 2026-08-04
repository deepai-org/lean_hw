# Loom charter

## Mission

Loom's product is a machine-generic, proof-carrying hardware toolchain in Lean
4. Processor specifications, executable models, hardware designs, proofs, and
generated artifacts should share definitions wherever that prevents drift.
LNP64-µ is the driving verification case; Acc8 is the small end-to-end
pathfinder; the other machines exercise integration, protocols, and hardware
targets.

This charter states direction and governance. It is not a status report and
does not turn roadmap items into current claims. Current facts belong in
[`STATUS.md`](STATUS.md); architecture belongs in [`PLAN.md`](PLAN.md), active
work in [`NEXTSTEPS.md`](NEXTSTEPS.md), and longer-term direction in
[`PLATONIC.md`](PLATONIC.md) and [`LOOM_GAPS.md`](LOOM_GAPS.md).

## Scope

The core scope is:

- transition-system and ISA definitions;
- kernel-checked machine invariants, refinement, and bounded properties;
- a synchronous hardware EDSL and verified compiler;
- a deliberately small structural Verilog boundary;
- certificate-checked decision procedures and independent corroboration;
- artifact generation, exact binding, and documentation projections; and
- explicit integration contracts for memories, ports, CDC, and platform
  components.

The generic `Loom` library must not import `Machines` or `Tools`; the audit
enforces this separation. Machine-specific requirements are allowed to drive
generic features, but the generic abstraction must remain usable by at least
the machines that justify it.

## Current vertical stack

The repository currently contains:

1. generic `TSys`, bounded-property, ISA, and protocol definitions;
2. LNP64-µ T1–T9 proofs and an unbounded ISS-to-EDSL simulation;
3. a hardware EDSL with registers, memories, inputs/outputs, composition,
   synchronous semantics, and target-memory diagnostics;
4. a verified compiler to a µVerilog AST and a structural SSA renderer;
5. exact concrete-SSA release certificates for Acc8 and LNP64-µ;
6. BMC/k-induction and LRAT checking, plus an independent unproved LRAT
   checker used for cross-validation;
7. optional post-synthesis equivalence checks over a reported fragment; and
8. book generation and FPGA integration evidence.

The repository does **not** contain an independent checker for Lean kernel
exports, a verified place-and-route or bitstream flow, or a proof of arbitrary
Verilog/Yosys semantics. Those remain possible future assurance work, not
present capabilities.

## The LNP64-µ theorem ladder

The authoritative statements are the declarations imported by
`Machines/Lnp64u/Theorems/Ledger.lean`:

- **T1 — encoding and convention soundness:** encoding layout, opcode
  distinctness, decode/encode facts, legal-opcode coverage/refusal, operand
  preservation, and convention checks.
- **T2 — authority confinement:** reachable authority remains below manifest
  roots under the modeled derivation and transfer operations.
- **T3 — temporal safety:** generation monotonicity, no resurrection, and
  revoke-related safety properties in the modeled machine.
- **T4 — integrity/frame:** activation scrub, caller restoration, and the
  named inter-domain influence channels.
- **T5 — architectural noninterference:** equality of destuttered observations
  for domains satisfying the theorem's isolation, agreement, and priority
  hypotheses. Timing channels are intentionally erased.
- **T6 — totality/no-hostage:** closed outcomes and bounded caller resumption
  under strict schedulability and the theorem's other hypotheses.
- **T7 — real time:** retirement cost, budget-delivery, and scheduling bounds
  under explicit schedulability premises.
- **T8 — ownership-transfer memory safety:** machine-wide W^X and modeled
  grant/revoke/regrant and status-word properties.
- **T9 — conservation:** lineage-ledger balance and budget upper bounds.

These are mathematical statements about the defined model. Their hypotheses
and exclusions must not be shortened into unconditional product claims. The
release theorem transports named invariant consequences onto the compiled
LNP64-µ transition system; it does not bundle every T1–T9 declaration as a
field.

## Trust doctrine

- Prefer kernel-checked proof terms and certificates. `native_decide` and the
  trusted Lean compiler are forbidden on theorem paths.
- Generic proof libraries such as Mathlib are acceptable because their proof
  terms are checked by the same kernel. Computational solvers remain
  untrusted unless their results are certified and checked.
- Keep the emitted-language assumption small, public, and
  construct-by-construct. Do not imply that synthesis or silicon follows from
  a theorem about formal bytes.
- Treat external-tool equivalence, simulation, and hardware measurements as
  valuable corroboration with named exclusions, never as retroactive proof.
- Add target-specific memory, CDC, and physical assumptions through explicit
  contracts rather than silently strengthening the EDSL semantics.

The authoritative release TCB is [`TCB.md`](TCB.md).

## Governance rules

1. **No hidden trust expansion.** Changes to axioms, unsafe code,
   `implemented_by`, certificate checkers, binders, parsers, or external-tool
   assumptions require an explicit audit and documentation update.
2. **Proof-driven infrastructure.** A generic feature should discharge a
   concrete machine, release, portability, or verification obligation.
3. **Machine/tool separation.** `Loom` stays machine-generic; machine imports
   flow outward only.
4. **Counterexamples are design results.** When a theorem is false, preserve
   the counterexample and repair either the model or the statement visibly.
5. **One owner per fact.** Current state lives in `STATUS.md`, reproduction in
   `REPRODUCING.md`, the release trust list in `TCB.md`, and limitation
   analysis in `TRUST.md`; other documents link instead of copying snapshots.
6. **Hardware evidence is dated.** Record the commit, tool versions, target,
   wrapper assumptions, and whether the current head still reproduces it.
7. **Portability is checked, not inferred from syntax.** Memory and resource
   requirements are stated against declared targets, and downstream mapping
   is still checked or corroborated separately.

## Long-term direction

The intended ladder extends beyond the µ demonstrator toward MMU/TLB and
multi-core memory-ordering proofs, richer exception and IPC machinery,
additional FPGA targets, and an ASIC flow. Each rung should extend the existing
definitions and proof boundaries without claiming that future work is already
part of the current artifact.
