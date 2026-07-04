# TRUST — an honest bird's-eye audit of what the LNP64-µ theorems rest on

Audited 2026-07-04, against the bar: peer-review-grade, seL4-trustworthiness
or better. This document is deliberately adversarial to the project's own
claims; it is the seed of the paper's trust section. Facts verified against
the repo at the audit date.

## A. Is it the right question? (property adequacy)

- **Timing channels are out of scope by construction.** T5's observation is
  the projection (regs, pc, run, cause) and trajectories are destuttered —
  *when* things happen is erased before comparison. Honest (budget provably
  drifts between runs), but T5 says nothing about covert timing channels.
  Same exclusion as seL4; a timing-quantified T5′ is future work.
- **The logic model is 2-state unless stated otherwise.** Lean, the EDSL,
  and the µVerilog semantics reason over `BitVec` values: every bit is 0 or
  1. Verilog simulation/synthesis has 4-state hazards (`X`/`Z`) and
  X-optimism/X-pessimism mismatches. Since 2026-07-04, CI re-emits Acc8 and
  LNP64-µ and runs `scripts/check_xfree_rtl.py` over the exact core RTL,
  rejecting X/Z/don't-care literals or constructs, missing register resets,
  and partial memory initialization. Residual risk: this is a text-level
  lint gate, not yet a Lean theorem tying the parser/AST to 2-state-safe
  generated text or proving every synthesis don't-care optimization
  impossible.
- **Reset is a mathematical initial-state assumption.** The proofs start
  from `Manifest.initState` / `Module.reset`: a perfectly clean state in
  which every proof-visible register, memory cell, pipeline latch, and hidden
  control bit has the intended value. The current trust story does not prove
  that a physical reset controller, asynchronous reset network, clock/PLL
  sequencing, scan state, or synthesis-inserted state actually realizes that
  state without glitches or metastability. Hardware claim shape: "from the
  modeled reset state," not "from every electrical power-on behavior."
- **The theorems are conditional on configuration.** T5 holds for domains
  configured `Isolated` (+`TopPriority`); T6 needs `StrictlySchedulable` +
  positive budgets. These conditions are proof-forced (the unconditioned
  statements are FALSE, with machine-checked counterexamples). Claim shape:
  "isolation holds for domains configured thus," never "the machine
  provides isolation."
- **The CPU is modeled as a closed machine, not a hostile SoC.** T5 assumes
  all architecturally relevant state changes come from the verified machine.
  External DMA, AXI/AHB fabric behavior, MMU/IOMMU translation, memory-mapped
  peripherals, timers, debug ports, and asynchronous interrupts are not in
  the model. If an unverified peripheral can mutate RAM, inject faults, or
  assert interrupts with adversarial timing, it is outside T5 unless it is
  either ruled out by integration policy or brought into the manifest/spec and
  proved compatible with `Isolated`.
- **D11 fixed the residual-budget stall-lock.** Underfunded serving issue
  now raises a deterministic `.budget` fault and unwinds the caller;
  underfunded non-serving issue burns the payer's residual budget to zero.
  `T6.no_hostage` no longer carries the former semantic `StallFree` side
  condition. The remaining progress caveat is environmental, not this
  scheduler bug.
- **Progress is not global liveness.** T6 is the only serious progress-shaped
  result, and after D11 it is a closed-machine scheduler/retirement theorem
  unless the model also
  accounts for external memory backpressure, instruction-fetch stalls,
  interrupt storms, exception loops, clock gating, and reset reassertion.
  "Useful user instructions eventually retire under arbitrary platform
  conditions" is not a current theorem.
- **Budget accounting is only as strong as the event model.** The spec
  charges instruction classes at issue and proves accounting over that
  closed machine. Real integrations must say who pays for interrupt entry,
  pipeline flushes, exception routing, memory stalls, and context-switch
  overhead. If an external event can drain another domain's budget, the
  scheduler becomes a denial-of-service channel even if T5's safety property
  still holds.
- **Fault routing must remain deterministic and local.** T1/T6 cover decode
  refusal and fatal domain halt in the ISS. The hardware-level claim still
  depends on every RTL/SoC fault source matching that deterministic behavior:
  illegal opcodes, malformed instruction words, memory-authority faults,
  double faults, unaligned/unsupported accesses, debug traps, and interrupt
  exceptions must not enter undefined or globally visible behavior.
- **Vacuity risk, partially addressed:** `Tests.Lnp64uWitnesses` now gives
  kernel-checked witnesses for finite manifest-side premise families:
  `Manifest.WF`, `RMC.Fits`, T7 schedulability on the base lockstep
  manifest, plus a concrete isolated manifest satisfying T5's `Isolated ∧
  TopPriority ∧ AgreeOn` and T6's `StrictlySchedulable ∧ positive budgets`.
  Since D11 deleted the semantic `StallFree` premise, the T6 witness now
  covers the remaining finite manifest-side hypotheses.

## B. Did we state the theorems properly?

- The statements were *falsified into shape*: eight-plus proof-forced
  repairs, each with a recorded counterexample (narrow wraparound, Q=P hog,
  retired-vs-dead, gate-class handles, cycle-wrap uninhabitedness, …).
  Strongest evidence in the repo that the statements mean something.
- Residual risk is **hypothesis creep** — every repair strengthened
  hypotheses, and strengthening is how vacuous theorems happen. Witness
  manifests are the antidote.
- The load-bearing definitions (`Wf`, `Isolated`, `Obs`, `resumeBound`)
  have had zero external readers. External statement review is not
  optional for the target bar.

## C. Does the proof stack have bugs? (Lean-side TCB, best to worst)

1. **Lean 4 kernel + 3 standard axioms** — shared with Mathlib.
2. **The µVerilog tool-boundary assumption** — one assumption exposed as
   two whitelisted axiom declarations: `ImplementsStandard` and
   `implements_standard_spec`. Its scope is now documented as concrete
   reset/cycle agreement for a concrete emitted module and tool realization,
   not a claim about full Verilog or physical implementation effects.
3. **`Tools/Audit.lean` is a trusted ~100-line compiled tool.** It computes
   real axiom closures (and caught the T5 `system_preserves` near-miss).
   Since 2026-07-04, `lake exe audit` prints each ledger theorem's axiom
   closure, so readers can inspect the raw closure behind each CLEAN/STATED
   verdict instead of trusting only the summary labels.
4. `decide` = kernel reduction (fine); `native_decide` banned repo-wide.
5. Superseded `SystemOpsWf` sorries — deleted 2026-07-04; remaining
   `sorry` hits are the audit-legal R-MC statements under `Theorems`.

## D. Does the generated Verilog comply with the proofs? (the chain)

| Link | Status (2026-07-04) |
|---|---|
| ISS (`machine m`) — where T1–T9 live | proved |
| ISS ↔ EDSL core (R-MC) | **TESTED, not proved** (1 sorry: `square`; 2,256 directed full-state lockstep cycles) |
| EDSL core → Module IR (`compile`) | proved generically, sorry-free |
| Module → *executed* emission | **`@[implemented_by compileImpl]` — unproved replacement** |
| Module ↔ emitted text | round-trip `#guard` = **compiled eval, NOT kernel** (Acc8); **lnp64u: none yet** |
| text → simulator/synthesizer | µVerilog boundary assumption + iverilog/yosys corroboration; CI X-free/reset/init lint over freshly emitted Acc8 + LNP64-µ RTL |
| verified CPU netlist → SoC fabric / board | out of scope (DMA, interrupts, bus arbitration/backpressure, debug, MMU/IOMMU, coherency) |
| netlist → silicon → physics | out of scope (reset sequencing, timing closure, glitches, metastability, power side channels) |

- **Finding 1 — R-MC gap.** Today "T1–T9 hold of the RTL" is a
  proved-tested-proved sandwich; the honest phrasing until `square` closes
  is "proved of the ISS; correspondence to RTL mechanically tested and
  partially proved."
- **Finding 2 — `implemented_by` (Compile.lean:386) enlarged the TCB.**
  The kernel reasons about the reference `compile`; every executed
  artifact (emitted `.v`, BMC CNF) comes from the unproved `compileImpl`.
  Divergence = proving theorems about one circuit and shipping another.
- **Finding 3 — the round-trip net has eval-level mesh.** Acc8's
  `#guard acc8Module.parseCheck` runs in the compiled evaluator (the
  kernel `decide +kernel` variant measured >4 min / >40 GB via String's
  quadratic kernel model; only a small demo module is kernel-checked).
  So the net meant to catch Finding 2 itself trusts the Lean compiler.
  Findings 2+3 compound. Fixes: prove `compileImpl = compile` (bounded:
  memoization + pruning) or gate-compare reference output; land lnp64u
  `parseCheck`; make one full-size round-trip genuinely kernel-checked.
- **Finding 4 — reset realization is below the proof boundary.** The R-MC
  reset obligations can show that the EDSL reset state abstracts to
  `Manifest.initState`; they do not show that an electrical or SoC-level
  reset sequence reaches that state on real hardware. Integration needs a
  reset contract: all proof-visible state initialized, no unmodeled retained
  state, reset held through clock stabilization, and no partially-reset
  bus/peripheral interaction.
- **Finding 5 — platform I/O can bypass the theorem.** The core's memory is
  modeled internally. A real platform must either forbid external writers to
  protected memory or verify the bus/IOMMU/peripheral policy. Otherwise DMA,
  debug, interrupts, or memory backpressure can break isolation/progress
  without contradicting any current Lean theorem.
- **Finding 6 — 2-state proofs need an X-free RTL contract.** A synthesized
  netlist can choose concrete values for Verilog `X`/don't-care behavior
  that a simulator treats differently. The new `check_xfree_rtl.py` CI gate
  rejects the main emitted text hazards (X/Z/don't-care literals or
  constructs, un-reset registers, partially initialized memories). What
  remains is the formal adequacy upgrade: prove or parser-check that every
  emitted µVerilog artifact stays inside this 2-state-safe subset, including
  no undefined array-read behavior under the synthesis interpretation.
- **Finding 7 — physical event accounting is not specified.** The scheduler's
  budget proofs count modeled issue/retire behavior. Platform events such as
  interrupt delivery, exception flushes, wait states, and debug traps need an
  integration contract saying whether they are impossible, charged locally,
  or modeled and proved.

## E. Conceptual traps

- **Avoided (advertise it):** noninterference is a hyperproperty and is
  NOT preserved by refinement — a correct simulation theorem can transport
  nothing about T5. Loom dodges this structurally: R-MC's `abs_run` is
  functional whole-state *equality* (deterministic exact lockstep, enabled
  by T6.totality), and equality transports hyperproperties.
- **Open: the spec is single-source.** ISA book, conformance suite, and
  ISS are projections of one declaration set — no divergence, but no
  independence. Adequacy evidence = executability + the falsification
  history. The only fix is external eyes.
- **Open: initial-state adequacy.** Reset theorems over `Module.reset` are
  not reset-controller theorems. A power-on or warm-reset path that leaves
  one hidden flop, pipeline latch, SRAM, debug CSR, or bus bridge in a
  non-model state starts execution outside the reachable-state set used by
  T1–T9.
- **Open: closed-world adequacy.** The theorems intentionally reason about
  the verified machine, not the entire chip. The paper must say whether the
  deployment target has no DMA/interrupt/MMU/peripheral nondeterminism, or
  which external components are trusted to preserve the machine's assumptions.
- **Open: liveness adequacy.** Safety survives stuttering; useful progress
  does not. After D11 removed `StallFree`, the remaining question is whether
  the environment can indefinitely prevent retirement by withholding memory,
  flooding interrupts, or repeatedly resetting/gating the core.
- **Open: fault adequacy.** Deterministic `abs_run` transport assumes every
  low-level fault is either modeled or impossible. Undocumented opcodes,
  exception-priority ties, debug entry, bus errors, and double-fault-like
  cases must not produce behavior outside the ISS transition relation.

## F. Verdict vs the seL4 bar

- **Ahead in shape:** verification extends below the ISA into the RTL;
  a completed chain trusts the Lean kernel plus one narrowly documented
  µVerilog tool-boundary assumption — smaller and cleaner than seL4's TCB
  statement.
- **Behind today:** (1) R-MC gap ⇒ end-to-end guarantee currently
  comparable to seL4, not better; (2) `implemented_by` + eval-level
  guards are unproved TCB residue; (3) reset, X-free RTL, platform I/O,
  budget-event accounting, fault
  routing, and global progress are integration assumptions, not proved
  properties; (5) zero external scrutiny of spec and statements — most of
  what "seL4-trustworthy" socially means.

## Ranked punch list

1. Close R-MC `square` (NEXTSTEPS §1/§4 fork).
2. DONE 2026-07-04: D11 scheduler fix landed; serving underfunding raises
   a `.budget` fault, non-serving underfunding burns residual budget, and
   `StallFree` is deleted from T6.
3. ● Prove or gate-check `compileImpl = compile`; land lnp64u
   `parseCheck`; one full-size kernel-checked round-trip.
4. DONE 2026-07-04: `Tests.Lnp64uWitnesses` gives kernel-checked witnesses
   for finite manifest-side hypotheses, and D11 deleted T6's semantic
   `StallFree` side condition.
5. Specify the reset contract needed to enter `Manifest.initState` /
   `Module.reset`, including clock/reset sequencing and proof-visible hidden
   state; decide whether it is a trusted integration assumption or a future
   checked artifact.
6. PARTIAL 2026-07-04: `scripts/check_xfree_rtl.py` runs in CI after fresh
   Acc8 + LNP64-µ emission and rejects X/Z/don't-care literals or
   constructs, missing register resets, and partial memory initialization.
   Remaining: promote this from text-level lint to a Lean parser/AST
   2-state-safety theorem, and cover synthesis undefined-read/don't-care
   adequacy explicitly.
7. Specify the SoC boundary: DMA/interrupt/MMU/peripheral/debug behavior,
   memory backpressure, and which pieces are trusted vs. modeled/proved.
8. Specify budget-event accounting for interrupts, exceptions, flushes,
   stalls, debug entry, and other non-retirement cycles.
9. Specify and test/prove deterministic fault routing for every hardware
   fault source, including illegal/unsupported opcodes and bus/debug faults.
10. After D11, state the remaining closed-world progress theorem precisely
   and separate it from unproved platform-wide liveness.
11. DONE 2026-07-04: axiom-closure printing landed in `lake exe audit`,
   and the `ImplementsStandard` wording was narrowed to concrete µVerilog
   reset/cycle agreement for one emitted module and tool realization.
12. DONE 2026-07-04: deleted superseded `SystemOpsWf` sorries and scrubbed
   stale "kernel-checked" claims that were actually eval-checked.
13. External statement review — the one item no code closes.
