import Machines.Lnp64u.Logic.Hostage
import Machines.Lnp64u.Theorems.T7

/-!
# T6 — Totality and no-hostage

The outcome set is closed — {retire, `-errno`, domain-halt} — and a blocked
gate caller resumes within a manifest-computable bound, quantified over all
callees *including adversarial ones*: the donation bound plus forced unwind
(the design change this theorem forced, 2026-07-03) makes the statement one
only a proof can make.

## Proof-forced statement change (2026-07-03): the starvation refutation

The original statement (no schedulability hypothesis;
`resumeBound = (maxDonation+1)·maxChainDepth·P_d + 2·P_d`) is **false**.
The bound contained no interference term, and `Manifest.WF.budget_le` is
`Q ≤ P`, which admits a domain that is *always* eligible. Concrete
counterexample (3 live domains; `numDomains = 4`, the fourth boots into
`halt`):

* **H** (hog): priority 3 (top), `budgetQ = periodP = 6`. Program: one
  `yield` (cost `.sched = 1`), then an infinite loop of ALU ops
  (cost `.alu = 2`). Code capability boot-mapped executable, so fetch
  always succeeds.
* **D** (caller): priority 2, large `budgetQ = periodP` (say 64/64).
  Program: `gate_call` through a boot gate capability for gate `g`.
* **C** (callee of `g`): priority 1, any budget. Its program is irrelevant
  — it never executes an instruction.

Timeline against the actual `Step` semantics: at cycle 0 the scheduler
picks H (top priority, boot budget 6 > 0); H issues `yield`, which retires
at cycle 1 setting H's budget to 0. At cycle 2, H is ineligible, so D
issues `gate_call` (cost `.gate = 8`, charged upfront); it retires at
cycle 10: D becomes `.blocked g`, C serves `g` with
`donated = D.maxDonation`. Meanwhile H refilled to 6 at cycle 6
(`refillPhase`: `6 % 6 = 0`). From cycle 11 on, every idle-core cycle has
H eligible — `run = .running` and `payer H = H` (H serves nothing) with
`budget > 0` — and H has top priority, so `schedule` never picks C
(`schedule_priority_le`/`prio_inj`). H's budget never reaches 0: an ALU
issue charges 2 and occupies the core 3 cycles (issue + 1 burn + retire),
so H spends at most `2·⌈6/3⌉ = 4 < 6` per period window and is topped
back to 6 at every boundary; the `cycle = 0` no-refill case is covered by
the boot budget. C therefore never reaches the core, so none of the three
unblock mechanisms — `gate_return` retiring, C halting/faulting
(`haltDom` unwind), or donation exhaustion at C's issue — can ever fire;
`refillPhase` and `moverPhase` never touch `run`. D stays `.blocked g`
at every cycle ≥ 11, past any finite bound. ∎

The repair (the charter's anticipated class, T2/T8 precedent): add the
*strict* schedulability hypothesis `StrictlySchedulable` — strict, so
every hyperperiod contains at least one cycle's worth of slack that the
serving chain (which pays from the blocked caller's budget) can use —
and give `resumeBound` an interference term in the hyperperiod.
-/

namespace Machines.Lnp64u.Theorems.T6

open Machines.Lnp64u Loom

/-- **Totality.** The machine is deterministic and total: every state has
exactly one successor. (By construction — `step` is a Lean function — but
stated because the claim is about the *machine*, not the formalization:
there is no state, adversarial or otherwise, without a defined next
cycle.) -/
theorem totality (m : Manifest) (σ : MachineState) :
    ∃! σ', (machine m).step σ σ' :=
  ⟨step m σ, rfl, fun _ h => h.symm⟩

/-- **Strict schedulability** (T6's hypothesis, proof-forced 2026-07-03):
over the hyperperiod `L = hyperL m`, the summed budget demand is *strictly*
below `L` — `Σ_d Q_d · (L / P_d) < L`. Strictness guarantees that other
domains cannot buy every cycle of a hyperperiod, so a funded, top-eligible
serving chain is issued at least once per interference window. Compare
`T7.Schedulable`, which is the non-strict `≤` (enough for budget delivery,
not for liveness — the `≤`-boundary case is exactly the starvation
counterexample in this file's header). -/
def StrictlySchedulable (m : Manifest) : Prop :=
  ((List.finRange numDomains).map
    (fun d => (m.doms d).budgetQ * (hyperL m / (m.doms d).periodP))).sum < hyperL m

/-- Strict schedulability implies T7's (non-strict) schedulability: the two
theorems share one premise family. -/
theorem strictlySchedulable_schedulable (m : Manifest)
    (h : StrictlySchedulable m) : T7.Schedulable m :=
  Nat.le_of_lt h

/-- The caller-side resume bound, repaired (2026-07-03; see the header
refutation for WHY the original per-period bound was false):

* `(maxDonationBound m + 2) · maxChainDepth` — the progress measure: the
  serving chain above the caller has at most `maxChainDepth` live
  activations; each contributes at most `maxDonationBound m` donation
  decrements (every issue charges ≥ 1) plus an unwind/return step plus one
  in-flight drain. `maxDonationBound` is the machine-wide ceiling, not
  `(m.doms d).maxDonation`: deeper activations are donated from *their*
  callers' bounds, not from `d`'s.
* `(2 · hyperL m + 2)` — the interference window per progress step: under
  `StrictlySchedulable`, other domains can charge strictly less than
  `hyperL m` budget per hyperperiod, and an issue of cost `c` occupies the
  core at most `c + 1 ≤ 2c` cycles, so within `2 · hyperL m + 2` cycles of
  any instant the core has an idle cycle with every foreign budget spent —
  where the chain head is the top-priority eligible domain and issues
  (`schedule_eq_of_top`), stalls only if its own chain spent the budget
  (progress), or unwinds.
* `+ 2 · hyperL m` — slack for the initial partial period/hyperperiod
  alignment and the final Mover/retire drain.

Coarse and manifest-computable — tightened per target (and per domain,
restoring a `d`-dependence through the chain depth *above* `d`) as T6′ in
Phase 3. -/
def resumeBound (m : Manifest) (_d : DomainId) : Nat :=
  (maxDonationBound m + 2) * maxChainDepth * (2 * hyperL m + 2) +
    2 * hyperL m

/-- **No-hostage.** Under strict schedulability, a domain blocked on a gate
call resumes (or halts) within `resumeBound` cycles, whatever the callee
does: return, fault, halt, loop (donation exhaustion unwinds it), or call
deeper (depth ≤ 4, each level donation-bounded).

The hypothesis `hsched` is proof-forced (2026-07-03): without it the
statement is false — see the starvation counterexample in this file's
header. Remaining assembly (the per-cycle ingredients are proved in
`Logic/Hostage.lean`):

1. the well-founded progress measure on the chain state above `d`
   (live activations, top activation's `donated`, in-flight `cyclesLeft`),
   decreased by `corePhase_issue_serving` / `haltDom_caller_running`;
2. the budget-accounting bound on no-progress cycles per hyperperiod
   (issues charge payer budgets upfront, `refillPhase` restores only at
   period boundaries — `periodP_dvd_hyperL`), giving the
   `2 · hyperL m + 2` window via `StrictlySchedulable`;
3. the stall analysis: a stall with the chain head top-eligible means the
   chain itself spent the payer budget since the last refill
   (`corePhase_stall` + `schedule_eq_of_top`), which is prior progress. -/
theorem no_hostage (m : Manifest) (hwf : m.WF) (hsched : StrictlySchedulable m)
    (σ : MachineState) (hreach : (machine m).Reachable σ)
    (d : DomainId) (g : GateId) (hblocked : (σ.doms d).run = .blocked g) :
    ∃ n ≤ resumeBound m d, ((stepN m n σ).doms d).run ≠ .blocked g := by
  sorry

end Machines.Lnp64u.Theorems.T6
