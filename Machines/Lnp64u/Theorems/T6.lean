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

The first repair added the *strict* schedulability hypothesis (charge
form): `Σ_e Q_e·(L/P_e) < L` over the hyperperiod `L`. Attempting the
assembly refuted the repaired statement **twice more** (2026-07-03,
same session):

## Second refutation: the occupancy hog (charge-strictness is too weak)

An issue of cost `c` occupies the core for `c + 1` cycles (the issue
cycle latches `cyclesLeft = c`; the countdown burns `c - 1` cycles; the
retirement consumes one more) but charges only `c`. Budget accounting
therefore bounds *charges*, not *core occupancy*, and the two differ by a
factor of up to `(c+1)/c`. Concrete counterexample against
`Σ Q·(L/P) < L`: reuse the layout above but give **H** `budgetQ = 4`,
`periodP = 6`, and the ALU loop after the boot `yield`. After D blocks
(cycle 10 as before), H issues an ALU op the moment the core frees
(cycle 11: charge 2, occupy 11–13; cycle 14: charge 2, budget 0, occupy
14–16), idles 17, refills at 18 — and from cycle 18 the pattern
`issue/burn/retire · issue/burn/retire` tiles each 6-cycle period of H
*exactly*: 2 issues charge 4 = Q and occupy all 6 cycles. The core is
never idle again, C never runs, D is a hostage — yet
`Σ Q·(L/P) = 4·(192/6) + 8·3 + 1·3 + 1·3 = 158 < 192 = L`. (The fourth
domain, priority 0, gets the single idle cycle 17 and halts.) ∎

The repair: `StrictlySchedulable` now carries the occupancy factor 2
(`c + 1 ≤ 2c` for every cost `c ≥ 1`, `cost_pos`): `2·Σ Q·(L/P) < L`.

## Third refutation: the residual-budget stall-lock (priority inversion)

`corePhase`'s issue path *stalls the core* when the scheduled domain's
payer has positive budget below the fetched instruction's cost
(`corePhase_stall`: `corePhase m σ = σ`, no budget moves). A stall cycle
spends nothing, so **no budget hypothesis can count it**, and the
scheduler re-picks the same domain every cycle. Concrete counterexample
(satisfies `Manifest.WF`, the 2× `StrictlySchedulable`, and positive
budgets): **H** priority 3, `budgetQ = 1`, `periodP = 6`, program
`yield; alu; …`. As above, H's `yield` retires at cycle 1 (budget 0), D
blocks at cycle 10, H refilled to 1 at cycle 6. From cycle 11 on H is
top-priority eligible (budget 1 > 0) at every cycle, fetch and decode of
the ALU op succeed, and `cost = 2 > 1 = budget`: the core stalls,
*forever* — refills restore exactly 1, D's refill at 64 makes C eligible
but never scheduled. `2·Σ Q·(L/P) = 2·(1·32 + 8·3 + 1·3 + 1·3) = 124 <
192`. D is a hostage. ∎

No manifest-computable hypothesis can exclude this: the stalling residual
is produced by the *program* (adversarial ROM mixing cost-1 and cost-2+
instructions), and budgets evolve by arbitrary cost multisets, so any
`0 < budget < cost` state is reachable for some program. The honest
statement therefore carries the semantic side condition `StallFree` — no
reachable cycle stalls. (The hardware fix is a scheduler change — skip or
budget-burn on an underfunded pick — which belongs to a later µ revision;
`Step.lean` is frozen for this phase. Sane manifests discharge
`StallFree` per system by cost-aligning each program's issue sequence
with its budget.)
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

/-- **Strict schedulability** (T6's hypothesis; proof-forced 2026-07-03,
occupancy factor added by the second refutation): over the hyperperiod
`L = hyperL m`, twice the summed budget demand is strictly below `L` —
`2·Σ_e Q_e·(L/P_e) < L`. The factor 2 converts charges to core occupancy
(an issue of cost `c` occupies `c + 1 ≤ 2c` cycles but charges only `c`);
strictness guarantees the leftover cycle in which the funded, top-eligible
serving chain is issued. Compare `T7.Schedulable`, the non-strict,
factor-free `Σ Q·(L/P) ≤ L` (enough for budget delivery, not liveness). -/
def StrictlySchedulable (m : Manifest) : Prop :=
  2 * ((List.finRange numDomains).map
    (fun d => (m.doms d).budgetQ * (hyperL m / (m.doms d).periodP))).sum < hyperL m

/-- Strict schedulability implies T7's (non-strict) schedulability: the two
theorems share one premise family. -/
theorem strictlySchedulable_schedulable (m : Manifest)
    (h : StrictlySchedulable m) : T7.Schedulable m := by
  unfold StrictlySchedulable at h
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.two_mul _ ▸ h))

/-- **Stall-freedom** (T6's semantic side condition; proof-forced
2026-07-03 by the stall-lock refutation in this file's header): no
reachable cycle stalls the core. A stall (`StallsAt`: scheduled, fetched,
decoded, payer budget positive but below cost) freezes the machine state
while spending nothing, so it can repeat forever and no budget-counting
hypothesis excludes it. Stated on `refillPhase m σ` because that is the
state `corePhase` runs in within `step`. Not manifest-computable —
discharged per system by cost-aligning each program's issue sequence with
its budgets (e.g. every domain only issues instructions of one cost `c`
with `c ∣ Q`); the µ-successor hardware fix is a scheduler that skips or
burns an underfunded pick. -/
def StallFree (m : Manifest) : Prop :=
  ∀ σ, (machine m).Reachable σ → ¬ StallsAt m (refillPhase m σ)

/-- The per-progress-step interference window (see `resumeBound`): the
number of cycles within which, under `StrictlySchedulable` + `StallFree`
+ positive budgets, the serving chain above a blocked caller must have
been issued (or unwound) at least once. Derived from the potential
`Ψ = 2·massExcept σ origin + inflight-remaining + #non-halted`: every
non-progress cycle decreases `Ψ` by ≥ 1 (issue: `corePhase_cases` charge
equation + `cost_pos`; burn/retire: countdown; fault-halt: the halted
count; idle with the origin funded: impossible, the chain head is
eligible and `schedule_isSome_of_eligible` fires; stall: excluded), while
refills refund at most `2·Q_e` per boundary — `2·Σ Q·(L/P) ≤ L - 1` per
hyperperiod (`StrictlySchedulable`) plus one partial hyperperiod at each
window edge. Solving `n ≤ Ψ₀ + (n/L + 1)·(L-1) + 2·budgetMass` with
`Ψ₀ ≤ 2·budgetMass + maxCostBound + numDomains` gives
`n ≤ L·(4·budgetMass + L + maxCostBound + numDomains + 2)`, plus one
period (≤ `L`) of origin-refill wait folded in by the caller. Coarse and
manifest-computable. -/
def interferenceWindow (m : Manifest) : Nat :=
  hyperL m * (4 * budgetMass m + hyperL m + maxCostBound + numDomains + 2)

/-- The caller-side resume bound, repaired twice (2026-07-03; see the
header refutations for WHY each predecessor was false):

* `(maxDonationBound m + 2) ^ maxChainDepth` — the progress measure: the
  serving chain above the caller is a path of ≤ `maxChainDepth` live
  activations; the vector of their `donated` fields (⊥ for absent levels)
  lives in `{0, …, maxDonationBound+1}^maxChainDepth` and every chain
  progress event (chain-head issue, deeper `gate_call`, `gate_return`
  pop, forced unwind) strictly decreases it *lexicographically* — deeper
  levels refresh to a full `maxDonation` when an earlier level pays the
  gate cost, so the event count is the lex order type `(M+2)^depth`, not
  `(M+2)·depth` (the original bound's factor was wrong too).
* `interferenceWindow m + 2·hyperL m + maxCostBound + 2` — the cycles per
  progress event: origin-refill wait (≤ one period ≤ `hyperL`), the
  interference window, and the chain instruction's own in-flight drain.
* the trailing `+ …` — slack for the initial partial period and the final
  retire/unwind cycle.

Coarse and manifest-computable — tightened per target (and per domain,
restoring a `d`-dependence through the chain depth *above* `d`) as T6′ in
Phase 3. The formula is owned by `no_hostage`'s (in-progress) assembly
and will be adjusted to the honest constants the mechanized counting
produces. -/
def resumeBound (m : Manifest) (_d : DomainId) : Nat :=
  ((maxDonationBound m + 2) ^ maxChainDepth + 1) *
    (interferenceWindow m + 2 * hyperL m + maxCostBound + 2)

/-- **No-hostage.** Under strict (occupancy-corrected) schedulability,
stall-freedom, and positive budgets, a domain blocked on a gate call
resumes (or its unwind fires) within `resumeBound` cycles, whatever the
callee does: return, fault, halt, loop (donation exhaustion unwinds it),
or call deeper (depth ≤ 4, each level donation-bounded).

All three side conditions are proof-forced (2026-07-03): without
`hsched` the priority hog starves the chain (header refutation 1, and in
its charge-only form, refutation 2); without `hstall` the stall-lock
freezes the core forever (refutation 3); without `hpos` a zero-quota
origin never refunds the chain. Remaining assembly (the per-cycle
ingredients are proved in `Logic/Hostage.lean`), itemized:

1. **Chain structure** (from `Wf.blocked_gate`/`gate_serving`/
   `serving_gate` + `wfa_invariant`): the serving chain above `d` is a
   finite path `origin ⋯ → d → c₁ → ⋯ → c_k`, `k ≤ maxChainDepth`; only
   the head `c_k` is `running`; `payer c_k = origin`; every other
   domain's payer differs from `origin`; and the chain shape is frozen on
   cycles the head is not issued/in flight (`step_touch` + the gate ops'
   `require` guards: a foreign `gate_call` into a chain member is
   `gateBusy`). Needs one new reachability invariant,
   `run = halted → serving = none`, to exclude a half-halted chain.
2. **Measure**: the lex order on the `donated` vector; every chain-head
   issue strictly decreases it (`corePhase_issue_serving` — donation
   charge or forced unwind) and every chain-head retirement of a gate op
   pops/pushes below it (`GateStep`'s `gatecall_touch`/
   `gatereturn_touch` post-state equations); order type
   `(maxDonationBound+2)^maxChainDepth` bounds the event count.
3. **Potential**: `Ψ = 2·massExcept σ origin + inflight + #non-halted`
   decreases ≥ 1 per non-progress cycle (`corePhase_cases` arms: issue
   via `massExcept_sub` + `cost_pos` — foreign because `payer e = origin`
   forces `e` onto the chain by 1; burn/retire via the countdown; halt
   via the halted count — needs halted-monotonicity of `step`, still
   unproved at the exec level; idle-with-funded-origin impossible via
   `Eligible` head + `schedule_isSome_of_eligible`; stall excluded by
   `hstall`), refunded ≤ `2Q_e` per boundary (`refillPhase_budget_cases`)
   and `2·Σ Q·(L/P) ≤ L-1` per hyperperiod (`hsched`,
   `periodP_dvd_hyperL`). Needs the cycle-counter lemma
   `(step m σ).cycle = σ.cycle + 1` (exec never writes `cycle`; prove as
   an `InflightEq`-style combinator sweep).
4. **Origin refill**: `origin.budget = budgetQ > 0` (`hpos`,
   `refillPhase_budget_cases`) within one period (≤ `hyperL`,
   `periodP_le_hyperL`) of any cycle; only chain issues draw it down
   (item 1), so the head stays eligible until the next progress event.
5. **Assembly**: split `[0, resumeBound]` by `stepN_add` into ≤
   `(maxDonationBound+2)^maxChainDepth` windows of
   `interferenceWindow + 2·hyperL + maxCostBound + 2` cycles; items 3+4
   force a progress event in each; item 2 exhausts the measure; the last
   event is `gate_return` retiring at `g` (`unblocked`), a chain unwind
   reaching `a.caller = d` (`haltDom_caller_running`), or donation
   exhaustion at the head (`corePhase_issue_serving`, right arm) — each
   flips `(σ.doms d).run` off `.blocked g`. Adjust `resumeBound`'s
   constants here if the mechanized count differs. -/
theorem no_hostage (m : Manifest) (hwf : m.WF) (hsched : StrictlySchedulable m)
    (hstall : StallFree m) (hpos : ∀ e, 0 < (m.doms e).budgetQ)
    (σ : MachineState) (hreach : (machine m).Reachable σ)
    (d : DomainId) (g : GateId) (hblocked : (σ.doms d).run = .blocked g) :
    ∃ n ≤ resumeBound m d, ((stepN m n σ).doms d).run ≠ .blocked g := by
  sorry

end Machines.Lnp64u.Theorems.T6
