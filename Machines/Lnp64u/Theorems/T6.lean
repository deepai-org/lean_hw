-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Logic.HostageCount
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
back to 6 at every boundary (the boundary at cycle 0 rewrites the boot
budget, a no-op — the wrapping counter has no boot-skip). C therefore never reaches the core, so none of the three
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

## Third refutation repaired: underfunded issue must be chargeable

The original issue path stalled when the scheduled domain's payer had
positive budget below the fetched instruction's cost. A stall cycle spent
nothing and changed nothing, so no budget-counting hypothesis could
exclude infinite replay of the same underfunded pick. The repaired
semantics make serving underfunding a `.budget` fault, using the existing
halt/unwind path to resume the caller; non-serving underfunding burns the
payer's residual budget to zero. Both cases are chargeable progress, so T6
no longer needs a semantic stall-freedom side condition.
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

/-- The per-progress-step interference window (see `resumeBound`): the
number of cycles within which, under `StrictlySchedulable` and positive
budgets, the serving chain above a blocked caller must have
been issued (or unwound) at least once. Derived from the potential
`Ψ = 2·massExcept σ origin + inflight-remaining + #non-halted`: every
non-progress cycle decreases `Ψ` by ≥ 1 (issue: charge equation +
`cost_pos`; burn/retire: countdown; fault-halt: the halted count; idle
with the origin funded: impossible, the chain head is eligible and
`schedule_isSome_of_eligible` fires), while refills refund at most
`gainAt` per cycle — bounded per window through
`StrictlySchedulable` (`gainSum_bound`).

**Constants adjusted to the mechanized count (2026-07-03, as this
docstring anticipated):** the multiple-counting lemma
(`card_multiples`, an interval-endpoints argument) certifies
`n/P + 2` boundaries per window rather than `n/P + 1`, and the origin
funding wait (≤ one hyperperiod) is absorbed into the same window, so
the honest solution of
`n ≤ L + Ψ₀ + (n/L + 1)·(L-1) + 4·budgetMass` with
`Ψ₀ ≤ 2·budgetMass + maxCostBound + numDomains` is
`n = L·(6·budgetMass + maxCostBound + numDomains + 2·L + 2)` — exactly
`Logic/HostageCount.lean`'s `scanBound`, with which this definition
agrees definitionally (`scan_arith` closes the window). Coarse and
manifest-computable. -/
def interferenceWindow (m : Manifest) : Nat :=
  hyperL m * (6 * budgetMass m + maxCostBound + numDomains + 2 * hyperL m + 2)

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

/-- **No-hostage.** Under strict (occupancy-corrected) schedulability
and positive budgets, a domain blocked on a gate call
resumes (or its unwind fires) within `resumeBound` cycles, whatever the
callee does: return, fault, halt, loop (donation exhaustion unwinds it),
or call deeper (depth ≤ 4, each level donation-bounded).

Both side conditions are proof-forced: without
`hsched` the priority hog starves the chain (header refutation 1, and in
its charge-only form, refutation 2); without `hpos` a zero-quota
origin never refunds the chain. **PROVED sorry-free (2026-07-03)** — the
assembly lives in `Logic/HostageChain.lean` (chain structure),
`Logic/HostageMeasure.lean` (radix measure), `Logic/HostageFrame.lean`
(foreign-cycle frames) and `Logic/HostageCount.lean` (`cycle_master`,
`drain`, `scan`, `window`, `resume_of_measure`). The obligations,
itemized:

1. **Chain structure** (from `Wf.blocked_gate`/`gate_serving`/
   `serving_gate` + `wfa_invariant`): the serving chain above `d` is a
   finite path `origin ⋯ → d → c₁ → ⋯ → c_k`, `k ≤ maxChainDepth`; only
   the head `c_k` is `running`; `payer c_k = origin`; every other
   domain's payer differs from `origin`; and the chain shape is frozen on
   cycles the head is not issued/in flight (`step_touch` + the gate ops'
   `require` guards: a foreign `gate_call` into a chain member is
   `gateBusy`). **DONE (2026-07-03):** the one new reachability invariant
   this needed — `run = halted → serving = none`, excluding a half-halted
   chain — is now proved sorry-free as
   `Hostage.halted_serving_none_invariant` (a full ISA combinator sweep:
   `haltDom_hsn`/`CalmOut.hsn` for the halt and calm ops,
   `gatecall_hsn`/`gatereturn_hsn` via `gateCall_end_hsn`/
   `gateReturn_end_hsn` for the gate ops, lifted through
   `retire_hsn`/`corePhase_hsn`/`step_hsn` to every reachable state). The
   remaining part of this item — assembling the frozen-shape path itself —
   is bundled into the measure/potential counting below.
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
   via the halted count — **DONE (2026-07-03)**: halted-monotonicity is
   now proved sorry-free as `Hostage.halted_stays`/`stepN_halted` (a
   `HaltedStays` ISA sweep: calm ops via `CalmOut.haltedStays`, the gate
   ops via `gateCall_end_halted`/`gateReturn_end_halted` — the resumed
   caller is `.blocked`, never `.halted`, by `Wf.gate_serving` — and the
   halts via `haltDom_halted`); idle-with-funded-origin impossible via
   `Eligible` head + `schedule_isSome_of_eligible`; underfunded issue is
   a `.budget` halt), refunded ≤ `2Q_e` per boundary (`refillPhase_budget_cases`)
   and `2·Σ Q·(L/P) ≤ L-1` per hyperperiod (`hsched`,
   `periodP_dvd_hyperL`). The cycle-counter lemma is **DONE
   (2026-07-03)**: `(step m σ).cycle = σ.cycle + 1` is
   `Hostage.step_cycle` (with `stepN_cycle` for windows; since 2026-07-04
   these are `BitVec 32` equations — the counter wraps — and window
   arguments reduce mod `P` through `stepN_cycle_mod`, backed by
   `Manifest.WF.period_dvd`), via the `CycleEq` combinator sweep (exec
   never writes `cycle`), mirroring `InflightEq`.
4. **Origin refill**: `origin.budget = budgetQ > 0` (`hpos`,
   `refillPhase_budget_cases`) within one period (≤ `hyperL`,
   `periodP_le_hyperL`) of any cycle; only chain issues draw it down
   (item 1), so the head stays eligible until the next progress event.
   **DONE (2026-07-03)**: the refill brick is
   `Hostage.refill_within_period` (a boundary at most `periodP` cycles
   ahead restores `budget = budgetQ`, via `stepN_cycle`) and
   `origin_refill_eligible` (`0 < budget` within `hyperL` cycles, at the
   very `refillPhase` state `corePhase` runs in). The "stays eligible"
   half is the chain-frame part of item 1.
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
    (hpos : ∀ e, 0 < (m.doms e).budgetQ)
    (σ : MachineState) (hreach : (machine m).Reachable σ)
    (d : DomainId) (g : GateId) (hblocked : (σ.doms d).run = .blocked g) :
    ∃ n ≤ resumeBound m d, ((stepN m n σ).doms d).run ≠ .blocked g := by
  have hsched' : 2 * ((List.finRange numDomains).map
      (fun e => (m.doms e).budgetQ * (hyperL m / (m.doms e).periodP))).sum < hyperL m :=
    hsched
  have hci : ChainInv m σ := chain_invariant m hwf σ hreach
  obtain ⟨j, hj, hclean⟩ := to_clean m hwf maxCostBound σ hreach
    (fun fl hfl => hci.inflightLe fl hfl)
  have hreachj : (machine m).Reachable (stepN m j σ) := stepN_reachable m σ hreach j
  -- window-arithmetic facts, shared by both branches
  have hWpow : 1 ≤ (maxDonationBound m + 2) ^ maxChainDepth :=
    Nat.pow_pos (by omega)
  have hIW : interferenceWindow m = scanBound m := rfl
  have hwl : windowLen m ≤ interferenceWindow m + 2 * hyperL m + maxCostBound + 2 := by
    unfold windowLen
    rw [hIW]
    omega
  have hnw : maxCostBound ≤ interferenceWindow m + 2 * hyperL m + maxCostBound + 2 := by
    omega
  by_cases hbj : ((stepN m j σ).doms d).run = .blocked g
  · have hwfj : Wf (stepN m j σ) := (wfa_invariant m hwf _ hreachj).1
    have hsnj : HaltedServingNone (stepN m j σ) :=
      halted_serving_none_invariant m hwf _ hreachj
    have hcij : ChainInv m (stepN m j σ) := chain_invariant m hwf _ hreachj
    obtain ⟨l, hh, hcf, hlenb⟩ := chain_exists hwfj hsnj hcij.depthLink hbj
    have hMlt : chainMeasure m (stepN m j σ) d < chainW m ^ maxChainDepth :=
      chainMeasure_lt m hwfj hcij.depthLink hcij.donatedLe hcf
    have hWeq : chainW m = maxDonationBound m + 2 := rfl
    obtain ⟨n, hn, hout⟩ := resume_of_measure m hwf hsched' hpos
      (chainW m ^ maxChainDepth - 1) (stepN m j σ) hreachj hbj hclean (by omega)
    refine ⟨j + n, ?_, ?_⟩
    · -- j + n ≤ resumeBound
      unfold resumeBound
      have hM1 : chainW m ^ maxChainDepth - 1 + 1 = chainW m ^ maxChainDepth := by
        have : 1 ≤ chainW m ^ maxChainDepth := by
          rw [hWeq]
          exact hWpow
        omega
      rw [hM1] at hn
      have hmul : chainW m ^ maxChainDepth * windowLen m ≤
          chainW m ^ maxChainDepth *
            (interferenceWindow m + 2 * hyperL m + maxCostBound + 2) :=
        Nat.mul_le_mul_left _ hwl
      rw [hWeq] at hmul hn
      have hvexp : ((maxDonationBound m + 2) ^ maxChainDepth + 1) *
          (interferenceWindow m + 2 * hyperL m + maxCostBound + 2) =
          (maxDonationBound m + 2) ^ maxChainDepth *
            (interferenceWindow m + 2 * hyperL m + maxCostBound + 2) +
          (interferenceWindow m + 2 * hyperL m + maxCostBound + 2) := by
        ring
      omega
    · rw [stepN_add]
      exact hout
  · refine ⟨j, ?_, hbj⟩
    unfold resumeBound
    have h1 : 1 * (interferenceWindow m + 2 * hyperL m + maxCostBound + 2) ≤
        ((maxDonationBound m + 2) ^ maxChainDepth + 1) *
          (interferenceWindow m + 2 * hyperL m + maxCostBound + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

end Machines.Lnp64u.Theorems.T6
